import Langlands.Representation.LocallyConstant.CompactAction
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Maps.Proper.Basic

/-! # Compactly supported locally constant smooth modules -/

noncomputable section

universe uX uG uR uV

namespace Langlands.CompactAction

open Topology Filter

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : Type uX} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {V : Type uV} [Zero V]

/-- Compact support makes local constancy uniform near the identity, including
at points outside the support. The ambient space need not be compact. -/
theorem functionStabilizer_isOpen_of_hasCompactSupport
    (f : LocallyConstant X V) (hf : HasCompactSupport f) :
    IsOpen (functionStabilizer G f : Set G) := by
  have h : ∀ᶠ g in 𝓝 (1 : G), ∀ x ∈ tsupport f, f (g • x) = f x := by
    apply hf.eventually_forall_of_forall_eventually
    intro x _
    have h₁ := (f.isLocallyConstant.comp_continuous continuous_smul).eventually_eq
      ((1 : G), x)
    have h₂ := (f.isLocallyConstant.comp_continuous continuous_snd).eventually_eq
      ((1 : G), x)
    filter_upwards [h₁, h₂] with p hp hpx
    have hp' : f (p.1 • p.2) = f x := by simpa using hp
    exact hp'.trans hpx.symm
  apply (functionStabilizer G f).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset (inter_mem h (inv_mem_nhds_one G h))
  intro g hg x
  by_cases hx : f x = 0
  · by_cases hxg : f (g • x) = 0
    · exact hxg.trans hx.symm
    · have heq := hg.2 (g • x) (subset_tsupport f hxg)
      simpa using heq.symm
  · exact hg.1 x (subset_tsupport f hx)

/-- The actual spatial stabilizer of a compactly supported locally constant function. -/
def compactSupportOpenStabilizer (f : LocallyConstant X V)
    (hf : HasCompactSupport f) : OpenSubgroup G :=
  ⟨functionStabilizer G f, functionStabilizer_isOpen_of_hasCompactSupport G f hf⟩

@[simp]
theorem mem_compactSupportOpenStabilizer (f : LocallyConstant X V)
    (hf : HasCompactSupport f) (g : G) :
    g ∈ compactSupportOpenStabilizer G f hf ↔ ∀ x, f (g • x) = f x := Iff.rfl

end Langlands.CompactAction

namespace Langlands.CompactAction.LocallyConstantModule.CompactSupport

open CategoryTheory Topology

variable {R : Type uR} [CommRing R] {X : Type uX} [TopologicalSpace X]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- The full submodule defined by actual compact topological support. -/
def submodule (R : Type uR) [CommRing R] (X : Type uX) [TopologicalSpace X]
    (V : Type uV) [AddCommGroup V] [Module R V] : Submodule R (LocallyConstant X V) where
  carrier := {f | HasCompactSupport f}
  zero_mem' := HasCompactSupport.zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun r _ hf => hf.comp_left (smul_zero r)

/-- All compactly supported locally constant functions, with no stabilizer condition. -/
abbrev Functions (R : Type uR) [CommRing R] (X : Type uX) [TopologicalSpace X]
    (V : Type uV) [AddCommGroup V] [Module R V] := ↥(submodule R X V)

@[simp]
theorem mem_submodule (f : LocallyConstant X V) :
    f ∈ submodule R X V ↔ HasCompactSupport f := Iff.rfl

/-- Compact support implies finite image without compactness of the domain
or a topology on the coefficients. -/
theorem range_finite (f : Functions R X V) : (Set.range f.val).Finite := by
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := discreteTopology_bot V
  exact (f.property.isCompact_range f.val.continuous).finite_of_discrete

variable {G : Type uG} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- The original diagonal action preserves actual compact support. -/
theorem diagonal_hasCompactSupport (ρ : Representation R G V) (g : G)
    (f : LocallyConstant X V) (hf : HasCompactSupport f) :
    HasCompactSupport (diagonalRepresentation ρ g f) :=
  (hf.comp_homeomorph (Homeomorph.smul (α := X) g⁻¹)).comp_left (map_zero (ρ g))

/-- Restrict the full diagonal representation to its compact-support submodule. -/
def representation (ρ : Representation R G V) :
    Representation R G (Functions R X V) :=
  (diagonalRepresentation ρ).subrepresentation (submodule R X V)
    (fun g f hf => diagonal_hasCompactSupport ρ g f hf)

@[simp]
theorem representation_apply (ρ : Representation R G V) (g : G)
    (f : Functions R X V) (x : X) :
    (representation ρ g f).val x = ρ g (f.val (g⁻¹ • x)) := rfl

/-- The inclusion retains every compactly supported function and intertwines
with the full diagonal representation. -/
def inclusion (ρ : Representation R G V) :
    (representation (X := X) ρ).IntertwiningMap (diagonalRepresentation (X := X) ρ) where
  toLinearMap := (submodule R X V).subtype
  isIntertwining' _ := rfl

/-- The actual coefficient intertwiner preserves compact support. -/
def coefficientIntertwiner {W : Type*} [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {σ : Representation R G W}
    (a : ρ.IntertwiningMap σ) :
    (representation (X := X) ρ).IntertwiningMap (representation (X := X) σ) where
  toLinearMap :=
    ((LocallyConstant.mapₗ R a.toLinearMap).comp (submodule R X V).subtype).codRestrict
      (submodule R X W) (fun f => f.property.comp_left (map_zero a.toLinearMap))
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    exact Representation.IntertwiningMap.isIntertwining ρ σ a g (f.val (g⁻¹ • x))

@[simp]
theorem coefficientIntertwiner_apply {W : Type*} [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {σ : Representation R G W}
    (a : ρ.IntertwiningMap σ) (f : Functions R X V) (x : X) :
    (coefficientIntertwiner (X := X) a f).val x = a (f.val x) := rfl

/-- Proper equivariant domain maps induce actual compact-support-preserving pullback. -/
def pullbackIntertwiner {Y : Type*} [TopologicalSpace Y] [MulAction G Y]
    [ContinuousConstSMul G Y] (ρ : Representation R G V) (q : C(X, Y))
    (hq : IsProperMap q) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    (representation (X := Y) ρ).IntertwiningMap (representation (X := X) ρ) where
  toLinearMap :=
    ((LocallyConstant.comapₗ R q).comp (submodule R Y V).subtype).codRestrict
      (submodule R X V) (fun f =>
        (hq.isCompact_preimage f.property).of_isClosed_subset
          (isClosed_tsupport _) (tsupport_comp_subset_preimage f.val q.continuous))
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    exact congrArg (ρ g) (congrArg f.val (heq g⁻¹ x).symm)

@[simp]
theorem pullbackIntertwiner_apply {Y : Type*} [TopologicalSpace Y] [MulAction G Y]
    [ContinuousConstSMul G Y] (ρ : Representation R G V) (q : C(X, Y))
    (hq : IsProperMap q) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (f : Functions R Y V) (x : X) :
    (pullbackIntertwiner ρ q hq heq f).val x = f.val (q x) := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G X]

/-- Intersect the constructed spatial stabilizer with the finitely many
coefficient stabilizers. -/
def commonOpenStabilizer (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (f : Functions R X V) : OpenSubgroup G := by
  letI : Finite (Set.range f.val) := (range_finite f).to_subtype
  exact compactSupportOpenStabilizer G f.val f.property ⊓ OpenSubgroup.iInfOfFinite
    (fun a : Set.range f.val =>
      ⟨ρ.stabilizer a.val, (isSmoothVector_iff_isOpen_stabilizer a.val).mp (hρ a.val)⟩)

omit [ContinuousConstSMul G X] in
@[simp]
theorem mem_commonOpenStabilizer (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (f : Functions R X V) (g : G) :
    g ∈ commonOpenStabilizer ρ hρ f ↔
      (∀ x, f.val (g • x) = f.val x) ∧
        ∀ a : Set.range f.val, ρ g a.val = a.val := by
  change (g ∈ functionStabilizer G f.val ∧
    g ∈ (⨅ a : Set.range f.val, ρ.stabilizer a.val)) ↔ _
  simp only [Subgroup.mem_iInf]
  rfl

/-- Smoothness is proved for the whole compact-support module on a possibly
noncompact domain. -/
theorem representation_isSmooth (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    IsSmooth (representation (X := X) ρ) := by
  intro f
  refine ⟨commonOpenStabilizer ρ hρ f, ?_⟩
  intro g
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change ρ (g : G) (f.val ((g : G)⁻¹ • x)) = f.val x
  have hs := ((mem_commonOpenStabilizer ρ hρ f (g : G)⁻¹).mp
    ((commonOpenStabilizer ρ hρ f).inv_mem g.property)).1 x
  rw [hs]
  exact ((mem_commonOpenStabilizer ρ hρ f g).mp g.property).2
    ⟨f.val x, ⟨x, rfl⟩⟩

/-- Bundle every compactly supported locally constant function with the
proved smooth diagonal action. -/
def smoothRepresentation (A : SmoothRep.{uR, uG, uV} R G) :
    SmoothRep.{uR, uG, max uX uV} R G :=
  SmoothRep.of (representation (X := X) A.representation)
    (representation_isSmooth A.representation A.isSmooth)

/-- Actual pointwise postcomposition by a smooth coefficient morphism. -/
def smoothCoefficientMap {A B : SmoothRep.{uR, uG, uV} R G} (a : A ⟶ B) :
    smoothRepresentation (X := X) A ⟶ smoothRepresentation (X := X) B :=
  SmoothRep.ofHom (coefficientIntertwiner (X := X) (SmoothRep.hom a))

@[simp]
theorem smoothCoefficientMap_apply {A B : SmoothRep.{uR, uG, uV} R G} (a : A ⟶ B)
    (f : Functions R X A) (x : X) :
    (SmoothRep.hom (smoothCoefficientMap (X := X) a) f).val x =
      SmoothRep.hom a (f.val x) := rfl

/-- The compact-support diagonal construction is functorial in arbitrary
smooth module coefficients. -/
def coefficientFunctor :
    SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, max uX uV} R G where
  obj := smoothRepresentation (X := X)
  map := smoothCoefficientMap
  map_id _ := by
    ext f
    rfl
  map_comp _ _ := by
    ext f
    rfl

/-- Proper equivariant pullback of the constructed smooth representations. -/
def smoothPullback {Y : Type uX} [TopologicalSpace Y] [MulAction G Y]
    [ContinuousSMul G Y] (A : SmoothRep.{uR, uG, uV} R G) (q : C(X, Y))
    (hq : IsProperMap q) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    smoothRepresentation (X := Y) A ⟶ smoothRepresentation (X := X) A :=
  SmoothRep.ofHom (pullbackIntertwiner A.representation q hq heq)

end Langlands.CompactAction.LocallyConstantModule.CompactSupport
