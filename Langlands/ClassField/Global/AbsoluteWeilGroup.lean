import Langlands.ClassField.Global.RelativeWeilMap
import Mathlib.FieldTheory.Galois.Profinite

/-! # The absolute global Weil group as a projective limit along Weil maps

Artin–Tate, Chapter XV, printed pp.177–181: a transitive collection of Weil maps
between the relative Weil groups of the finite Galois layers of `Ω / F`, and the
subgroup of coherent families in their product.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology CategoryTheory Opposite
open scoped NumberField

universe u

attribute [local instance] relativeIdeleClassAction

namespace FiniteGaloisLayer

variable {F : Type u} [Field F] [NumberField F] {Ω : Type u} [Field Ω] [Algebra F Ω]

/-- A finite Galois layer of `Ω / F` is a number field. -/
instance numberField (K : FiniteGaloisIntermediateField F Ω) : NumberField K :=
  NumberField.of_module_finite F K

/-- The discrete topology on the Galois group of a finite Galois layer, as used by the
relative Weil groups (`relativeGaloisTopology`). It is installed only for finite layers, so
that `Ω ≃ₐ[F] Ω` keeps Mathlib's Krull topology. -/
@[instance_reducible]
def galoisTopology (K : FiniteGaloisIntermediateField F Ω) : TopologicalSpace (K ≃ₐ[F] K) :=
  relativeGaloisTopology F K

attribute [local instance] galoisTopology

/-- The inclusion of a smaller finite Galois layer into a larger one, as an algebra;
this is the algebra structure used by Mathlib's restriction maps on Galois groups. -/
abbrev algebra {K L : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L) : Algebra K L :=
  RingHom.toAlgebra (Subsemiring.inclusion hKL)

omit [NumberField F] in
theorem isScalarTower {K L : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L) :
    letI := algebra hKL
    IsScalarTower F K L :=
  letI := algebra hKL
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

end FiniteGaloisLayer

open FiniteGaloisLayer

attribute [local instance] FiniteGaloisLayer.galoisTopology

/-- A transitive collection of Weil maps (Artin–Tate XV, printed pp.177–178) between the
relative Weil groups `W_{K/F} = RelativeWeilGroup c F K` of all finite Galois layers `K`
of `Ω / F`. -/
structure WeilMapSystem (c : FundamentalClass.ClassFamily.{u}) (F : Type u) [Field F]
    [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
    (h : FundamentalClass.Restriction c) where
  /-- The Weil map `W_{L/F} → W_{K/F}` for `K ≤ L`. -/
  map : ∀ {K L : FiniteGaloisIntermediateField F Ω}, K ≤ L →
    (RelativeWeilGroup c F L →ₜ* RelativeWeilGroup c F K)
  isWeilMap : ∀ {K L : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L),
    letI := FiniteGaloisLayer.algebra hKL
    haveI := FiniteGaloisLayer.isScalarTower hKL
    RelativeWeilGroup.IsWeilMap c F K L h (map hKL)
  map_map : ∀ {K L M : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L) (hLM : L ≤ M)
    (t : RelativeWeilGroup c F M), map hKL (map hLM t) = map (hKL.trans hLM) t

namespace WeilMapSystem

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h)

theorem surjective_map {K L : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L) :
    Function.Surjective (S.map hKL) := by
  let := FiniteGaloisLayer.algebra hKL
  have := FiniteGaloisLayer.isScalarTower hKL
  exact (S.isWeilMap hKL).surjective

/-- The Weil map of a layer to itself is the identity. -/
theorem map_self (K : FiniteGaloisIntermediateField F Ω) (t : RelativeWeilGroup c F K) :
    S.map le_rfl t = t := by
  obtain ⟨s, rfl⟩ := S.surjective_map (le_refl K) t
  exact S.map_map le_rfl le_rfl s

/-- The projection to `Gal(K/F)` of the image of a Weil map is the restriction. -/
theorem projection_map {K L : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L)
    (t : RelativeWeilGroup c F L) :
    letI := FiniteGaloisLayer.algebra hKL
    haveI := FiniteGaloisLayer.isScalarTower hKL
    RelativeWeilGroup.projection c F K (S.map hKL t) =
      AlgEquiv.restrictNormalHom K (RelativeWeilGroup.projection c F L t) := by
  let := FiniteGaloisLayer.algebra hKL
  have := FiniteGaloisLayer.isScalarTower hKL
  exact (S.isWeilMap hKL).projection_map t

/-- The coherent families in the product of the relative Weil groups. -/
def weilSubgroup :
    Subgroup (∀ K : FiniteGaloisIntermediateField F Ω, RelativeWeilGroup c F K) where
  carrier := {x | ∀ ⦃K L : FiniteGaloisIntermediateField F Ω⦄ (hKL : K ≤ L),
    S.map hKL (x L) = x K}
  mul_mem' {x y} hx hy K L hKL := by
    change S.map hKL (x L * y L) = x K * y K
    rw [map_mul, hx hKL, hy hKL]
  one_mem' K L hKL := map_one (S.map hKL)
  inv_mem' {x} hx K L hKL := by
    change S.map hKL (x L)⁻¹ = (x K)⁻¹
    rw [map_inv, hx hKL]

/-- The global Weil group of the system: Artin–Tate's projective limit of the relative
Weil groups, with the topology induced by the product topology. -/
abbrev WeilGroup : Type u := S.weilSubgroup

/-- The topology of the global Weil group, induced by the product topology. It is declared
explicitly so that it is available without the local Galois-group topology instance. -/
instance instTopologicalSpace : TopologicalSpace S.WeilGroup :=
  inferInstanceAs (TopologicalSpace S.weilSubgroup)

instance isTopologicalGroup : IsTopologicalGroup S.WeilGroup :=
  inferInstanceAs (IsTopologicalGroup S.weilSubgroup)

theorem mem_weilSubgroup_iff
    (x : ∀ K : FiniteGaloisIntermediateField F Ω, RelativeWeilGroup c F K) :
    x ∈ S.weilSubgroup ↔
      ∀ ⦃K L : FiniteGaloisIntermediateField F Ω⦄ (hKL : K ≤ L), S.map hKL (x L) = x K :=
  Iff.rfl

/-- The projection of the global Weil group to the relative Weil group `W_{K/F}`. -/
def toLevel (K : FiniteGaloisIntermediateField F Ω) :
    S.WeilGroup →ₜ* RelativeWeilGroup c F K where
  toMonoidHom :=
    (Pi.evalMonoidHom (fun K : FiniteGaloisIntermediateField F Ω => RelativeWeilGroup c F K)
      K).comp S.weilSubgroup.subtype
  continuous_toFun := (continuous_apply K).comp continuous_subtype_val

@[simp]
theorem toLevel_apply (K : FiniteGaloisIntermediateField F Ω) (x : S.WeilGroup) :
    S.toLevel K x = (x : ∀ K : FiniteGaloisIntermediateField F Ω, RelativeWeilGroup c F K) K :=
  rfl

theorem map_toLevel {K L : FiniteGaloisIntermediateField F Ω} (hKL : K ≤ L) (x : S.WeilGroup) :
    S.map hKL (S.toLevel L x) = S.toLevel K x :=
  x.2 hKL

/-- Elements of the global Weil group are determined by their projections to all levels. -/
@[ext]
theorem ext {x y : S.WeilGroup} (hxy : ∀ K, S.toLevel K x = S.toLevel K y) : x = y :=
  Subtype.ext (funext hxy)

section Lift

variable {G : Type*} [Group G] [TopologicalSpace G]
  (f : ∀ K : FiniteGaloisIntermediateField F Ω, G →ₜ* RelativeWeilGroup c F K)
  (hf : ∀ ⦃K L : FiniteGaloisIntermediateField F Ω⦄ (hKL : K ≤ L) (g : G),
    S.map hKL (f L g) = f K g)

/-- The universal property of the projective limit: a compatible family of continuous
homomorphisms to all relative Weil groups factors through the global Weil group. -/
def lift : G →ₜ* S.WeilGroup where
  toFun g := ⟨fun K => f K g, fun _ _ hKL => hf hKL g⟩
  map_one' := Subtype.ext (funext fun K => map_one (f K))
  map_mul' g g' := Subtype.ext (funext fun K => map_mul (f K) g g')
  continuous_toFun :=
    Continuous.subtype_mk (continuous_pi fun K => (f K).continuous) _

@[simp]
theorem toLevel_lift (K : FiniteGaloisIntermediateField F Ω) (g : G) :
    S.toLevel K (S.lift f hf g) = f K g :=
  rfl

theorem lift_unique (φ : G →ₜ* S.WeilGroup) (hφ : ∀ K g, S.toLevel K (φ g) = f K g) :
    φ = S.lift f hf :=
  ContinuousMonoidHom.ext fun g => S.ext fun K => hφ K g

end Lift

section Galois

/-- The family of projections `W_F → W_{K/F} → Gal(K/F)`, as an element of Mathlib's
projective limit of the finite Galois groups of `Ω / F`. -/
def toGaloisLimit :
    S.WeilGroup →* ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor F Ω) where
  toFun x :=
    { val := fun L => RelativeWeilGroup.projection c F L.unop (S.toLevel L.unop x)
      property := fun {L₁ L₂} π => by
        have hle : L₂.unop ≤ L₁.unop := leOfHom π.unop
        let := FiniteGaloisLayer.algebra hle
        have := FiniteGaloisLayer.isScalarTower hle
        have hx := S.map_toLevel hle x
        change AlgEquiv.restrictNormalHom L₂.unop
            (RelativeWeilGroup.projection c F L₁.unop (S.toLevel L₁.unop x)) =
          RelativeWeilGroup.projection c F L₂.unop (S.toLevel L₂.unop x)
        rw [← hx]
        exact (S.projection_map hle _).symm }
  map_one' := by
    apply Subtype.ext
    funext L
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    funext L
    exact map_mul (RelativeWeilGroup.projection c F L.unop) _ _

theorem continuous_toGaloisLimit : Continuous S.toGaloisLimit := by
  apply continuous_induced_rng.mpr
  refine continuous_pi fun L => ?_
  have hc : Continuous fun x : S.WeilGroup =>
      RelativeWeilGroup.projection c F L.unop (S.toLevel L.unop x) :=
    (ClassExtension.continuous_projection (c F L.unop)).comp (S.toLevel L.unop).continuous
  exact hc

variable [IsGalois F Ω]

/-- The continuous homomorphism `g : W_F → Gal(Ω/F)` of Artin–Tate XV, printed p.180,
characterized by `g(u)|_K = g_K(u_K)` for every finite Galois layer `K`. -/
def toGalois : S.WeilGroup →ₜ* (Ω ≃ₐ[F] Ω) where
  toMonoidHom :=
    (InfiniteGalois.mulEquivToLimit F Ω).symm.toMonoidHom.comp S.toGaloisLimit
  continuous_toFun :=
    (InfiniteGalois.continuousMulEquivToLimit F Ω).symm.continuous.comp
      S.continuous_toGaloisLimit

theorem restrictNormalHom_toGalois (K : FiniteGaloisIntermediateField F Ω) (x : S.WeilGroup) :
    AlgEquiv.restrictNormalHom K (S.toGalois x) =
      RelativeWeilGroup.projection c F K (S.toLevel K x) := by
  have h := congrArg (fun g => g.val (op K))
    ((InfiniteGalois.mulEquivToLimit F Ω).apply_symm_apply (S.toGaloisLimit x))
  exact h

/-- Artin–Tate's subgroup `U_E = g⁻¹(G_E)` of the global Weil group (XV, printed p.181), for
an intermediate field `E` of `Ω / F`, `G_E` being the subgroup of `Gal(Ω/F)` fixing `E`. -/
def fieldSubgroup (E : IntermediateField F Ω) : Subgroup S.WeilGroup :=
  E.fixingSubgroup.comap S.toGalois.toMonoidHom

theorem mem_fieldSubgroup_iff (E : IntermediateField F Ω) (x : S.WeilGroup) :
    x ∈ S.fieldSubgroup E ↔ S.toGalois x ∈ E.fixingSubgroup :=
  Iff.rfl

theorem isOpen_fieldSubgroup (E : IntermediateField F Ω) [FiniteDimensional F E] :
    IsOpen (S.fieldSubgroup E : Set S.WeilGroup) :=
  E.fixingSubgroup_isOpen.preimage S.toGalois.continuous

theorem isClosed_fieldSubgroup (E : IntermediateField F Ω) [FiniteDimensional F E] :
    IsClosed (S.fieldSubgroup E : Set S.WeilGroup) :=
  OpenSubgroup.isClosed ⟨S.fieldSubgroup E, S.isOpen_fieldSubgroup E⟩

/-- The first statement of the lemma of Artin–Tate XV, printed p.181: for `E ⊆ K` with `K` a
finite Galois layer, `u ∈ U_E` exactly when the image of `u` in `Gal(K/F)` fixes `E`. -/
theorem mem_fieldSubgroup_iff_projection_toLevel (E : IntermediateField F Ω)
    (K : FiniteGaloisIntermediateField F Ω) (hEK : E ≤ K.toIntermediateField)
    (x : S.WeilGroup) :
    x ∈ S.fieldSubgroup E ↔ ∀ y : E,
      RelativeWeilGroup.projection c F K (S.toLevel K x) ⟨y, hEK y.2⟩ = ⟨y, hEK y.2⟩ := by
  rw [mem_fieldSubgroup_iff, ← S.restrictNormalHom_toGalois K]
  have hval : ∀ z : K, ((AlgEquiv.restrictNormalHom K (S.toGalois x) z : K) : Ω) =
      S.toGalois x (z : Ω) :=
    fun z => AlgEquiv.restrictNormal_commutes (S.toGalois x) K z
  simp only [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hfix y
    exact Subtype.ext ((hval _).trans (hfix y y.2))
  · intro hfix y hy
    exact (hval ⟨y, hEK hy⟩).symm.trans (congrArg Subtype.val (hfix ⟨y, hy⟩))

/-- For a finite Galois layer `K`, `U_K` is the kernel of `W_F → W_{K/F} → Gal(K/F)`. -/
theorem mem_fieldSubgroup_layer_iff (K : FiniteGaloisIntermediateField F Ω)
    (x : S.WeilGroup) :
    x ∈ S.fieldSubgroup K.toIntermediateField ↔
      RelativeWeilGroup.projection c F K (S.toLevel K x) = 1 := by
  rw [mem_fieldSubgroup_iff, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker,
    ← S.restrictNormalHom_toGalois K]

theorem fieldSubgroup_layer_eq_ker (K : FiniteGaloisIntermediateField F Ω) :
    S.fieldSubgroup K.toIntermediateField =
      ((RelativeWeilGroup.projection c F K).comp (S.toLevel K).toMonoidHom).ker := by
  ext x
  exact S.mem_fieldSubgroup_layer_iff K x

instance fieldSubgroup_layer_normal (K : FiniteGaloisIntermediateField F Ω) :
    (S.fieldSubgroup K.toIntermediateField).Normal := by
  rw [fieldSubgroup_layer_eq_ker]
  exact MonoidHom.normal_ker _

end Galois

end WeilMapSystem

end Langlands.ClassField.Global
