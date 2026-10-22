import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Compactness.Compact

/-! Smooth induction and compact induction by right translation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The quotient whose points are right cosets `P * g`, with the quotient topology. -/
abbrev LeftQuotient (P : Subgroup G) := Quotient (QuotientGroup.rightRel P)

/-- The projection to `P \ G`. -/
def quotientMap (P : Subgroup G) (g : G) : LeftQuotient P :=
  Quotient.mk _ g

/-- Right multiplication on `P \ G`. -/
def quotientRight (P : Subgroup G) (g : G) : LeftQuotient P → LeftQuotient P :=
  Quotient.map' (fun x => x * g) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_inv_rev, mul_assoc] using h)

private theorem continuous_quotientRight (P : Subgroup G) (g : G) :
    Continuous (quotientRight P g) :=
  (continuous_id.mul_const g).quotient_map' _

/-- Mathlib's actual module of covariant functions, without a smoothness restriction. -/
abbrev EquivariantFunctions (P : Subgroup G) (σ : Representation R P V) :=
  Representation.coindV P.subtype σ

/-- The existing right-translation action on covariant functions. -/
abbrev equivariantAction (P : Subgroup G) (σ : Representation R P V) :=
  Representation.coind P.subtype σ

/-- Covariant functions with one open right stabilizer for each entire function. -/
abbrev SmoothFunctions (P : Subgroup G) (σ : Representation R P V) : Type (max uG uV) :=
  smoothVectors (equivariantAction P σ)

instance smoothFunctionsAddCommGroup (P : Subgroup G) (σ : Representation R P V) :
    AddCommGroup (SmoothFunctions P σ) :=
  Submodule.addCommGroup _

/-- The smooth induced representation, obtained by restricting right translation. -/
def smoothInduced (P : Subgroup G) (σ : Representation R P V) :
    Representation R G (SmoothFunctions P σ) :=
  smoothPart (equivariantAction P σ)

/-- Evaluation of a smooth induced function. -/
def eval (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) (g : G) : V :=
  f.1.1 g

/-- Build a smooth induced function from covariance and a single uniform open stabilizer. -/
def smoothFunctionOf (P : Subgroup G) (σ : Representation R P V) (f : G → V)
    (hcov : ∀ (p : P) (x : G), f ((p : G) * x) = σ p (f x))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (x : G), f (x * (k : G)) = f x) :
    SmoothFunctions P σ :=
  ⟨⟨f, hcov⟩, K, by
    intro k
    apply Subtype.ext
    exact funext (hK k)⟩

/-- The constructed smooth induction is smooth, for direct use by other bundled interfaces. -/
theorem smoothInduced_smooth (P : Subgroup G) (σ : Representation R P V) :
    IsSmooth (R := R) (G := G) (V := SmoothFunctions P σ) (smoothInduced P σ) := by
  intro f
  obtain ⟨K, hK⟩ := f.property
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

/-- Postcomposition by an equivariant linear map, restricted to smooth functions. -/
def smoothInducedMap (P : Subgroup G) {σ : Representation R P V}
    {τ : Representation R P W} (T : σ.IntertwiningMap τ) :
    (smoothInduced P σ).IntertwiningMap (smoothInduced P τ) :=
  smoothMap (Representation.coindMap P.subtype T)

/-- Compatibility name for the canonical full subcategory of smooth representations. -/
abbrev SmoothRep (R : Type uR) (G : Type uG)
    [CommRing R] [Group G] [TopologicalSpace G] :=
  Langlands.SmoothRep.{uR, uG, uV} R G

set_option maxHeartbeats 800000 in
/-- Smooth induction with its smoothness certificate and intrinsic functor laws. -/
def smoothInductionFunctor (P : Subgroup G) :
    Rep.{uV} R P ⥤ SmoothRep.{uR, uG, max uG uV} R G where
  obj A := ⟨Rep.of (smoothInduced P A.ρ), smoothInduced_smooth P A.ρ⟩
  map f := CategoryTheory.ObjectProperty.homMk (Rep.ofHom (smoothInducedMap P f.hom))
  map_id _ := by ext f x; rfl
  map_comp _ _ := by ext f x; rfl

/-- The nonzero support projected to `P \ G`. -/
def quotientSupport (P : Subgroup G) (f : G → V) : Set (LeftQuotient P) :=
  quotientMap P '' Function.support f

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem preimage_quotientSupport (P : Subgroup G) (σ : Representation R P V)
    (f : EquivariantFunctions P σ) :
    quotientMap P ⁻¹' quotientSupport P f.1 = Function.support f.1 := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    intro hx
    have hp : y * x⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hxy.symm)
    have hf := f.property ⟨y * x⁻¹, hp⟩ x
    have hzero : f.1 y = 0 := by
      simpa [mul_assoc, hx] using hf
    exact hy hzero
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem eval_locallyConstant (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) : IsLocallyConstant (eval P σ f) := by
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (K : Set G),
    isOpenMap_mul_left x _ K.isOpen, ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg (fun F : EquivariantFunctions P σ => F.1 x) (hK ⟨k, hk⟩)

private theorem quotientSupport_closed (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) : IsClosed (quotientSupport P (eval P σ f)) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isCoinducing.isClosed_preimage.mp
  change IsClosed (quotientMap P ⁻¹' quotientSupport P f.1.1)
  rw [preimage_quotientSupport]
  exact (eval_locallyConstant P σ f).isOpen_fiber 0 |>.isClosed_compl

/-- Smooth functions whose actual projected nonzero support is compact. -/
def compactFunctions (P : Subgroup G) (σ : Representation R P V) :
    Submodule R (SmoothFunctions P σ) where
  carrier := {f | IsCompact (quotientSupport P (eval P σ f))}
  zero_mem' := by
    change IsCompact (quotientMap P '' Function.support (0 : G → V))
    simp
  add_mem' := by
    intro f h hf hh
    apply (hf.union hh).of_isClosed_subset (quotientSupport_closed P σ (f + h))
    rintro _ ⟨x, hx, rfl⟩
    have hzero : eval P σ f x ≠ 0 ∨ eval P σ h x ≠ 0 := by
      by_contra hn
      simp only [not_or, not_not] at hn
      exact hx (by change eval P σ f x + eval P σ h x = 0; rw [hn.1, hn.2, add_zero])
    rcases hzero with hzero | hzero
    · exact Or.inl ⟨x, hzero, rfl⟩
    · exact Or.inr ⟨x, hzero, rfl⟩
  smul_mem' := by
    intro a f hf
    apply hf.of_isClosed_subset (quotientSupport_closed P σ (a • f))
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    intro hzero
    exact hx (by change a • eval P σ f x = 0; rw [hzero, smul_zero])

/-- Compact induction's module, still a space of actual covariant functions. -/
abbrev CompactFunctions (P : Subgroup G) (σ : Representation R P V) : Type (max uG uV) :=
  compactFunctions P σ

instance compactFunctionsAddCommGroup (P : Subgroup G) (σ : Representation R P V) :
    AddCommGroup (CompactFunctions P σ) :=
  Submodule.addCommGroup _

/-- Compact support modulo `P` is stable under right translation. -/
def compactSubrepresentation (P : Subgroup G) (σ : Representation R P V) :
    Subrepresentation (smoothInduced P σ) where
  toSubmodule := compactFunctions P σ
  apply_mem_toSubmodule := by
    intro g f hf
    apply (hf.image (continuous_quotientRight P g⁻¹)).of_isClosed_subset
      (quotientSupport_closed P σ (smoothInduced P σ g f))
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨quotientMap P (x * g), ⟨x * g, hx, rfl⟩, ?_⟩
    change quotientMap P (x * g * g⁻¹) = quotientMap P x
    rw [mul_inv_cancel_right]

/-- Compact induction, with right translation restricted to compact support modulo `P`. -/
def compactInduced (P : Subgroup G) (σ : Representation R P V) :
    Representation R G (CompactFunctions P σ) :=
  (compactSubrepresentation P σ).toRepresentation

/-- Compact induction is smooth with the inherited uniform open stabilizers. -/
theorem compactInduced_smooth (P : Subgroup G) (σ : Representation R P V) :
    IsSmooth (R := R) (G := G) (V := CompactFunctions P σ) (compactInduced P σ) := by
  intro f
  obtain ⟨K, hK⟩ := smoothInduced_smooth P σ f.1
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

private theorem compact_map_mem (P : Subgroup G) {σ : Representation R P V}
    {τ : Representation R P W} (T : σ.IntertwiningMap τ)
    (f : SmoothFunctions P σ) (hf : f ∈ compactFunctions P σ) :
    smoothInducedMap P T f ∈ compactFunctions P τ := by
  apply hf.of_isClosed_subset (quotientSupport_closed P τ (smoothInducedMap P T f))
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  intro hzero
  exact hx (by change T (eval P σ f x) = 0; rw [hzero, map_zero])

/-- Postcomposition on compact induction, with support preservation proved intrinsically. -/
def compactInducedMap (P : Subgroup G) {σ : Representation R P V}
    {τ : Representation R P W} (T : σ.IntertwiningMap τ) :
    (compactInduced P σ).IntertwiningMap (compactInduced P τ) where
  toLinearMap := (smoothInducedMap P T).toLinearMap.restrict (compact_map_mem P T)
  isIntertwining' g := by
    ext f x
    rfl

/-- Compact induction as a functor returning actual smooth representations. -/
def compactInductionFunctor (P : Subgroup G) :
    Rep.{uV} R P ⥤ SmoothRep.{uR, uG, max uG uV} R G where
  obj A := ⟨Rep.of (compactInduced P A.ρ), compactInduced_smooth P A.ρ⟩
  map f := CategoryTheory.ObjectProperty.homMk (Rep.ofHom (compactInducedMap P f.hom))
  map_id _ := by ext f x; rfl
  map_comp _ _ := by ext f x; rfl

/-- Build a compact induced function from its covariance, uniform stabilizer and quotient support. -/
def compactFunctionOf (P : Subgroup G) (σ : Representation R P V) (f : G → V)
    (hcov : ∀ (p : P) (x : G), f ((p : G) * x) = σ p (f x))
    (K : OpenSubgroup G) (hK : ∀ (k : K) (x : G), f (x * (k : G)) = f x)
    (hc : IsCompact (quotientSupport P f)) : CompactFunctions P σ :=
  ⟨smoothFunctionOf P σ f hcov K hK, hc⟩

/-- The canonical equivariant inclusion of compact induction into smooth induction. -/
def compactInclusion (P : Subgroup G) (σ : Representation R P V) :
    (compactInduced P σ).IntertwiningMap (smoothInduced P σ) where
  toLinearMap := (compactFunctions P σ).subtype
  isIntertwining' _ := by ext f x; rfl

/-- A unit-valued character with open kernel, requiring no topology on the coefficient ring. -/
structure SmoothCharacter (R : Type uR) (G : Type uG)
    [CommRing R] [Group G] [TopologicalSpace G] where
  /-- The actual scalar character. -/
  toMonoidHom : G →* Rˣ
  /-- Smoothness of the scalar character. -/
  isOpen_ker : IsOpen (toMonoidHom.ker : Set G)

/-- The genuine smooth scalar representation underlying a smooth character. -/
def SmoothCharacter.toSmoothRep (χ : SmoothCharacter R G) : SmoothRep.{uR, uG, uR} R G :=
  ⟨Rep.of (Langlands.characterRepresentation χ.toMonoidHom), by
    intro a
    refine ⟨⟨χ.toMonoidHom.ker, χ.isOpen_ker⟩, ?_⟩
    intro k
    change (χ.toMonoidHom (k : G) : R) • a = a
    have hk : χ.toMonoidHom (k : G) = 1 := k.property
    simp [hk]⟩

/-- Scalar twisting as an actual functor, using the accepted twist and intertwiner constructions. -/
def SmoothCharacter.twistFunctor (χ : SmoothCharacter R G) :
    Rep.{uV} R G ⥤ Rep.{uV} R G where
  obj A := Rep.of (Langlands.twist χ.toMonoidHom A.ρ)
  map f := Rep.ofHom (Langlands.twistIntertwining χ.toMonoidHom f.hom)
  map_id _ := by ext v; rfl
  map_comp _ _ := by ext v; rfl

/-- Normalized smooth induction; the caller supplies the actual smooth normalizing character. -/
def normalizedSmoothInduced (P : Subgroup G) (χ : SmoothCharacter R P)
    (σ : Representation R P V) :=
  smoothInduced P (Langlands.twist χ.toMonoidHom σ)

/-- Normalized compact induction with the same character and quotient-support convention. -/
def normalizedCompactInduced (P : Subgroup G) (χ : SmoothCharacter R P)
    (σ : Representation R P V) :=
  compactInduced P (Langlands.twist χ.toMonoidHom σ)

/-- Normalized smooth induction, with postcomposition maps and intrinsic functor laws. -/
def normalizedSmoothInductionFunctor (P : Subgroup G) (χ : SmoothCharacter R P) :
    Rep.{uV} R P ⥤ SmoothRep.{uR, uG, max uG uV} R G :=
  χ.twistFunctor ⋙ smoothInductionFunctor P

/-- Normalized compact induction, with postcomposition maps and intrinsic functor laws. -/
def normalizedCompactInductionFunctor (P : Subgroup G) (χ : SmoothCharacter R P) :
    Rep.{uV} R P ⥤ SmoothRep.{uR, uG, max uG uV} R G :=
  χ.twistFunctor ⋙ compactInductionFunctor P

end Langlands.Induction
