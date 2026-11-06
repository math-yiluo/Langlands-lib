import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.Geometry.Building.IntegerValuationBuildingData

/-! # Constructing apartment data when the actual relative-root set is empty -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

namespace RootFunctionFamily

/-- The normalized empty family, extended by `∞` to every character and point. -/
def constantTop : RootFunctionFamily S G :=
  ⟨fun _ _ => ⊤⟩

@[simp] theorem constantTop_apply (a : characterLattice S) (g : rationalPoints G) :
    (constantTop : RootFunctionFamily S G) a g = ⊤ :=
  rfl

@[simp] theorem vadd_constantTop (v : V S) :
    v +ᵥ (constantTop : RootFunctionFamily S G) = constantTop := by
  ext a g
  simp only [vadd_apply, constantTop_apply, WithTop.top_add]

@[simp] theorem smul_constantTop {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    (n : normalizerPoints i) :
    n • (constantTop : RootFunctionFamily S G) = constantTop := by
  ext a g
  rfl

end RootFunctionFamily

variable [IsAffineHom G.X.hom]

section RootDatum

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- With no actual relative roots, the normalized empty family satisfies V 0–V 5. -/
theorem isRootDatumValuation_constantTop_of_relativeRoots_eq_empty
    (hΦ : relativeRoots i = ∅) :
    IsRootDatumValuation i (RootFunctionFamily.constantTop : RootFunctionFamily S G) := by
  have hnot : ∀ a, a ∉ relativeRoots i := fun a => hΦ ▸ Set.notMem_empty a
  exact {
    eq_top_of_not_mem_roots := fun _ _ _ => rfl
    eq_top_of_not_mem := fun a ha => (hnot a ha).elim
    three_le_encard := fun a ha => (hnot a ha).elim
    one_mem := fun a ha => (hnot a ha).elim
    mul_mem := fun a ha => (hnot a ha).elim
    inv_mem := fun a ha => (hnot a ha).elim
    eq_top_iff := fun a ha => (hnot a ha).elim
    reflection := fun a ha => (hnot a ha).elim
    commutator := fun a ha => (hnot a ha).elim
    double := fun a ha => (hnot a ha).elim
    opposite := fun a ha => (hnot a ha).elim }

/-- The off-root normalization determines the entire family when there are no roots. -/
theorem IsRootDatumValuation.eq_constantTop_of_relativeRoots_eq_empty
    {φ : RootFunctionFamily S G} (hφ : IsRootDatumValuation i φ)
    (hΦ : relativeRoots i = ∅) : φ = RootFunctionFamily.constantTop := by
  ext a g
  exact hφ.eq_top_of_not_mem_roots a (hΦ ▸ Set.notMem_empty a) g

end RootDatum

/-- Split-torus V 6 has no root-indexed conditions when the relative-root set is empty. -/
theorem isSplitTorusCompatible_of_relativeRoots_eq_empty {i : S.toGrp ⟶ G}
    (hΦ : relativeRoots i = ∅)
    (ω : kˣ → ℝ) (φ : RootFunctionFamily S G) : IsSplitTorusCompatible i ω φ := by
  intro a ha
  exact (hΦ ▸ Set.notMem_empty a) ha |>.elim

namespace KPApartmentData

/-- Construct the normalizer-stable singleton equipollence class of the normalized
empty valuation, for any supplied ground-field order function. -/
def ofRelativeRootsEqEmpty (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ω : kˣ → ℝ) (hΦ : relativeRoots i = ∅) : KPApartmentData i ω where
  carrier := {RootFunctionFamily.constantTop}
  exists_eq_orbit := by
    refine ⟨RootFunctionFamily.constantTop,
      isRootDatumValuation_constantTop_of_relativeRoots_eq_empty hΦ,
      isSplitTorusCompatible_of_relativeRoots_eq_empty hΦ ω _, ?_⟩
    ext φ
    constructor
    · intro hφ
      have heq : φ = RootFunctionFamily.constantTop := hφ
      exact ⟨0, (zero_vadd _ _).trans heq.symm⟩
    · rintro ⟨v, rfl⟩
      exact RootFunctionFamily.vadd_constantTop v
  smul_mem := by
    intro n φ hφ
    have heq : φ = RootFunctionFamily.constantTop := hφ
    change n • φ = RootFunctionFamily.constantTop
    rw [heq, RootFunctionFamily.smul_constantTop]

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

@[simp] theorem ofRelativeRootsEqEmpty_carrier (ω : kˣ → ℝ)
    (hΦ : relativeRoots i = ∅) :
    (ofRelativeRootsEqEmpty i ω hΦ).carrier = {RootFunctionFamily.constantTop} :=
  rfl

/-- Every valid apartment class for the same empty actual root set is this singleton. -/
theorem carrier_eq_singleton_of_relativeRoots_eq_empty {ω : kˣ → ℝ}
    (D : KPApartmentData i ω) (hΦ : relativeRoots i = ∅) :
    D.carrier = {RootFunctionFamily.constantTop} := by
  obtain ⟨φ, hv, _, hc⟩ := D.exists_eq_orbit
  have heq := hv.eq_constantTop_of_relativeRoots_eq_empty hΦ
  rw [hc, heq]
  ext ψ
  constructor
  · rintro ⟨v, rfl⟩
    exact RootFunctionFamily.vadd_constantTop v
  · intro hψ
    have heqψ : ψ = RootFunctionFamily.constantTop := hψ
    exact ⟨0, (zero_vadd _ _).trans heqψ.symm⟩

end KPApartmentData

namespace IntegerValuation

/-- Full centralizer V 6 for an empty actual relative-root set. -/
theorem isOmegaCompatible_of_relativeRoots_eq_empty
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (D : KPApartmentData i (order v)) (C : CentralizerDatum i)
    (hΦ : relativeRoots i = ∅) : IsOmegaCompatible v D C := by
  intro φ hφ a ha
  exact (hΦ ▸ Set.notMem_empty a) ha |>.elim

end IntegerValuation

namespace IntegerValuationBuildingData

/-- Construct actual integer-valued building data at a prescribed maximal split torus
with no relative roots and a supplied actual centralizer datum. -/
def ofRelativeRootsEqEmpty (v : Valuation k (WithZero (Multiplicative ℤ)))
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hΦ : relativeRoots i = ∅) (C : CentralizerDatum i) :
    IntegerValuationBuildingData v G := by
  letI := mono_of_isMaximalSplitTorus hi
  exact {
    isConnectedReductive := hG
    S := S
    i := i
    isMaximalSplitTorus := hi
    apartment := KPApartmentData.ofRelativeRootsEqEmpty i (IntegerValuation.order v) hΦ
    centralizer := C
    isOmegaCompatible := IntegerValuation.isOmegaCompatible_of_relativeRoots_eq_empty v _ C hΦ }

end IntegerValuationBuildingData

end Field

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace KPApartmentData

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- Full centralizer V 6 has no conditions when the actual relative-root set is empty. -/
theorem isOmegaCompatible_of_relativeRoots_eq_empty
    (D : KPApartmentData i (localFieldOrder F)) (C : CentralizerDatum i)
    (hΦ : relativeRoots i = ∅) : D.IsOmegaCompatible C := by
  intro φ hφ a ha
  exact (hΦ ▸ Set.notMem_empty a) ha |>.elim

/-- With an empty actual relative-root set, any apartment class satisfies the full
published single-apartment predicate for every supplied actual centralizer datum. -/
theorem satisfiesApartmentAxioms_of_relativeRoots_eq_empty
    (D : KPApartmentData i (localFieldOrder F)) (C : CentralizerDatum i)
    (hΦ : relativeRoots i = ∅) : D.SatisfiesApartmentAxioms C :=
  (satisfiesApartmentAxioms_iff_of_relativeRoots_eq_empty hΦ).2
    (D.isOmegaCompatible_of_relativeRoots_eq_empty C hΦ)

end KPApartmentData

namespace ValuationBuildingData

/-- Construct actual local-field building data at the prescribed maximal split torus
with empty relative-root set, retaining the supplied actual centralizer datum. -/
def ofRelativeRootsEqEmpty (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hΦ : relativeRoots i = ∅) (C : CentralizerDatum i) :
    ValuationBuildingData G := by
  letI := mono_of_isMaximalSplitTorus hi
  exact {
    isConnectedReductive := hG
    S := S
    i := i
    isMaximalSplitTorus := hi
    apartment := KPApartmentData.ofRelativeRootsEqEmpty i (localFieldOrder F) hΦ
    centralizer := C
    isOmegaCompatible := KPApartmentData.isOmegaCompatible_of_relativeRoots_eq_empty _ C hΦ }

/-- The constructed root-free local-field data satisfy the published single-apartment
predicate, including V 7 and the rank-zero affine-root and normalizer conditions. -/
theorem ofRelativeRootsEqEmpty_satisfiesApartmentAxioms
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hΦ : relativeRoots i = ∅) (C : CentralizerDatum i) :
    (ofRelativeRootsEqEmpty hG i hi hΦ C).apartment.SatisfiesApartmentAxioms
      (ofRelativeRootsEqEmpty hG i hi hΦ C).centralizer := by
  have := mono_of_isMaximalSplitTorus hi
  exact KPApartmentData.satisfiesApartmentAxioms_of_relativeRoots_eq_empty _ C hΦ

/-- Specialize the root-free constructor to an anisotropic connected reductive group. -/
def ofIsAnisotropic (hG : IsConnectedReductive G) (ha : IsAnisotropic G)
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (C : CentralizerDatum i) :
    ValuationBuildingData G :=
  ofRelativeRootsEqEmpty hG i hi (ha.relativeRoots_eq_empty hi.isSplitSubtorus) C

end ValuationBuildingData

end Local

end Langlands.Geometry.Building
