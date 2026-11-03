import Langlands.BruhatTits.Cartan.SpecialCompactDominantQuotient
import Langlands.Geometry.Building.SpecialCompact
import Langlands.Representation.Plancherel.RenardDominantComparisonStatement

/-! # Explicit comparison obligations for the chosen geometric compact subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
  (ν : cocharacterLattice S) (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (restrictionEvaluation s))

local notation "K₀" => D.specialCompactSubgroup x
local notation "Zdom" => dominantCentralizer i ν s h
local notation "QK" => DoubleCoset.Quotient (K₀ : Set (rationalPoints G)) K₀

/-- The separate geometric coverage obligation for this exact `K₀`. -/
def HasSpecialCompactCartanCoverage : Prop :=
  ∀ g : rationalPoints G, ∃ z : Zdom,
    dominantCompactRepresentative D x ν j s h z = DoubleCoset.mk K₀ K₀ g

/-- The missing comparison between the actual induced relation and the actual
centralizer norm kernel `Z(F)^1`. It is a property, not a theorem about weak data. -/
def HasSpecialCompactValuationClassification : Prop :=
  ∀ z z' : Zdom, dominantCompactSetoid D x ν j s h z z' ↔
    z'.val * z.val⁻¹ ∈ rationalCommonNormKernel Z

/-- Both obligations needed to parametrize these double cosets by the actual
valuation chamber. The subgroup is fixed geometrically by `D` and `x`. -/
def SpecialCompactCartanComparison : Prop :=
  HasSpecialCompactCartanCoverage D x ν j s h ∧
    HasSpecialCompactValuationClassification D x ν j s h

/-- Relation classification is equivalently equality of the actual real values. -/
theorem specialCompactSetoid_iff_valuation_eq
    (hc : HasSpecialCompactValuationClassification D x ν j s h) (z z' : Zdom) :
    dominantCompactSetoid D x ν j s h z z' ↔
      centralizerValuation s h z.val = centralizerValuation s h z'.val :=
  (hc z z').trans (centralizerValuation_eq_iff s h z.val z'.val).symm

/-- The same classification in the actual integer-character image. -/
theorem specialCompactSetoid_iff_characterValue_eq
    (hc : HasSpecialCompactValuationClassification D x ν j s h) (z z' : Zdom) :
    dominantCompactSetoid D x ν j s h z z' ↔
      rationalCharacterValuation Z z.val = rationalCharacterValuation Z z'.val := by
  rw [hc z z', ← rationalCharacterValuation_ker, ← div_eq_mul_inv,
    MonoidHom.div_mem_ker_iff, eq_comm]

/-- Classification identifies the existing induced quotient with the existing
norm quotient, by the identity on actual dominant representatives. -/
def dominantCompactNormEquiv
    (hc : HasSpecialCompactValuationClassification D x ν j s h) :
    DominantCompactQuotient D x ν j s h ≃ DominantNormQuotient i ν s h :=
  _root_.Quotient.congrRight (fun z z' =>
    (hc z z').trans QuotientGroup.rightRel_apply.symm)

@[simp]
theorem dominantCompactNormEquiv_class
    (hc : HasSpecialCompactValuationClassification D x ν j s h) (z : Zdom) :
    dominantCompactNormEquiv D x ν j s h hc
        (dominantCompactClass D x ν j s h z) =
      RestrictedRightQuotient.mk _ _ z := rfl

/-- Under the explicit relation comparison, the induced quotient has values
in the chamber of the actual image, without any full cocharacter identification. -/
def dominantCompactChamberEquiv
    (hc : HasSpecialCompactValuationClassification D x ν j s h) :
    DominantCompactQuotient D x ν j s h ≃ dominantValuationImage i ν s h :=
  (dominantCompactNormEquiv D x ν j s h hc).trans
    (dominantNormQuotientEquiv i ν s h)

@[simp]
theorem dominantCompactChamberEquiv_class
    (hc : HasSpecialCompactValuationClassification D x ν j s h) (z : Zdom) :
    dominantCompactChamberEquiv D x ν j s h hc
        (dominantCompactClass D x ν j s h z) =
      ⟨(centralizerValuation s h).rangeRestrict z.val, z.property⟩ := rfl

/-- Coverage and classification together give the genuine chamber bijection. -/
def dominantChamberDoubleCosetEquiv
    (hc : SpecialCompactCartanComparison D x ν j s h) :
    dominantValuationImage i ν s h ≃ QK :=
  (dominantCompactChamberEquiv D x ν j s h hc.2).symm.trans
    (dominantCompactDoubleCosetEquiv D x ν j s h hc.1)

/-- The chamber equivalence sends an actual representative's value to the
double coset of that same actual point. -/
theorem dominantChamberDoubleCosetEquiv_value
    (hc : SpecialCompactCartanComparison D x ν j s h) (z : Zdom) :
    dominantChamberDoubleCosetEquiv D x ν j s h hc
        ⟨(centralizerValuation s h).rangeRestrict z.val, z.property⟩ =
      DoubleCoset.mk K₀ K₀ (rationalPoints.map j z.val) := by
  change dominantCompactDoubleCosetEquiv D x ν j s h hc.1
    ((dominantCompactChamberEquiv D x ν j s h hc.2).symm
      ((dominantCompactChamberEquiv D x ν j s h hc.2)
        (dominantCompactClass D x ν j s h z))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Map any specified set of actual centralizer points to these double cosets. -/
def specialCompactSectionMap (A : Set (rationalPoints Z)) : A → QK :=
  fun a => DoubleCoset.mk K₀ K₀ (rationalPoints.map j a.val)

/-- An actual dominant valuation section gives disjoint and exhaustive double
coset representatives once the two geometric obligations have been supplied. -/
theorem specialCompactSectionMap_bijective
    (hc : SpecialCompactCartanComparison D x ν j s h)
    (A : Set (rationalPoints Z)) (hA : IsDominantValuationSection Zdom A) :
    Function.Bijective (specialCompactSectionMap D x j A) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply hA.2.injOn a.property b.property
    apply Subtype.ext
    exact (specialCompactSetoid_iff_characterValue_eq D x ν j s h hc.2
      ⟨a.val, hA.1 a.property⟩ ⟨b.val, hA.1 b.property⟩).mp hab
  · intro q
    induction q using _root_.Quotient.inductionOn with
    | h g =>
      obtain ⟨z, hz⟩ := hc.1 g
      obtain ⟨a, ha, hav⟩ := hA.2.surjOn
        (show (rationalCharacterValuation Z).rangeRestrict z.val ∈
          (rationalCharacterValuation Z).rangeRestrict '' Zdom from
            ⟨z.val, z.property, rfl⟩)
      refine ⟨⟨a, ha⟩, ?_⟩
      have hrel := (specialCompactSetoid_iff_characterValue_eq D x ν j s h hc.2
        ⟨a, hA.1 ha⟩ z).mpr (congrArg Subtype.val hav)
      exact hrel.trans hz

/-- Package the representative bijection with its actual representative map. -/
def specialCompactSectionEquiv
    (hc : SpecialCompactCartanComparison D x ν j s h)
    (A : Set (rationalPoints Z)) (hA : IsDominantValuationSection Zdom A) :
    A ≃ QK :=
  Equiv.ofBijective (specialCompactSectionMap D x j A)
    (specialCompactSectionMap_bijective D x ν j s h hc A hA)

@[simp]
theorem specialCompactSectionEquiv_apply
    (hc : SpecialCompactCartanComparison D x ν j s h)
    (A : Set (rationalPoints Z)) (hA : IsDominantValuationSection Zdom A) (a : A) :
    specialCompactSectionEquiv D x ν j s h hc A hA a =
      DoubleCoset.mk K₀ K₀ (rationalPoints.map j a.val) := rfl

/-- The precise remaining geometric and lattice obligations for Renard's
representatives at this fixed subgroup. No validity or existence is inferred. -/
def SpecialCompactRenardComparison : Prop :=
  SpecialCompactCartanComparison D x ν j s h ∧
    DominantCentralizerLatticeConclusions i ν s h

end Langlands.Plancherel.RenardCartan
