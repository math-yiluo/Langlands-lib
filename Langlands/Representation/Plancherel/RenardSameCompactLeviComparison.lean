import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.BruhatTits.Cartan.DominantQuotient
import Langlands.Representation.Plancherel.RenardDominantComparisonStatement

/-! # Cartan comparison obligations inside the same compact Levi intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
  (ν : cocharacterLattice S) (J : Set (characterLattice S))
  (jM : Z ⟶ Standard.leviScheme i ν J) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (restrictionEvaluation s))

local instance : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

local notation "iM" => Standard.leviTorusHom i ν J
local notation "KM" => D.specialCompactLeviSubgroup ν J x
local notation "ZdomM" => dominantCentralizer iM ν s h
local notation "QM" =>
  DoubleCoset.Quotient (KM : Set (rationalPoints (Standard.leviScheme i ν J))) KM

/-- Coverage by dominant points for the preimage of the fixed ambient `K₀`
in the actual standard Levi, with the same centralizer valuation. -/
def HasSameCompactLeviCoverage : Prop :=
  ∀ m : rationalPoints (Standard.leviScheme i ν J), ∃ z : ZdomM,
    DoubleCoset.mk KM KM (rationalPoints.map jM z.val) = DoubleCoset.mk KM KM m

/-- The valuation-kernel comparison for the relation induced by this exact
Levi compact intersection. This is an obligation, not a structural theorem. -/
def HasSameCompactLeviClassification : Prop :=
  ∀ z z' : ZdomM,
    DoubleCoset.mk KM KM (rationalPoints.map jM z.val) =
        DoubleCoset.mk KM KM (rationalPoints.map jM z'.val) ↔
      z'.val * z.val⁻¹ ∈ rationalCommonNormKernel Z

/-- Both geometric obligations for the actual Levi and the same ambient
compact subgroup. No independently chosen compact subgroup is a parameter. -/
def SameCompactLeviCartanComparison : Prop :=
  HasSameCompactLeviCoverage D x ν J jM s h ∧
    HasSameCompactLeviClassification D x ν J jM s h

/-- The supplied classification and coverage construct the genuine norm-quotient
bijection. Well-definedness is part of the existing conditional constructor. -/
def sameCompactLeviNormEquiv
    (hc : SameCompactLeviCartanComparison D x ν J jM s h) :
    DominantNormQuotient iM ν s h ≃ QM :=
  RestrictedRightQuotient.doubleCosetEquiv ZdomM (rationalCommonNormKernel Z)
    (rationalPoints.map jM) KM hc.1 hc.2

@[simp]
theorem sameCompactLeviNormEquiv_class
    (hc : SameCompactLeviCartanComparison D x ν J jM s h) (z : ZdomM) :
    sameCompactLeviNormEquiv D x ν J jM s h hc
        (RestrictedRightQuotient.mk _ _ z) =
      DoubleCoset.mk KM KM (rationalPoints.map jM z.val) := rfl

/-- The Levi chamber in the same actual valuation image parametrizes these
double cosets once the two comparison obligations have been supplied. -/
def sameCompactLeviChamberEquiv
    (hc : SameCompactLeviCartanComparison D x ν J jM s h) :
    dominantValuationImage iM ν s h ≃ QM :=
  (dominantNormQuotientEquiv iM ν s h).symm.trans
    (sameCompactLeviNormEquiv D x ν J jM s h hc)

theorem sameCompactLeviChamberEquiv_value
    (hc : SameCompactLeviCartanComparison D x ν J jM s h) (z : ZdomM) :
    sameCompactLeviChamberEquiv D x ν J jM s h hc
        ⟨(centralizerValuation s h).rangeRestrict z.val, z.property⟩ =
      DoubleCoset.mk KM KM (rationalPoints.map jM z.val) := by
  change sameCompactLeviNormEquiv D x ν J jM s h hc
    ((dominantNormQuotientEquiv iM ν s h).symm
      ((dominantNormQuotientEquiv iM ν s h)
        (RestrictedRightQuotient.mk _ _ z))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The representative map uses actual centralizer points in this actual Levi. -/
def sameCompactLeviSectionMap (A : Set (rationalPoints Z)) : A → QM :=
  fun a => DoubleCoset.mk KM KM (rationalPoints.map jM a.val)

/-- Every dominant valuation section supplies disjoint, exhaustive representatives
for the same compact Levi intersection, under the explicit comparison. -/
theorem sameCompactLeviSectionMap_bijective
    (hc : SameCompactLeviCartanComparison D x ν J jM s h)
    (A : Set (rationalPoints Z)) (hA : IsDominantValuationSection ZdomM A) :
    Function.Bijective (sameCompactLeviSectionMap D x ν J jM A) := by
  have hvalue (z z' : ZdomM) :
      DoubleCoset.mk KM KM (rationalPoints.map jM z.val) =
          DoubleCoset.mk KM KM (rationalPoints.map jM z'.val) ↔
        rationalCharacterValuation Z z.val = rationalCharacterValuation Z z'.val := by
    rw [hc.2 z z', ← rationalCharacterValuation_ker, ← div_eq_mul_inv,
      MonoidHom.div_mem_ker_iff, eq_comm]
  constructor
  · intro a b hab
    apply Subtype.ext
    apply hA.2.injOn a.property b.property
    apply Subtype.ext
    exact (hvalue ⟨a.val, hA.1 a.property⟩ ⟨b.val, hA.1 b.property⟩).mp hab
  · intro q
    induction q using _root_.Quotient.inductionOn with
    | h m =>
      obtain ⟨z, hz⟩ := hc.1 m
      obtain ⟨a, ha, hav⟩ := hA.2.surjOn
        (show (rationalCharacterValuation Z).rangeRestrict z.val ∈
          (rationalCharacterValuation Z).rangeRestrict '' ZdomM from
            ⟨z.val, z.property, rfl⟩)
      refine ⟨⟨a, ha⟩, ?_⟩
      exact ((hvalue ⟨a, hA.1 ha⟩ z).mpr (congrArg Subtype.val hav)).trans hz

/-- Package the actual representative map as an equivalence. -/
def sameCompactLeviSectionEquiv
    (hc : SameCompactLeviCartanComparison D x ν J jM s h)
    (A : Set (rationalPoints Z)) (hA : IsDominantValuationSection ZdomM A) :
    A ≃ QM :=
  Equiv.ofBijective (sameCompactLeviSectionMap D x ν J jM A)
    (sameCompactLeviSectionMap_bijective D x ν J jM s h hc A hA)

@[simp]
theorem sameCompactLeviSectionEquiv_apply
    (hc : SameCompactLeviCartanComparison D x ν J jM s h)
    (A : Set (rationalPoints Z)) (hA : IsDominantValuationSection ZdomM A) (a : A) :
    sameCompactLeviSectionEquiv D x ν J jM s h hc A hA a =
      DoubleCoset.mk KM KM (rationalPoints.map jM a.val) := rfl

omit [Mono i.hom.hom.left] in
/-- Root containment compares the two chambers without changing the valuation. -/
theorem ambientDominant_subset_leviDominant
    (hroots : positiveRelativeRoots iM ν ⊆ positiveRelativeRoots i ν) :
    dominantCentralizer i ν s h ⊆ ZdomM :=
  fun _ hz a ha => hz a (hroots ha)

omit [Mono i.hom.hom.left] in
/-- The positive uniformizer sets use the same `C₀`, with fewer inequalities
in the Levi when its positive roots are ambient positive roots. -/
theorem ambientC0Plus_subset_leviC0Plus
    (hroots : positiveRelativeRoots iM ν ⊆ positiveRelativeRoots i ν) :
    C0Plus S s (positiveRelativeRoots i ν) ⊆ C0Plus S s (positiveRelativeRoots iM ν) := by
  rintro z ⟨c, hc, rfl⟩
  exact ⟨c, fun a ha => hc a (hroots ha), rfl⟩

omit [Mono i.hom.hom.left] in
/-- One full transversal is cut by each chamber in the same actual centralizer. -/
theorem ambientTildeC0Plus_subset_leviTildeC0Plus
    (hroots : positiveRelativeRoots iM ν ⊆ positiveRelativeRoots i ν)
    (F0 : Set (rationalPoints Z)) :
    tildeC0Plus s F0 (dominantCentralizer i ν s h) ⊆ tildeC0Plus s F0 ZdomM :=
  fun _ hz => ⟨hz.1, ambientDominant_subset_leviDominant ν J s h hroots hz.2⟩

variable (j : Z ⟶ G)

/-- The precise same-`K₀` standard-Levi comparison obligations. The represented
centralizer, torus factor, positive roots and lattice data are all compared
explicitly. This property does not assert inheritance for weak apartment data. -/
def SpecialCompactStandardLeviCompatibility : Prop :=
  ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∃ jM : Z ⟶ Standard.leviScheme i ν J,
      IsClosedSubgroup jM ∧
      (torusCentralizer (Standard.leviTorusHom i ν J)).IsRepresentedBy jM ∧
      jM ≫ Standard.leviHom i ν J = j ∧
      s ≫ jM = Standard.leviTorusHom i ν J ∧
      positiveRelativeRoots (Standard.leviTorusHom i ν J) ν ⊆ positiveRelativeRoots i ν ∧
      SameCompactLeviCartanComparison D x ν J jM s h ∧
      DominantCentralizerLatticeConclusions (Standard.leviTorusHom i ν J) ν s h

end Langlands.Plancherel.RenardCartan
