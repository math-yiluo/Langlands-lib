import Langlands.Representation.Plancherel.RenardDominantFiniteCover
import Langlands.Representation.Plancherel.RenardDominantTransversal

/-! # Actual full-product sections and conditional dominant assembly -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise TensorProduct

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}
  (s : S.toGrp ⟶ Z)

/-- Valuation of a pair consisting of an actual uniformizer point and a
chosen actual representative. -/
def fullProductValuation (F0 : Set (rationalPoints Z))
    (cf : (C0 S s) × F0) : rationalCharacterValuationImage Z :=
  (rationalCharacterValuation Z).rangeRestrict (cf.1.val * cf.2.val)

/-- A bijection on the uniformizer subgroup and a full-lattice transversal
give a bijection on actual product pairs. -/
theorem fullProductValuation_bijective
    (hC : Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z)))
    {F0 : Set (rationalPoints Z)} (hF : IsFiniteLatticeTransversal s F0) :
    Function.Bijective (fullProductValuation s F0) := by
  constructor
  · rintro ⟨c, f⟩ ⟨d, g⟩ hprod
    have hres := congrArg (QuotientGroup.mk' (splitValuationImage s)) hprod
    change latticeResidue s (c.val * f.val) = latticeResidue s (d.val * g.val) at hres
    rw [map_mul, map_mul, latticeResidue_eq_one_of_mem_C0 s c.property,
      latticeResidue_eq_one_of_mem_C0 s d.property, one_mul, one_mul] at hres
    have hfg : f = g := hF.2.injective hres
    subst g
    have hcdval : (rationalCharacterValuation Z).rangeRestrict c.val =
        (rationalCharacterValuation Z).rangeRestrict d.val := by
      change (rationalCharacterValuation Z).rangeRestrict (c.val * f.val) =
        (rationalCharacterValuation Z).rangeRestrict (d.val * f.val) at hprod
      simpa only [map_mul, mul_left_inj] using hprod
    have hcd : c = d := Subtype.ext (hC.injOn c.property d.property hcdval)
    exact Prod.ext hcd rfl
  · intro v
    obtain ⟨z, rfl⟩ := (rationalCharacterValuation Z).rangeRestrict_surjective v
    obtain ⟨f, hf⟩ := hF.2.surjective (latticeResidue s z)
    have hdiff : (rationalCharacterValuation Z).rangeRestrict z /
        (rationalCharacterValuation Z).rangeRestrict f.val ∈ splitValuationImage s :=
      (QuotientGroup.eq_iff_div_mem (N := splitValuationImage s)).mp hf.symm
    obtain ⟨c, hc, hcv⟩ := hC.surjOn hdiff
    refine ⟨⟨⟨c, hc⟩, f⟩, ?_⟩
    change (rationalCharacterValuation Z).rangeRestrict (c * f.val) =
      (rationalCharacterValuation Z).rangeRestrict z
    rw [map_mul, hcv, div_mul_cancel]

/-- The same lattice hypotheses give the actual full valuation section and
nonrepetition of all product pairs. -/
theorem isValuationSection_tildeC0_of_bijOn
    (hC : Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z)))
    {F0 : Set (rationalPoints Z)} (hF : IsFiniteLatticeTransversal s F0) :
    IsValuationSection (tildeC0 s F0) ∧
      Function.Injective (fun cf : (C0 S s) × F0 =>
        rationalCharacterValuation Z (cf.1.val * cf.2.val)) := by
  have hprod := fullProductValuation_bijective s hC hF
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨c, hc, f, hf, hcf⟩ := (mem_tildeC0 s F0 x.val).mp x.property
    obtain ⟨d, hd, g, hg, hdg⟩ := (mem_tildeC0 s F0 y.val).mp y.property
    have hp : fullProductValuation s F0 ⟨⟨c, hc⟩, ⟨f, hf⟩⟩ =
        fullProductValuation s F0 ⟨⟨d, hd⟩, ⟨g, hg⟩⟩ := by
      change (rationalCharacterValuation Z).rangeRestrict (c * f) =
        (rationalCharacterValuation Z).rangeRestrict (d * g)
      rw [hcf, hdg]
      exact hxy
    have heq := congrArg (fun cf : (C0 S s) × F0 => cf.1.val * cf.2.val)
      (hprod.injective hp)
    exact Subtype.ext (hcf.symm.trans (heq.trans hdg))
  · intro v
    obtain ⟨⟨c, f⟩, hcf⟩ := hprod.surjective v
    exact ⟨⟨c.val * f.val, (mem_tildeC0 s F0 _).mpr
      ⟨c.val, c.property, f.val, f.property, rfl⟩⟩, hcf⟩
  · intro x y hxy
    exact hprod.injective (Subtype.ext hxy)

variable (h : Function.Bijective (restrictionEvaluation s))
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Any full-lattice transversal cuts to the actual dominant valuation section. -/
theorem isDominantValuationSection_tildeC0Plus_of_bijOn
    (hC : Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z)))
    {F0 : Set (rationalPoints Z)} (hF : IsFiniteLatticeTransversal s F0) :
    IsDominantValuationSection (dominantCentralizer i ν s h)
      (tildeC0Plus s F0 (dominantCentralizer i ν s h)) ∧
      Set.BijOn (centralizerValuation s h).rangeRestrict
        (tildeC0Plus s F0 (dominantCentralizer i ν s h))
        (dominantValuationImage i ν s h) := by
  have hdom := isDominantValuationSection_inter s h i ν
    (isValuationSection_tildeC0_of_bijOn s hC hF).1
  exact ⟨hdom, isDominantValuationSection_bijOn_centralizerValuation s h i ν hdom⟩

/-- Chamber-compatible full transversals give the positive section and
nonrepetition by restriction from the full product pairs. -/
theorem chamberCompatible_positiveProducts_of_bijOn
    (hC : Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z)))
    {F0 : Set (rationalPoints Z)}
    (hF : IsChamberCompatibleTransversal s (positiveRelativeRoots i ν)
      (dominantCentralizer i ν s h) F0) :
    IsDominantValuationSection (dominantCentralizer i ν s h)
      (C0Plus S s (positiveRelativeRoots i ν) * F0) ∧
      HasNonrepeatingPositiveProducts s (positiveRelativeRoots i ν) F0 := by
  have hfull := isValuationSection_tildeC0_of_bijOn s hC hF.1
  have hdom := (isDominantValuationSection_tildeC0Plus_of_bijOn s h i ν hC hF.1).1
  rw [hF.2.2] at hdom
  refine ⟨hdom, ?_⟩
  intro x y hxy
  have hp := hfull.2
    (a₁ := ⟨⟨x.1.val, C0Plus_subset_C0 S s _ x.1.property⟩, x.2⟩)
    (a₂ := ⟨⟨y.1.val, C0Plus_subset_C0 S s _ y.1.property⟩, y.2⟩) hxy
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun cf : (C0 S s) × F0 => cf.1.val) hp)
  · exact congrArg (fun cf : (C0 S s) × F0 => cf.2) hp

/-- All seven actual dominant conclusions follow from the stated lattice
comparison and finite root support. This is a conditional assembly helper. -/
theorem dominantCentralizerLatticeConclusions_of_latticeComparison
    (hroots : (positiveRelativeRoots i ν).Finite)
    (hindex : (splitValuationImage s).FiniteIndex)
    (hC : Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z))) :
    DominantCentralizerLatticeConclusions i ν s h := by
  refine ⟨centralizerValuation_uniformizerSection s h,
    C0Plus_eq_inter_dominant s h i ν,
    centralizerValuationImageEquiv_image_dominant s h i ν,
    exists_finite_dominant_latticeTransversal s h i ν hroots hindex,
    ?_, exists_finite_positiveProductCover s h i ν hroots hindex hC.surjOn, ?_⟩
  · intro F0 hF
    exact isDominantValuationSection_tildeC0Plus_of_bijOn s h i ν hC hF
  · intro F0 hF
    exact chamberCompatible_positiveProducts_of_bijOn s h i ν hC hF

end Langlands.Plancherel.RenardCartan
