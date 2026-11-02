import Langlands.AlgebraicGeometry.Picard.DualPointOriginTriviality
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantCohomologyVanishingProof
import Langlands.AlgebraicGeometry.Modules.RationalPointComplement
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof

/-! # Higher direct images of the Poincaré bundle vanish away from the origin -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
open Langlands.SchemeModule Langlands.Scheme.Modules

section Support

variable (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  (hA : HasDualScheme A)

/-- Away from the origin of the dual, every higher direct image of the Poincaré bundle along
the projection to the dual vanishes. -/
theorem poincareDirectImage_isZero_away_from_origin
    [LocallyOfFiniteType (dualScheme A hA).hom] (n : ℕ) :
    IsZero ((Scheme.Modules.pullback
      (rationalPointComplement (dualScheme A hA).hom {dualOrigin A hA}
        (Set.finite_singleton _)).ι).obj
      ((DerivedSections.higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom
        n).obj (poincareLineBundle A hA).obj)) := by
  let D := dualScheme A hA
  let B := (baseChange D.hom).obj A
  let U := rationalPointComplement D.hom {dualOrigin A hA} (Set.finite_singleton _)
  refine DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres
    universalPerfectSections K D.hom B.X.hom (poincareLineBundle A hA) U ?_ n
  intro x hx m
  let y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ D :=
    Over.homMk (x ≫ U.ι) (by simpa only [Over.mk_hom, Category.assoc] using hx)
  have hy : y ∉ ({dualOrigin A hA} : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk D.hom)) := by
    apply (mem_rationalPointComplement_iff D.hom {dualOrigin A hA}
      (Set.finite_singleton _) y).mp
    change (x (IsLocalRing.closedPoint K)).val ∈ U
    exact (x (IsLocalRing.closedPoint K)).property
  exact algClosedFieldTranslationInvariantCohomologyVanishing K
    ((baseChange (x ≫ U.ι)).obj B) (fibreLineBundle B (poincareLineBundle A hA) (x ≫ U.ι))
    (poincareLineBundle_picardZero A hA K (x ≫ U.ι))
    (fun ⟨e⟩ ↦ hy (dualPoint_eq_origin_of_fibre_iso A hA y e)) m

/-- Every higher direct image of the Poincaré bundle has finite closed support. -/
theorem poincareDirectImage_hasFiniteClosedSupport
    [LocallyOfFiniteType (dualScheme A hA).hom] (n : ℕ) :
    HasFiniteClosedSupport
      ((DerivedSections.higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom
        n).obj (poincareLineBundle A hA).obj) :=
  hasFiniteClosedSupport_of_isZero_rationalPointComplement (dualScheme A hA).hom
    {dualOrigin A hA} (Set.finite_singleton _) _
    (poincareDirectImage_isZero_away_from_origin K A hA n)

/-- Every higher direct image of the Poincaré bundle is supported at the origin of the dual. -/
theorem poincareDirectImage_stalkSupport_subset
    [LocallyOfFiniteType (dualScheme A hA).hom] (n : ℕ) :
    stalkSupport ((DerivedSections.higherDirectImage
        ((baseChange (dualScheme A hA).hom).obj A).X.hom n).obj (poincareLineBundle A hA).obj) ⊆
      {(dualOrigin A hA).left (IsLocalRing.closedPoint K)} := by
  simpa only [rationalPointComplement, TopologicalSpace.Opens.coe_mk, compl_compl,
    Set.image_singleton] using
    stalkSupport_subset_compl_of_isZero_pullback _ _
      (poincareDirectImage_isZero_away_from_origin K A hA n)

end Support

end Langlands.AbelianScheme
