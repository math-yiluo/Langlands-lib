import Langlands.FieldTheory.DimensionLEOneArithmetic
import Langlands.ClassFieldTheory.Local.RelativeH1Proof
import Langlands.Cohomology.Tate.CohomologicallyTrivial
import Langlands.Cohomology.Tate.PGroupTateVanishingProof
import Langlands.Cohomology.Tate.SylowTateVanishingProof
import Langlands.Cohomology.Tate.Reindex

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Langlands.ClassFieldTheory.Local

universe u

namespace Langlands.FieldTheory

private def fixedFieldSubgroupCohomologyIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (unitsRepresentation K L)) n ≅
      relativeCohomology (IntermediateField.fixedField H) L n :=
  groupCohomology.mapIso (IntermediateField.subgroupEquivAlgEquiv H)
    (LinearEquiv.refl IntegerScalars (Additive Lˣ)) (fun _ => rfl) n

/-- All actual Tate degrees of the finite Galois units representation vanish. -/
theorem HasDimensionLEOne.finite_units_tate_isZero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype Gal(L/K)]
    (hK : HasDimensionLEOne K) (n : ℤ) :
    IsZero (tateCohomology (unitsRepresentation K L) n) := by
  apply Langlands.Tate.sylowTateVanishing IntegerScalars Gal(L/K)
    (unitsRepresentation K L) n
  intro p hp P _
  let H : Subgroup Gal(L/K) := P
  let E := IntermediateField.fixedField H
  let : FiniteDimensional K E := IntermediateField.finiteDimensional_left E
  let : Algebra.IsSeparable K E :=
    Algebra.isSeparable_tower_bot_of_isSeparable K E L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  have hE : HasDimensionLEOne E := hK.finite_separable_extension
  have h1 : IsZero (groupCohomology
      (Rep.res H.subtype (unitsRepresentation K L)) 1) := by
    let : Subsingleton (relativeCohomology E L 1) := finiteRelativeH1Vanishing E L
    exact (ModuleCat.isZero_of_subsingleton (relativeCohomology E L 1)).of_iso
      (fixedFieldSubgroupCohomologyIso K L H 1)
  have h2 : IsZero (groupCohomology
      (Rep.res H.subtype (unitsRepresentation K L)) 2) := by
    let : Subsingleton (relativeCohomology E L 2) := hE.trivial_finite_relative_h2 L
    exact (ModuleCat.isZero_of_subsingleton (relativeCohomology E L 2)).of_iso
      (fixedFieldSubgroupCohomologyIso K L H 2)
  exact Langlands.Tate.pGroupTateVanishing p hp P.1 P.isPGroup'
    (Rep.res H.subtype (unitsRepresentation K L)) 1
    (h1.of_iso ((TateCohomology.isoGroupCohomology 1).app _))
    (h2.of_iso ((TateCohomology.isoGroupCohomology 2).app _)) n

private def fixedFieldUnitsIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (H : Subgroup Gal(L/K)) :
    Rep.res (IntermediateField.subgroupEquivAlgEquiv H).symm.toMonoidHom
        (Rep.res H.subtype (unitsRepresentation K L)) ≅
      unitsRepresentation (IntermediateField.fixedField H) L :=
  Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.refl IntegerScalars (Additive Lˣ)) (fun _ => rfl))

/-- The norm criterion makes finite Galois units cohomologically trivial
on every subgroup, with their actual automorphism action. -/
theorem HasDimensionLEOne.finite_units_cohomologicallyTrivial
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hK : HasDimensionLEOne K) :
    Langlands.Tate.IsCohomologicallyTrivial (unitsRepresentation K L) := by
  intro H _ n
  let E := IntermediateField.fixedField H
  let : FiniteDimensional K E := IntermediateField.finiteDimensional_left E
  let : Algebra.IsSeparable K E :=
    Algebra.isSeparable_tower_bot_of_isSeparable K E L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  let : Fintype Gal(L/E) := Fintype.ofFinite _
  have hE : HasDimensionLEOne E := hK.finite_separable_extension
  exact (hE.finite_units_tate_isZero n).of_iso
    (Langlands.Tate.reindexIso (IntermediateField.subgroupEquivAlgEquiv H)
      (fixedFieldUnitsIso K L H) n)

end Langlands.FieldTheory
