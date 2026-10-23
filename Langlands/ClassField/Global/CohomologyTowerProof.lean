import Langlands.ClassField.Global.CohomologyTowerStatement

/-! # Proof of the idele-class cohomology tower identities -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open CategoryTheory

universe u

namespace Langlands.Global.AdelicFunctoriality

section InclusionTower

variable {K L M : Type u} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- The place below a place in a tower is independent of the intermediate field. -/
theorem finitePlace_under_under (q : HeightOneSpectrum (𝓞 M)) :
    (q.under (𝓞 L)).under (𝓞 K) = q.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) q.asIdeal

/-- The actual finite-adele inclusions compose in a scalar tower. -/
theorem finiteAdeleInclusion_trans (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleInclusion (K := L) (L := M) (finiteAdeleInclusion (K := K) (L := L) x) =
      finiteAdeleInclusion (K := K) (L := M) x := by
  apply FiniteAdeleRing.ext
  intro q
  change FiniteExtension.completionMap (q.under (𝓞 L)) q
      (FiniteExtension.completionMap ((q.under (𝓞 L)).under (𝓞 K)) (q.under (𝓞 L))
        (x ((q.under (𝓞 L)).under (𝓞 K)))) =
    FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K)))
  exact ClassField.Global.adicCompletion_coordinate_eq
    (finitePlace_under_under (K := K) (L := L) q)
    (fun y => FiniteExtension.completionMap (q.under (𝓞 L)) q
      (FiniteExtension.completionMap ((q.under (𝓞 L)).under (𝓞 K)) (q.under (𝓞 L)) y))
    (FiniteExtension.completionMap (q.under (𝓞 K)) q)
    ((FiniteExtension.continuous_completionMap (q.under (𝓞 L)) q).comp
      (FiniteExtension.continuous_completionMap
        ((q.under (𝓞 L)).under (𝓞 K)) (q.under (𝓞 L))))
    (FiniteExtension.continuous_completionMap (q.under (𝓞 K)) q)
    (fun a => by simp only [FiniteExtension.completionMap_coe,
      ← IsScalarTower.algebraMap_apply K L M])
    (fun p => x p)

/-- The actual adele inclusions compose, at both finite and infinite places. -/
theorem adeleInclusion_trans (x : AdeleRing (𝓞 K) K) :
    adeleInclusion (K := L) (L := M) (adeleInclusion (K := K) (L := L) x) =
      adeleInclusion (K := K) (L := M) x := by
  refine Prod.ext ?_ (finiteAdeleInclusion_trans x.2)
  change infiniteAdeleMap (algebraMap L M) (infiniteAdeleMap (algebraMap K L) x.1) =
    infiniteAdeleMap (algebraMap K M) x.1
  rw [← RingHom.comp_apply, ← infiniteAdeleMap_comp, ← IsScalarTower.algebraMap_eq K L M]

/-- The actual idele-class inclusions compose in a scalar tower. -/
theorem ideleClassInclusion_trans (x : IdeleClassGroup (𝓞 K) K) :
    ideleClassInclusion (K := L) (L := M) (ideleClassInclusion (K := K) (L := L) x) =
      ideleClassInclusion (K := K) (L := M) x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change (QuotientGroup.mk
      (ideleInclusion (K := L) (L := M) (ideleInclusion (K := K) (L := L) a)) :
        IdeleClassGroup (𝓞 M) M) = QuotientGroup.mk (ideleInclusion (K := K) (L := M) a)
    exact congrArg (QuotientGroup.mk : IdeleGroup (𝓞 M) M → IdeleClassGroup (𝓞 M) M)
      (Units.ext (adeleInclusion_trans (K := K) (L := L) (M := M) a))

end InclusionTower

end Langlands.Global.AdelicFunctoriality

namespace Langlands.ClassField.Global

open Langlands.Global.AdelicFunctoriality

/-- Restriction through two successive base fields equals direct restriction. -/
theorem ideleClassRestrictionTransitivity : IdeleClassRestrictionTransitivity.{u} := by
  intro F K L E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n a
  have h : relativeIdeleClassRestriction F K E n ≫ relativeIdeleClassRestriction K L E n =
      relativeIdeleClassRestriction F L E n := by
    rw [relativeIdeleClassRestriction, relativeIdeleClassRestriction,
      relativeIdeleClassRestriction, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr
    · ext σ x
      rfl
    · rfl
  exact ConcreteCategory.congr_hom h a

/-- Inflation through two successive upper fields equals direct inflation. -/
theorem ideleClassInflationTransitivity : IdeleClassInflationTransitivity.{u} := by
  intro F E L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n a
  have h : relativeIdeleClassInflation F E L n ≫ relativeIdeleClassInflation F L M n =
      relativeIdeleClassInflation F E M n := by
    rw [relativeIdeleClassInflation, relativeIdeleClassInflation,
      relativeIdeleClassInflation, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr
    · exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp F E L M).symm
    · ext x
      exact congrArg Additive.ofMul (ideleClassInclusion_trans x.toMul)
  exact ConcreteCategory.congr_hom h a

/-- Inflation commutes with restriction of the base field. -/
theorem ideleClassInflationRestrictionCompatibility :
    IdeleClassInflationRestrictionCompatibility.{u} := by
  intro F K E L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  let : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  intro n a
  have h : relativeIdeleClassInflation F E L n ≫ relativeIdeleClassRestriction F K L n =
      relativeIdeleClassRestriction F K E n ≫ relativeIdeleClassInflation K E L n := by
    rw [relativeIdeleClassInflation, relativeIdeleClassRestriction,
      relativeIdeleClassRestriction, relativeIdeleClassInflation,
      ← groupCohomology.map_comp, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr
    · ext σ x
      apply (algebraMap E L).injective
      change algebraMap E L ((σ.restrictScalars F).restrictNormal E x) =
        algebraMap E L ((σ.restrictNormal E).restrictScalars F x)
      rw [AlgEquiv.restrictNormal_commutes]
      exact (AlgEquiv.restrictNormal_commutes σ E x).symm
    · rfl
  exact ConcreteCategory.congr_hom h a

/-- The actual idele-class maps satisfy all three tower identities. -/
theorem ideleClassCohomologyTowerLaws : IdeleClassCohomologyTowerLaws.{u} :=
  ⟨ideleClassRestrictionTransitivity, ideleClassInflationTransitivity,
    ideleClassInflationRestrictionCompatibility⟩

end Langlands.ClassField.Global
