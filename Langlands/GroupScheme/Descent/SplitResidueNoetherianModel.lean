import Langlands.CommutativeAlgebra.StrictHenselianPointedResidueExtension
import Langlands.GroupScheme.Descent.FiniteCoefficientFlatAffineGroup
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Noetherian local coefficient models with split residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.Descent.SplitResidueNoetherianModel

open RelativeMultiplicativeType
open Langlands.CommutativeAlgebra

private theorem specAlgebraMap_comp
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    Spec.algebraMap S T ≫ Spec.algebraMap R S = Spec.algebraMap R T := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R S T]

/-- A prime localization of a finite-type integer algebra, mapping locally into
the original base, with a flat affine finitely presented recovering group and
a diagonalizable special fibre. -/
structure LocalModel
    (A : Type u) [CommRing A] (H : GroupScheme (Spec (CommRingCat.of A))) where
  coefficients : Type u
  [ring : CommRing coefficients]
  finiteType : Algebra.FiniteType ℤ coefficients
  prime : PrimeSpectrum coefficients
  [baseAlgebra : Algebra (Localization.AtPrime prime.asIdeal) A]
  localMap : IsLocalHom (algebraMap (Localization.AtPrime prime.asIdeal) A)
  group : GroupScheme (Spec (CommRingCat.of (Localization.AtPrime prime.asIdeal)))
  affine : IsAffineHom group.X.hom
  flat : Flat group.X.hom
  finitePresentation : LocallyOfFinitePresentation group.X.hom
  specialSplit : IsDiagonalizable
    ((baseChange (Spec.algebraMap (Localization.AtPrime prime.asIdeal)
      prime.asIdeal.ResidueField)).obj group)
  iso : H ≅ (baseChange
    (Spec.algebraMap (Localization.AtPrime prime.asIdeal) A)).obj group

attribute [instance] LocalModel.ring LocalModel.baseAlgebra

theorem LocalModel.noetherian
    {A : Type u} [CommRing A] {H : GroupScheme (Spec (CommRingCat.of A))}
    (D : LocalModel A H) :
    IsNoetherianRing (Localization.AtPrime D.prime.asIdeal) := by
  have := D.finiteType
  have : IsNoetherianRing D.coefficients :=
    Algebra.FiniteType.isNoetherianRing ℤ D.coefficients
  infer_instance

theorem LocalModel.approximation
    {A : Type u} [CommRing A] {H : GroupScheme (Spec (CommRingCat.of A))}
    (D : LocalModel A H) :
    EtaleCompletionApproximation (Localization.AtPrime D.prime.asIdeal) := by
  have := D.finiteType
  exact etaleCompletionApproximation_atPrime D.coefficients D.prime.asIdeal

/-- An existing finite-type coefficient model can be refined to a local model
with diagonalizable residue fibre and an actual local map to the original ring. -/
theorem nonempty_model_of_finiteType_model
    {A T : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing T] [Algebra.FiniteType ℤ T] [Algebra T A]
    (H : GroupScheme (Spec (CommRingCat.of A)))
    (H₀ : GroupScheme (Spec (CommRingCat.of T)))
    [IsAffineHom H₀.X.hom] [Flat H₀.X.hom]
    [LocallyOfFinitePresentation H₀.X.hom]
    (e₀ : H ≅ (baseChange (Spec.algebraMap T A)).obj H₀)
    (hSpecial : IsDiagonalizable
      ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H)) :
    Nonempty (LocalModel A H) := by
  let k := IsLocalRing.ResidueField A
  let : Algebra T k := Algebra.compHom k (algebraMap T A)
  have : IsScalarTower T A k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let q : Ideal T := RingHom.ker (algebraMap T k)
  have : q.IsPrime := RingHom.ker_isPrime _
  let κ := q.ResidueField
  let κmap : κ →ₐ[T] k :=
    Ideal.ResidueField.liftₐ q (Algebra.ofId T k) le_rfl
      (fun x hx => isUnit_iff_ne_zero.mpr hx)
  let : Algebra κ k := κmap.toRingHom.toAlgebra
  have : IsScalarTower T κ k :=
    IsScalarTower.of_algebraMap_eq' κmap.comp_algebraMap.symm
  let Hκ := (baseChange (Spec.algebraMap T κ)).obj H₀
  let Hk := (baseChange (Spec.algebraMap T k)).obj H₀
  let E₀ : (baseChange (Spec.algebraMap A k)).obj H ≅ Hk :=
    (baseChange (Spec.algebraMap A k)).mapIso e₀ ≪≫
      pullbackComparison (Spec.algebraMap T A) (Spec.algebraMap A k)
        (Spec.algebraMap T k) (specAlgebraMap_comp T A k) H₀
  have hHk : IsDiagonalizable Hk := hSpecial.of_iso E₀.symm
  let Eκ : (baseChange (Spec.algebraMap κ k)).obj Hκ ≅ Hk :=
    pullbackComparison (Spec.algebraMap T κ) (Spec.algebraMap κ k)
      (Spec.algebraMap T k) (specAlgebraMap_comp T κ k) H₀
  have hMT : Langlands.GroupScheme.IsMultiplicativeType Hκ := by
    obtain ⟨M, hM, hfg, ⟨e⟩⟩ := hHk.of_iso Eκ
    exact ⟨k, inferInstance, inferInstance, M, hM, hfg,
      ⟨e ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of k) M).symm⟩⟩
  obtain ⟨K, hK, aK, hfin, hgal, M, hM, hfg, ⟨eK⟩⟩ :=
    multiplicativeTypeFiniteGaloisSplitting κ Hκ hMT
  let : Algebra T K := ((algebraMap κ K).comp (algebraMap T κ)).toAlgebra
  have : IsScalarTower T κ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let HK := (baseChange (Spec.algebraMap T K)).obj H₀
  let EK : (baseChange (Spec.algebraMap κ K)).obj Hκ ≅ HK :=
    pullbackComparison (Spec.algebraMap T κ) (Spec.algebraMap κ K)
      (Spec.algebraMap T K) (specAlgebraMap_comp T κ K) H₀
  have hHK : IsDiagonalizable HK :=
    IsDiagonalizable.of_iso EK.symm
      ⟨M, hM, hfg, ⟨eK ≪≫ Diagonalizable.relativeModelIso (CommRingCat.of K) M⟩⟩
  obtain ⟨E, _, _, hE, Q, e, σ, -, he, -, σloc, -, hlocal⟩ :=
    exists_pointed_etale_residue_extension (A := A) (k := k)
      IsLocalRing.residue_surjective q (K := K)
  have : Algebra.FiniteType ℤ E :=
    Algebra.FiniteType.trans (S := T) inferInstance inferInstance
  let κQ := Q.asIdeal.ResidueField
  have heinv : e.symm.toRingHom.comp (algebraMap T K) = algebraMap T κQ := by
    ext t
    apply e.injective
    change e (e.symm (algebraMap T K t)) =
      e (algebraMap E κQ (algebraMap T E t))
    rw [e.apply_symm_apply, he]
  let b : Spec (CommRingCat.of κQ) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hb : b ≫ Spec.algebraMap T K = Spec.algebraMap T κQ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, heinv]
  let EQ : (baseChange b).obj HK ≅ (baseChange (Spec.algebraMap T κQ)).obj H₀ :=
    pullbackComparison (Spec.algebraMap T K) b (Spec.algebraMap T κQ) hb H₀
  have hHQ : IsDiagonalizable ((baseChange (Spec.algebraMap T κQ)).obj H₀) :=
    IsDiagonalizable.of_iso EQ.symm (hHK.baseChange b)
  let P := Localization.AtPrime Q.asIdeal
  let : Algebra P A := σloc.toRingHom.toAlgebra
  have : IsScalarTower T P A :=
    IsScalarTower.of_algebraMap_eq' σloc.comp_algebraMap.symm
  let HP := (baseChange (Spec.algebraMap T P)).obj H₀
  let EP : (baseChange (Spec.algebraMap P κQ)).obj HP ≅
      (baseChange (Spec.algebraMap T κQ)).obj H₀ :=
    pullbackComparison (Spec.algebraMap T P) (Spec.algebraMap P κQ)
      (Spec.algebraMap T κQ) (specAlgebraMap_comp T P κQ) H₀
  let EA : (baseChange (Spec.algebraMap P A)).obj HP ≅
      (baseChange (Spec.algebraMap T A)).obj H₀ :=
    pullbackComparison (Spec.algebraMap T P) (Spec.algebraMap P A)
      (Spec.algebraMap T A) (specAlgebraMap_comp T P A) H₀
  exact ⟨{
    coefficients := E
    finiteType := inferInstance
    prime := Q
    localMap := hlocal
    group := HP
    affine := by
      change IsAffineHom (pullback.snd H₀.X.hom (Spec.algebraMap T P))
      infer_instance
    flat := by
      change Flat (pullback.snd H₀.X.hom (Spec.algebraMap T P))
      infer_instance
    finitePresentation := by
      change LocallyOfFinitePresentation (pullback.snd H₀.X.hom (Spec.algebraMap T P))
      infer_instance
    specialSplit := IsDiagonalizable.of_iso EP hHQ
    iso := e₀ ≪≫ EA.symm }⟩

/-- A flat affine finitely presented group over a strictly Henselian base whose
special fibre is diagonalizable has a Noetherian local coefficient model with
split special fibre, mapping locally into the original base. -/
theorem nonempty_model
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (H : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffineHom H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hSpecial : IsDiagonalizable
      ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H)) :
    Nonempty (LocalModel A H) := by
  let : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨D, -⟩ := FiniteCoefficient.exists_flatAffineGroupModel (ULift.{u} ℤ) A H ∅
  have : Algebra.FiniteType (ULift.{u} ℤ) D.coefficients :=
    (Subalgebra.fg_iff_finiteType _).mp D.finite
  have : Algebra.FiniteType ℤ D.coefficients :=
    Algebra.FiniteType.trans (S := ULift.{u} ℤ) inferInstance inferInstance
  let := D.affine
  let := D.flat
  let := D.finitePresentation
  exact nonempty_model_of_finiteType_model H D.group D.iso hSpecial

end Langlands.GroupScheme.Descent.SplitResidueNoetherianModel
