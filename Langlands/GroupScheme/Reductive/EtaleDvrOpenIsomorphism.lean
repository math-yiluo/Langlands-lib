import Langlands.GroupScheme.Reductive.SplitDvrOpenIsomorphism
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

/-! # Étale removal of the split maximal torus hypothesis -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.EtaleOpenGenericIsomorphism

/-- An injective field-valued base map factors through a fraction field. -/
theorem isIso_field_of_injective
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))} (f : M ⟶ G)
    [IsIso ((baseChange (algebraBaseMap R K)).map f)]
    {L : Type u} [Field L] (φ : R →+* L) (hφ : Function.Injective φ) :
    IsIso ((baseChange (Spec.map (CommRingCat.ofHom φ))).map f) := by
  let ψ : K →+* L := IsFractionRing.lift hφ
  have hfac : Spec.map (CommRingCat.ofHom ψ) ≫ algebraBaseMap R K =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact IsFractionRing.lift_algebraMap hφ r
  rw [← hfac]
  exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff _ _ f).mpr inferInstance

/-- A local extension reflects invertibility on the canonical residue fibre. -/
theorem isIso_residue_of_local_extension
    {R B : Type u} [CommRing R] [IsLocalRing R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    [IsLocalHom (algebraMap R B)]
    {M G : GroupScheme (Spec (CommRingCat.of R))} (f : M ⟶ G)
    (hf : IsIso ((baseChange
      (algebraBaseMap R (IsLocalRing.ResidueField B))).map f)) :
    IsIso ((baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).map f) := by
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField B
  let : Algebra k l := (IsLocalRing.ResidueField.map (algebraMap R B)).toAlgebra
  let : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R B l]
    exact (IsLocalRing.ResidueField.map_comp_residue (algebraMap R B)).symm)
  have hcomp : IsIso ((baseChange (algebraBaseMap k l)).map
      ((baseChange (algebraBaseMap R k)).map f)) := by
    apply (TorusIsomorphismLocus.isIso_comp_baseChange_iff _ _ f).mp
    rw [splitTorus.algebraBaseMap_scalarTower (R := R) (A := k) (B := l)]
    exact hf
  let := hcomp
  exact TorusExistence.isIso_of_isIso_baseChange l
    ((baseChange (algebraBaseMap R k)).map f)

section Local

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hM : IsReductive M) (f : M ⟶ G)
    [IsOpenImmersion f.hom.hom.left]
    [hgeneric : IsIso ((baseChange (algebraBaseMap R K)).map f)]

include hM hgeneric

/-- Étale splitting and local normality remove the supplied torus from the
closed residue-field isomorphism criterion. -/
theorem closedResidueField_isIso :
    IsIso ((baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).map f) := by
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  obtain ⟨A, hA, q, hq, ⟨x, hx⟩, I, hI, i, hi, hmax⟩ :=
    exists_etale_affine_split_maximalTorus _ M hM (IsLocalRing.closedPoint R)
  let : CommRing A := hA
  let : Etale q := hq
  let : Fintype I := hI
  let : Algebra R A := (Spec.preimage q).hom.toAlgebra
  have hqa : algebraBaseMap R A = q := Spec.map_preimage q
  have hspec : Etale (algebraBaseMap R A) := by
    rw [hqa]
    exact hq
  have : Algebra.Etale R A := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec)
  let p : Ideal A := x.asIdeal
  let : p.IsPrime := x.isPrime
  let B := Localization.AtPrime p
  let c := algebraBaseMap A B
  have hp : p.under R = IsLocalRing.maximalIdeal R := by
    rw [← hqa] at hx
    exact congrArg PrimeSpectrum.asIdeal hx
  let : IsDomain B :=
    (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R A p B).1
  let : IsLocalHom (algebraMap R B) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq R A B, ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal B).under A).under R = _
    rw [IsLocalization.AtPrime.under_maximalIdeal B p, hp]
  let : Module.Flat A B := IsLocalization.flat B p.primeCompl
  let : Module.Flat R B := Module.Flat.trans R A B
  let : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let L := FractionRing B
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R B L]
    exact (FaithfulSMul.algebraMap_injective B L).comp
      (FaithfulSMul.algebraMap_injective R B)
  let Mb := (baseChange c).obj ((baseChange q).obj M)
  let Gb := (baseChange c).obj ((baseChange q).obj G)
  let fb : Mb ⟶ Gb := (baseChange c).map ((baseChange q).map f)
  have hMb : IsReductive Mb := (hM.baseChange q).baseChange c
  let : Smooth ((baseChange q).obj M).X.hom := (hM.baseChange q).smooth
  let : IsAffineHom ((baseChange q).obj M).X.hom := (hM.baseChange q).isAffineHom
  let : Smooth ((baseChange q).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom q))
  let : IsAffineHom ((baseChange q).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom q))
  let : Smooth Gb.X.hom :=
    inferInstanceAs (Smooth (pullback.snd ((baseChange q).obj G).X.hom c))
  let : IsAffineHom Gb.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd ((baseChange q).obj G).X.hom c))
  let : IsOpenImmersion ((baseChange q).map f).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) q f.hom.hom inferInstance
  let : IsOpenImmersion fb.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) c
      ((baseChange q).map f).hom.hom inferInstance
  let : Mono fb.hom.hom.left := inferInstance
  have hfac (F : Type u) [CommRing F] [Algebra B F] [Algebra A F]
      [Algebra R F] [IsScalarTower A B F] [IsScalarTower R A F] :
      (algebraBaseMap B F ≫ c) ≫ q = algebraBaseMap R F := by
    rw [← hqa]
    dsimp [c]
    rw [splitTorus.algebraBaseMap_scalarTower (R := A) (A := B) (B := F),
      splitTorus.algebraBaseMap_scalarTower (R := R) (A := A) (B := F)]
  have hL : IsIso ((baseChange (algebraBaseMap B L)).map fb) := by
    apply (TorusIsomorphismLocus.isIso_comp_baseChange_iff c _
      ((baseChange q).map f)).mp
    apply (TorusIsomorphismLocus.isIso_comp_baseChange_iff q _ f).mp
    rw [hfac L]
    exact isIso_field_of_injective (K := K) f (algebraMap R L) hRL
  let := hL
  let ib : splitTorus (Spec (CommRingCat.of B)) I ⟶ Mb :=
    (splitTorus.baseChangeIso c I).inv ≫ (baseChange c).map i
  have hib : IsClosedSubgroup ib :=
    (hi.baseChange c).iso_comp (splitTorus.baseChangeIso c I).symm
  have hmaxb : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) ib :=
    splitTorus.isFibrewiseMaximalTorus_baseChangedHom I _ i hmax c
  have hclosed : IsIso ((baseChange
      (algebraBaseMap B (IsLocalRing.ResidueField B))).map fb) :=
    SplitOpenGenericIsomorphism.closedResidueField_isIso (K := L) hMb fb I ib hib hmaxb
  have hfield : IsIso ((baseChange
      (algebraBaseMap R (IsLocalRing.ResidueField B))).map f) := by
    rw [← hfac (IsLocalRing.ResidueField B)]
    apply (TorusIsomorphismLocus.isIso_comp_baseChange_iff q _ f).mpr
    exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff c _
      ((baseChange q).map f)).mpr hclosed
  exact isIso_residue_of_local_extension (B := B) f hfield

end Local

section Dvr

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hM : IsReductive M) (f : M ⟶ G)
    [IsOpenImmersion f.hom.hom.left]
    [hgeneric : IsIso ((baseChange (algebraBaseMap R K)).map f)]

include hM hgeneric

/-- A generically invertible reductive open subgroup of a smooth affine
DVR group is the whole group, without a splitting hypothesis. -/
theorem isIso_of_dvr : IsIso f := by
  let : Smooth M.X.hom := hM.smooth
  let := closedResidueField_isIso (K := K) hM f
  have : IsIso f.hom.hom :=
    Langlands.AlgebraicGeometry.isIso_of_generic_special (K := K) f.hom.hom
      ⟨inferInstanceAs (IsIso ((baseChange (algebraBaseMap R K)).map f).hom.hom),
        inferInstanceAs (IsIso ((baseChange
          (algebraBaseMap R (IsLocalRing.ResidueField R))).map f).hom.hom)⟩
  have : IsIso f.hom.hom.left := inferInstance
  exact TorusIsomorphismLocus.isIso_of_underlying f

/-- The isomorphism with forward map the original open-subgroup inclusion. -/
def dvrIso : M ≅ G := by
  let := isIso_of_dvr (K := K) hM f
  exact asIso f

@[simp]
theorem dvrIso_hom : (dvrIso (K := K) hM f).hom = f := rfl

end Dvr

end Langlands.GroupScheme.EtaleOpenGenericIsomorphism
