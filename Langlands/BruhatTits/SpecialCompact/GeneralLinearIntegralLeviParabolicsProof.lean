import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralLeviParabolicsStatement
import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralParabolicsProof
import Langlands.GroupScheme.Rational.ParabolicFunctor
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Rational.StandardLeviNestedTransport
import Langlands.GroupScheme.Rational.TitsStandardParabolic
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer

/-! # Inheritance of integral Weyl representatives and parabolic factorizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

set_option maxHeartbeats 1000000 in
/-- The ambient Weyl and factorization clauses restrict to each actual standard Levi
at the inherited integral subgroup. -/
theorem generalLinearIntegralLeviParabolics :
    GeneralLinearIntegralLeviParabolicsStatement.{u} := by
  intro F _ _ _ _ N ν
  dsimp only
  intro hν J hJ
  let G := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
  let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
  let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  let iL := Standard.leviTorusHom i ν J
  let f := rationalPoints.map j
  let KL := K.comap f
  let : IsAffineHom L.X.hom := (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  change HasWeylRepresentatives iL KL ∧ HasParabolicFactorization iL ν KL
  have hG : IsConnectedReductive G := isConnectedReductive_generalLinear F (Fin N)
  have hi : IsMaximalSplitTorus i := GeneralLinear.isMaximalSplitTorus_diagonalTorus F
  obtain ⟨-, hiL, -, hs, -, -, hfamily⟩ :=
    StandardLeviNested.leviScheme_rankPackage hG i hi ν hν J hJ
  have hrep := Standard.isRepresentedBy_leviHom i ν J
  let : Mono j.hom.hom := hrep.1
  let points := hrep.rationalPointsEquiv
  have hmap (x : rationalPoints L) : f x ∈ standardLeviPoints i ν J := (points x).property
  have hpull (x : standardLeviPoints i ν J) : f (points.symm x) = x.val :=
    hrep.rationalPointsEquiv_symm_comp x
  have hinj : Function.Injective f :=
    fun _ _ h => (cancel_mono j.hom.hom).mp h
  obtain ⟨hweyl, hfac⟩ := generalLinearIntegralParabolics F N ν hν
  constructor
  · let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    let : Mono iL.hom.hom.left := hiL.isSplitSubtorus.mono
    intro w
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    let hcomp : iL ≫ j = i := Standard.leviTorusHom_comp i ν J
    let mapN := normalizerPointsMap iL j i hcomp
    obtain ⟨m, hmK, hmclass⟩ := hweyl (QuotientGroup.mk (mapN n))
    have hd : (m.val * (mapN n).val⁻¹) ∈ centralizerPoints i :=
      (QuotientGroup.eq_iff_div_mem.mp hmclass : m / mapN n ∈
        (centralizerPoints i).subgroupOf (normalizerPoints i))
    have hmL : m.val ∈ standardLeviPoints i ν J := by
      change m.val * (f n.val)⁻¹ ∈ centralizerPoints i at hd
      have hz := centralizerPoints_le_standardLeviPoints i ν J hd
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using mul_mem hz (hmap n.val)
    let mL := points.symm ⟨m.val, hmL⟩
    have hm : f mL = m.val := hpull ⟨m.val, hmL⟩
    have hrange : SubgroupFunctor.range (iL ≫ j) =
        SubgroupFunctor.range j ⊓ SubgroupFunctor.range i := by
      rw [hcomp]
      have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j := by
        rw [hrep.2]
        exact range_le_standardLevi i ν J
      apply SubgroupFunctor.ext
      intro U
      ext x
      exact ⟨fun hx => ⟨hle U hx, hx⟩, fun hx => hx.2⟩
    have hnL : mL ∈ normalizerPoints iL := by
      apply torusNormalizer_le_normalizerPoints iL
      apply SubgroupFunctor.mem_normalizer_of_range_comp_eq_inf iL j (SubgroupFunctor.range i) hrange
      change f mL ∈ (torusNormalizer i).carrier _
      rw [hm]
      exact normalizerPoints_le_torusNormalizer i m.property
    let mN : normalizerPoints iL := ⟨mL, hnL⟩
    refine ⟨mN, ?_, ?_⟩
    · change f mL ∈ K
      rwa [hm]
    · have he : mapN mN = m := Subtype.ext hm
      apply (isSplitTorus_splitTorus _).relativeWeylLatticeAction_injective iL
      rw [relativeWeylLatticeAction_mk, relativeWeylLatticeAction_mk,
        ← weylAction_normalizerPointsMap iL j i hcomp mN,
        ← weylAction_normalizerPointsMap iL j i hcomp n, he]
      exact congrArg (relativeWeylLatticeAction i) hmclass
  · intro Q hQ
    have hQJ : Q ⊆ J := hs ▸ hQ
    obtain ⟨hP, hM, hU⟩ := hfamily Q hQJ
    have hMQ : standardLeviPoints i ν Q ≤ standardLeviPoints i ν J := by
      have h := StandardLeviNested.standardLevi_le_range_leviHom hG i hi ν hν hJ hQJ
      rw [hrep.2] at h
      exact h _
    have hP' : standardParabolicPoints iL ν Q = (standardParabolicPoints i ν Q).comap f :=
      congrArg (fun H : SubgroupFunctor L => H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hP
    have hM' : standardLeviPoints iL ν Q = (standardLeviPoints i ν Q).comap f :=
      congrArg (fun H : SubgroupFunctor L => H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hM
    have hU' : standardUnipotentPoints iL ν Q = (standardUnipotentPoints i ν Q).comap f :=
      congrArg (fun H : SubgroupFunctor L => H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU
    apply Set.Subset.antisymm
    · rintro g ⟨hgK, hgP⟩
      rw [hP'] at hgP
      have hg : f g ∈ ((K ⊓ standardParabolicPoints i ν Q : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) :=
        ⟨hgK, hgP⟩
      rw [hfac Q (hQJ.trans hJ)] at hg
      obtain ⟨m, ⟨hmK, hmM⟩, u, ⟨huK, huU⟩, heq⟩ :=
        Set.mem_mul.mp hg
      have huL : u ∈ standardLeviPoints i ν J := by
        have hu : u = m⁻¹ * f g := by rw [← heq, inv_mul_cancel_left]
        rw [hu]
        exact mul_mem (inv_mem (hMQ hmM)) (hmap g)
      let m' := points.symm ⟨m, hMQ hmM⟩
      let u' := points.symm ⟨u, huL⟩
      have hm' : f m' = m := hpull ⟨m, hMQ hmM⟩
      have hu' : f u' = u := hpull ⟨u, huL⟩
      refine Set.mem_mul.mpr ⟨m', ?_, u', ?_, hinj ?_⟩
      · rw [hM']
        change f m' ∈ K ∧ f m' ∈ standardLeviPoints i ν Q
        rw [hm']
        exact ⟨hmK, hmM⟩
      · rw [hU']
        change f u' ∈ K ∧ f u' ∈ standardUnipotentPoints i ν Q
        rw [hu']
        exact ⟨huK, huU⟩
      · rw [map_mul, hm', hu']
        exact heq
    · rintro _ ⟨m, ⟨hmK, hmM⟩, u, ⟨huK, huU⟩, rfl⟩
      exact ⟨mul_mem hmK huK,
        mul_mem (standardLevi_le_standardParabolic iL ν Q _ hmM)
          (standardUnipotent_le_standardParabolic iL ν Q _ huU)⟩

end Langlands.BruhatTits.SpecialCompact
