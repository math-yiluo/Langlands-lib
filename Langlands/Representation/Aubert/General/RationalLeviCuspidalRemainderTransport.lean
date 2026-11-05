import Langlands.Representation.Aubert.General.CuspidalRemainderTransport
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Aubert.General.RationalLeviCuspidalEmbedding

/-! # Actual cuspidal remainder splittings on a standard rational Levi -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace Langlands.Aubert.General

universe uG uV uK uK'

section Splitting

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {κ : Type uK} {P M U : κ → Subgroup G}
  {h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k)}
  {hU : ∀ k, IsClosed (U k : Set G)}

/-- Change the actual vertex and both coproduct legs through an isomorphism. -/
theorem HasCuspidalRemainderSplitting.of_iso
    {A B : SmoothRep.{0, uG, uV} ℂ G}
    (hsplit : HasCuspidalRemainderSplitting P M U h hU A) (e : A ≅ B) :
    HasCuspidalRemainderSplitting P M U h hU B := by
  obtain ⟨Y, j, hC, hR, ⟨hc⟩⟩ := hsplit
  exact ⟨Y, (fun b => j b ≫ e.hom), hC, hR,
    ⟨IsColimit.ofIsoColimit hc (Cofan.ext e fun _ => rfl)⟩⟩

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {κ' : Type uK'} {P' M' U' : κ' → Subgroup H}
  {h' : ∀ k, IsSemidirectDecomposition (P' k) (M' k) (U' k)}
  {hU' : ∀ k, IsClosed (U' k : Set H)}

/-- An exact all-object cuspidality comparison both preserves and reflects
the supplied actual coproduct splitting. -/
theorem hasCuspidalRemainderSplitting_pullback_iff
    (e : H ≃ₜ* G)
    (hcusp : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      IsCuspidalFor P' M' U' h' hU' (SmoothRep.pullback e A) ↔
        IsCuspidalFor P M U h hU A)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    HasCuspidalRemainderSplitting P' M' U' h' hU' (SmoothRep.pullback e A) ↔
      HasCuspidalRemainderSplitting P M U h hU A := by
  constructor
  · intro hsplit
    have hcusp' (B : SmoothRep.{0, uG, uV} ℂ H) :
        IsCuspidalFor P M U h hU (SmoothRep.pullback e.symm B) ↔
          IsCuspidalFor P' M' U' h' hU' B := by
      let c := (SmoothRep.pullbackEquivalence e).counitIso.app B
      exact ⟨fun hB => ((hcusp _).mpr hB).of_iso c.symm,
        fun hB => (hcusp _).mp (hB.of_iso c)⟩
    exact (hsplit.pullback e.symm hcusp').of_iso
      ((SmoothRep.pullbackEquivalence e).unitIso.app A).symm
  · exact fun hsplit => hsplit.pullback e hcusp

end Splitting

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] {ι : Type uK}

/-- The local splitting condition for the exact proper standard tests inside
the literal closed Levi. This definition asserts no splitting existence. -/
def HasLeviCuspidalRemainderSplitting
    (P M U : Finset ι → Subgroup G) (hU : ∀ I, IsClosed (U I : Set G))
    (I : Finset ι) (hMI : IsClosed (M I : Set G))
    (hInner : ∀ K : Finset I,
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I)))
    (A : SmoothRep.{0, uG, uV} ℂ (M I)) : Prop :=
  letI := hMI.locallyCompactSpace
  HasStandardCuspidalRemainderSplitting
    (fun K : Finset I => (P (leviIndex I K)).subgroupOf (M I))
    (fun K => (M (leviIndex I K)).subgroupOf (M I))
    (fun K => (U (leviIndex I K)).subgroupOf (M I)) hInner
    (fun K => (hU (leviIndex I K)).preimage continuous_subtype_val) A

end Levi

namespace RationalPointFamily

universe u v

open _root_.AlgebraicGeometry GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hDynamic : DynamicLieStatement.{u}) (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (I : Finset (SimpleRoot i ν))
  (hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsClosedImmersion
    (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance : IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance : TopologicalSpace (rationalPoints G) := pointTopology
local instance : TopologicalSpace
    (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [Fintype (SimpleRoot (standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)]
  (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))
  (hUL : ∀ J, IsClosed (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J :
      Set (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))))
  (hMI : IsClosed (levi i ν I : Set (rationalPoints G)))
  (hInner : ∀ K : Finset I,
    IsSemidirectDecomposition ((parabolic i ν (leviIndex I K)).subgroupOf (levi i ν I))
      ((levi i ν (leviIndex I K)).subgroupOf (levi i ν I))
      ((unipotent i ν (leviIndex I K)).subgroupOf (levi i ν I)))
  (hOwn : ∀ K, IsSemidirectDecomposition
    (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν K)
    (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν K)
    (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν K))

include hDynamic hStandard hG hi hν hL

/-- The canonical point homeomorphism identifies the two actual splitting
conditions, including exclusion of all nonzero cuspidal subquotients. -/
theorem hasLeviCuspidalRemainderSplitting_iff_pullback
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) :
    HasLeviCuspidalRemainderSplitting (parabolic i ν) (levi i ν) (unipotent i ν)
        hU I hMI hInner A ↔
      HasStandardCuspidalRemainderSplitting
        (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)
        (levi (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)
        (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν) hOwn hUL
        (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) A) := by
  let := hMI.locallyCompactSpace
  exact (hasCuspidalRemainderSplitting_pullback_iff
    (leviRationalPointHomeomorph i ν I)
    (fun B => rationalLeviCuspidalityTransport hDynamic hStandard
      k G hG T i hi ν hν I hL hU hUL hMI hInner hOwn B) A).symm

/-- The intrinsic whole-category coproduct condition supplies the literal
inside-Levi splitting, without assuming an induction comparison. -/
theorem hasLeviCuspidalRemainderSplitting_of_rationalWholeCoproduct
    (hwhole : Renard.EveryObjectIsCoproductOfComponents
      (CuspidalSupport.rationalWholeCuspidalDecompositionProperties.{u, v}
        (Standard.leviScheme i ν (rootSet i ν I))
        (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL))
    (A : SmoothRep.{0, u, v} ℂ (levi i ν I)) :
    HasLeviCuspidalRemainderSplitting (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I hMI hInner A := by
  apply (hasLeviCuspidalRemainderSplitting_iff_pullback
    i ν hDynamic hStandard hG hi hν I hL hU hUL hMI hInner hOwn A).mpr
  exact CuspidalSupport.hasStandardCuspidalRemainderSplitting_of_rationalWholeCoproduct
    (Standard.leviScheme i ν (rootSet i ν I))
    (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL hwhole _

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- Proper induction in the literal standard Levi excludes every nonzero
cuspidal actual subquotient, conditional on its intrinsic whole coproduct.
The actual standard unipotent subgroup supplies unimodularity. -/
theorem no_leviCuspidal_subquotient_of_proper_induction_rationalWholeCoproduct
    (hM : ∀ J, IsClosed (levi i ν J : Set (rationalPoints G)))
    (hwhole : Renard.EveryObjectIsCoproductOfComponents
      (CuspidalSupport.rationalWholeCuspidalDecompositionProperties.{u, max u v}
        (Standard.leviScheme i ν (rootSet i ν I))
        (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL)) :
    letI := hMI.locallyCompactSpace
    ∀ (K : Finset I) (_hK : K ≠ Finset.univ)
    (σ : SmoothRep.{0, u, v} ℂ
      ((levi i ν (leviIndex I K)).subgroupOf (levi i ν I)))
    (D : SmoothRep.{0, u, max u v} ℂ (levi i ν I)) (_hD : Nontrivial D)
    (_hDA : SmoothRep.IsSubquotient D
      ((normalizedInductionFunctor (hInner K)
        ((hU (leviIndex I K)).preimage continuous_subtype_val)).obj σ)),
    ¬ IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I hMI hInner D := by
  let := hMI.locallyCompactSpace
  intro K hK σ D hD hDA
  have hsplit := hasLeviCuspidalRemainderSplitting_of_rationalWholeCoproduct
    i ν hDynamic hStandard hG hi hν I hL hU hUL hMI hInner hOwn hwhole
    ((normalizedInductionFunctor (hInner K)
      ((hU (leviIndex I K)).preimage continuous_subtype_val)).obj σ)
  exact no_leviCuspidal_subquotient_of_proper_induction_splitting
    (parabolic i ν) (levi i ν) (unipotent i ν) hU I hMI hInner K hK
    (isUnimodularModulus_standardUnipotent_in_levi i ν hG hi hν hStandard hU hM I K)
    σ hsplit D hD hDA

end RationalPointFamily
end Langlands.Aubert.General
