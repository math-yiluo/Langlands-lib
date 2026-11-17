import Langlands.GroupScheme.Reductive.LocalSuppliedRootIsogenyConjugacy
import Langlands.GroupScheme.Reductive.AffineSplitSurjectionRootDatumStatement
import Langlands.GroupScheme.Reductive.LocalSplitRootWeightFreeness

/-! # Local adapter from intrinsic root-datum compatibility -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I']
  [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]

/-- The actual character map of a supplied coordinate-torus homomorphism is
the weight map of some isogeny between the supplied root data. -/
def HasRootDatumTorusCharacterMap
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) [P.IsReduced] [Q.IsReduced] : Prop :=
  ∃ (p : ℕ) (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
    ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m)

namespace splitTorus

/-- A monomial identity on all scheme tests is an equality of actual
coordinate-torus characters. -/
theorem exponentCharacter_comp_eq_of_points
    (tau : commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      commGroupScheme (Spec (CommRingCat.of R)) I')
    (m : I' → ℤ) (n : I → ℤ)
    (h : ∀ (U : Over (Spec (CommRingCat.of R)))
      (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X),
      ∏ j', pointsEquiv I' U (x ≫ (CommGroupScheme.groupHom tau).hom.hom) j' ^ m j' =
        ∏ j, pointsEquiv I U x j ^ n j) :
    tau ≫ exponentCharacter _ I' m = exponentCharacter _ I n := by
  change CommGroupScheme.groupHom (tau ≫ exponentCharacter _ I' m) =
    CommGroupScheme.groupHom (exponentCharacter _ I n)
  apply hom_ext_points
  intro U x
  apply (Gm.pointsEquiv _ U).injective
  change Gm.pointsEquiv _ U ((x ≫ (CommGroupScheme.groupHom tau).hom.hom) ≫
      (CommGroupScheme.groupHom (exponentCharacter _ I' m)).hom.hom) =
    Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom (exponentCharacter _ I n)).hom.hom)
  rw [pointsEquiv_exponentCharacter, pointsEquiv_exponentCharacter]
  exact h U x

end splitTorus

variable [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hQ : IsFibrewiseRootDatumOf I' H j Q)
  (hG : IsReductive G) (hH : IsReductive H)
  (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
  (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (phi : G ⟶ H) [IsFinite phi.hom.hom.left]
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)

include hP hQ hG hH hi hj hmaxG hmaxH hphi

/-- The intrinsic split-surjection proposition supplies the actual common
character map over a local ring. The proposition remains an explicit premise. -/
theorem hasRootDatumTorusCharacterMap_of_affineSplitSurjectionRootDatum
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u})
    (hsurj : Surjective phi.hom.hom.left) :
    HasRootDatumTorusCharacterMap tau P Q := by
  classical
  have hfreeP := localRootWeightSpace_nonempty_linearEquiv G hG I i hmaxG P hP
  have hfreeQ := localRootWeightSpace_nonempty_linearEquiv H hH I' j hmaxH Q hQ
  have h := hAffine R G H hG hH I I' i j J J' P Q hi hmaxG hP hfreeP
    hj hmaxH hQ hfreeQ phi (CommGroupScheme.groupHom tau) inferInstance hsurj hphi
  obtain ⟨V, hs, p, r, _, hpoints⟩ := h.1 (IsLocalRing.closedPoint R)
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).mp hs
  refine ⟨p, r, fun m => ?_⟩
  apply splitTorus.exponentCharacter_comp_eq_of_points tau m (r.weightMap m)
  intro U x
  exact hpoints U (by simp only [hV, Scheme.Hom.preimage_top]) x m

/-- If both maps have the same torus square, compatible root data for the
first map give the package needed for the conjugator construction. -/
theorem hasCommonRootDatumTorusMap_of_affineSplitSurjectionRootDatum
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u})
    (hsurj : Surjective phi.hom.hom.left) (Phi : G ⟶ H)
    (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j) :
    HasCommonRootDatumTorusMap i j P Q phi Phi := by
  obtain ⟨p, r, hweight⟩ :=
    hasRootDatumTorusCharacterMap_of_affineSplitSurjectionRootDatum i j hP hQ
      hG hH hi hj hmaxG hmaxH tau phi hphi hAffine hsurj
  exact ⟨p, r, tau, hweight, hphi, hPhi⟩

/-- The intrinsic split-surjection proposition implies actual local torus
conjugacy for two finite maps with a common torus restriction. -/
theorem RelativeIsogeny.fppfLocallyTorusConjugate_of_affineSplitSurjectionRootDatum
    [DecidableEq I] [DecidableEq I']
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u})
    (hsurj : Surjective phi.hom.hom.left) (Phi : G ⟶ H)
    [IsFinite Phi.hom.hom.left]
    (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j) :
    FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j phi Phi := by
  exact fppfLocallyTorusConjugate_of_commonRootDatumTorusMap i j hP hQ phi Phi
    hG hH hi hj hmaxG hmaxH
    (hasCommonRootDatumTorusMap_of_affineSplitSurjectionRootDatum i j hP hQ
      hG hH hi hj hmaxG hmaxH tau phi hphi hAffine hsurj Phi hPhi)

end Langlands.GroupScheme
