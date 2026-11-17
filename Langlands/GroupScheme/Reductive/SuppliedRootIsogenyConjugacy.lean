import Langlands.GroupScheme.Reductive.SuppliedIsogenyRootAlignment
import Langlands.GroupScheme.Reductive.SimpleRootLocalTestRigidity
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Reductive.LocalSuppliedRootIsogenyConjugacy

/-! # Supplied-root torus conjugacy over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.GroupScheme.SuppliedRootIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]

private theorem linearIndependent_preimage_simpleRoots
    {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) (b : P.Base) :
    LinearIndependent ℤ (fun a : b.support => Q.root (r.indexEquiv.symm a)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hm := congrArg r.weightMap hc
  simp only [map_sum, map_smul, r.root_weightMap, Equiv.apply_symm_apply,
    map_zero, smul_smul] at hm
  have hz := Fintype.linearIndependent_iff.mp b.linearIndepOn_root.linearIndependent
    (fun a : b.support => c a * (r.rootFactor (r.indexEquiv.symm a) : ℤ)) hm a
  exact (mul_eq_zero.mp hz).resolve_right
    (by exact_mod_cast (r.rootFactor_pos (r.indexEquiv.symm a)).ne')

/-- An actual fppf change of a parameter scheme and a target torus point
conjugating the two ambient homomorphisms on every refined scheme test. -/
structure TorusConjugacyLift
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) (phi Phi : G ⟶ H)
    (V : Over (Spec (CommRingCat.of R))) where
  cover : Over (Spec (CommRingCat.of R))
  projection : cover ⟶ V
  lift : cover ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X
  flat : Flat projection.left
  surjective : Surjective projection.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection.left
  conjugates : TorusConjugates (T := splitTorus.commGroupScheme _ I') j phi Phi lift

variable
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi Phi : G ⟶ H)
  [IsFinite phi.hom.hom.left] [IsFinite Phi.hom.hom.left]
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)

variable (hG : IsReductive G) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
  (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)

include hP hQ hweight hphi hPhi hG hH hi hj hmaxG hmaxH

/-- Free actual root weights supply global root coordinates and hence an
fppf local whole-group torus conjugator over any commutative ring. -/
theorem exists_fppf_torusConjugates
    (hfreeP : ∀ a : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hfreeQ : ∀ a : J', Nonempty
      (splitTorus.exponentWeightSpace I' H j (Q.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      TorusConjugates (T := splitTorus.commGroupScheme _ I') j phi Phi t := by
  classical
  let b := Langlands.LinearAlgebra.RootDatumBase.base P
  let u := LocalRootGroup.rootParametrizationsOfFreeWeights i hG hmaxG hP hfreeP
  let v := LocalRootGroup.rootParametrizationsOfFreeWeights j hH hmaxH hQ hfreeQ
  have hu := LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
    i hG hmaxG hP hfreeP
  have hv := LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
    j hH hmaxH hQ hfreeQ
  obtain ⟨W, q, t, hflat, hsurj, hlfp, he⟩ :=
    exists_fppf_selected_root_alignment i j hP hQ r tau hweight phi Phi
      hphi hPhi hH hmaxH (fun a : b.support => r.indexEquiv.symm a)
      (linearIndependent_preimage_simpleRoots r b)
      (fun a : b.support => u a) (fun a : b.support => v (r.indexEquiv.symm a))
      (fun a => by simpa only [Equiv.apply_symm_apply] using hu a)
      (fun a => hv (r.indexEquiv.symm a)) V
  refine ⟨W, q, t, hflat, hsurj, hlfp, ?_⟩
  apply TorusConjugates.of_simpleRootParametrizations i j hP hQ r tau hweight
    phi Phi hphi hPhi hG hH hi hj hmaxG hmaxH b u (fun a _ => hu a) t
  intro a ha Z d x
  exact he Z d ⟨a, ha⟩ x

/-- A chosen fppf cover and whole-group torus conjugator from free actual
root weights and the supplied common root-datum map. -/
def suppliedRootConjugacyLift
    (hfreeP : ∀ a : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hfreeQ : ∀ a : J', Nonempty
      (splitTorus.exponentWeightSpace I' H j (Q.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (V : Over (Spec (CommRingCat.of R))) : TorusConjugacyLift j phi Phi V :=
  Classical.choice (show Nonempty (TorusConjugacyLift j phi Phi V) from by
    obtain ⟨W, q, t, hflat, hsurj, hlfp, ht⟩ :=
      exists_fppf_torusConjugates i j hP hQ r tau hweight phi Phi hphi hPhi
        hH hmaxH hG hi hj hmaxG hfreeP hfreeQ V
    exact ⟨⟨W, q, t, hflat, hsurj, hlfp, ht⟩⟩)

/-- A conjugator over the terminal test gives a singleton fppf cover of the
base with the all-test conjugation identity. -/
theorem fppfLocallyTorusConjugate_of_supplied_rootDatum
    (hfreeP : ∀ a : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hfreeQ : ∀ a : J', Nonempty
      (splitTorus.exponentWeightSpace I' H j (Q.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) :
    FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j phi Phi := by
  obtain ⟨W, q, t, hflat, hsurj, hlfp, ht⟩ :=
    exists_fppf_torusConjugates i j hP hQ r tau hweight phi Phi hphi hPhi
      hH hmaxH hG hi hj hmaxG hfreeP hfreeQ (𝟙_ (Over (Spec (CommRingCat.of R))))
  let U : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (CommRingCat.of R)) :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => W.left) (fun _ => q.left)
      (fun s => by obtain ⟨w, hw⟩ := hsurj.surj s; exact ⟨PUnit.unit, w, hw⟩)
      (fun _ => ⟨hflat, hlfp⟩)
  refine ⟨U, fun _ => ?_⟩
  have hq : q.left = W.hom := by simpa using Over.w q
  let e : Over.mk q.left ⟶ W :=
    Over.homMk (𝟙 W.left) (by simpa using hq.symm)
  exact ⟨e ≫ t, ht.comp e⟩

omit hweight hphi hPhi in
/-- The existential package of common actual root-datum and torus maps
suffices when the actual root weight spaces are free over the base ring. -/
theorem fppfLocallyTorusConjugate_of_commonRootDatumTorusMap
    (hfreeP : ∀ a : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hfreeQ : ∀ a : J', Nonempty
      (splitTorus.exponentWeightSpace I' H j (Q.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hcommon : HasCommonRootDatumTorusMap i j P Q phi Phi) :
    FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j phi Phi := by
  obtain ⟨p, r, tau, hweight, hphi, hPhi⟩ := hcommon
  exact fppfLocallyTorusConjugate_of_supplied_rootDatum i j hP hQ r tau hweight
    phi Phi hphi hPhi hH hmaxH hG hi hj hmaxG hfreeP hfreeQ

end Langlands.GroupScheme.SuppliedRootIsogeny
