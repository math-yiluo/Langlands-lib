import Langlands.GroupScheme.Reductive.RelativeIsogenyConjugationRigidity
import Langlands.GroupScheme.Reductive.RelativeIsogenyRootAlignment
import Langlands.GroupScheme.Reductive.NormalizedLocalRootFamily
import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityDescent
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # Local torus conjugacy with a supplied common root-datum map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.GroupScheme

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  [Finite J] [Finite J']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]

/-- Two actual homomorphisms have the same supplied root-datum isogeny and
coordinate torus map, including its integral character formula. -/
def HasCommonRootDatumTorusMap
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) [P.IsReduced] [Q.IsReduced]
    (phi Phi : G ⟶ H) : Prop :=
  ∃ (p : ℕ) (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I'),
    (∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m)) ∧
    i ≫ phi = CommGroupScheme.groupHom tau ≫ j ∧
    i ≫ Phi = CommGroupScheme.groupHom tau ≫ j

namespace RelativeIsogeny

omit [DecidableEq I] [DecidableEq I'] in
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

variable [IsLocalRing R] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
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
  [hfinphi : IsFinite phi.hom.hom.left] [hfinPhi : IsFinite Phi.hom.hom.left]
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
  (hG : IsReductive G) (hH : IsReductive H)
  (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
  (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)

include hP hQ hweight hphi hPhi hG hH hi hj hmaxG hmaxH

/-- Finite maps with a common compatible root-datum map admit an actual torus
conjugator after an fppf change of every parameter scheme over a local base. -/
theorem exists_fppf_torusConjugates (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      TorusConjugates (T := splitTorus.commGroupScheme _ I') j phi Phi t := by
  classical
  let b := Langlands.LinearAlgebra.RootDatumBase.base P
  obtain ⟨u, hu, hw⟩ := exists_normalizedLocalRootFamily hG i hi hmaxG hP b
  choose v hv using fun a : J' =>
    LocalRootGroup.exists_rootParametrization_of_flat j hH hmaxH hQ a
  have hind := linearIndependent_preimage_simpleRoots r b
  obtain ⟨W, q, t, hflat, hsurj, hlfp, he⟩ :=
    exists_fppf_selected_root_alignment i j hP hQ r tau hweight phi Phi
      hphi hPhi hH hmaxH (fun a : b.support => r.indexEquiv.symm a) hind
      (fun a : b.support => u a) (fun a : b.support => v (r.indexEquiv.symm a))
      (fun a => by simpa only [Equiv.apply_symm_apply] using hu a)
      (fun a => hv (r.indexEquiv.symm a)) V
  refine ⟨W, q, t, hflat, hsurj, hlfp, ?_⟩
  apply TorusConjugates.of_simpleRootRestrictions i j hP hQ r tau hweight
    phi Phi hphi hPhi hG hH hi hj hmaxG hmaxH b u v
    (fun a _ => ⟨hu a, hu (P.reflectionPerm a a)⟩)
    (fun a _ => ⟨hv (r.indexEquiv.symm a),
      hv (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a))⟩) hw t
  intro a ha Z d x
  exact he Z d ⟨a, ha⟩ x

/-- The local conjugating point gives a singleton fppf cover of the base. -/
theorem fppfLocallyTorusConjugate_of_supplied_rootDatum :
    FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j phi Phi := by
  obtain ⟨W, q, t, hflat, hsurj, hlfp, ht⟩ :=
    exists_fppf_torusConjugates i j hP hQ r tau hweight phi Phi hphi hPhi
      hG hH hi hj hmaxG hmaxH (𝟙_ (Over (Spec (CommRingCat.of R))))
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
/-- The existential package of compatible root data suffices for local torus
conjugacy of the two actual finite homomorphisms. -/
theorem fppfLocallyTorusConjugate_of_commonRootDatumTorusMap
    (hcommon : HasCommonRootDatumTorusMap i j P Q phi Phi) :
    FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j phi Phi := by
  obtain ⟨p, r, tau, hweight, hphi, hPhi⟩ := hcommon
  exact fppfLocallyTorusConjugate_of_supplied_rootDatum i j hP hQ r tau hweight
    phi Phi hphi hPhi hG hH hi hj hmaxG hmaxH

end RelativeIsogeny

end Langlands.GroupScheme
