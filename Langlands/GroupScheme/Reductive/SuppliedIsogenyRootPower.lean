import Langlands.GroupScheme.Reductive.SuppliedIsogenyRootRestriction
import Langlands.GroupScheme.Reductive.RelativeIsogenyRootPower

/-! # Prescribed powers of supplied root restrictions over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.SuppliedRootIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' : Type u} [Fintype I] [Fintype I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi : G ⟶ H) (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (b : J')
  {u : Ga R ⟶ G} {v : Ga R ⟶ H}
  (hu : IsRootParametrization i (P.root (r.indexEquiv b)) u)
  (hv : IsRootParametrization j (Q.root b) v)

/-- The base coefficient of the actual additive root restriction. -/
def rootRestrictionCoefficient : R :=
  (scalarOperation
    (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)).app
      (CommAlgCat.of R R) 1

/-- The actual root restriction has precisely the root-datum factor as its power. -/
theorem rootRestriction_hasLaurentPower :
    (scalarOperation (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)).HasLaurentPower 2 (r.rootFactor b) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    unfold NaturalLine.Operation.HasLaurentPower
    exact Subsingleton.elim _ _
  · let := hR
    apply hasLaurentPower_of_weight (P.root (r.indexEquiv b)) (P.coroot (r.indexEquiv b))
    · rw [← hP.pairing_of_nontrivial, P.root_coroot_two]
      rfl
    · apply hu.restriction_powerWeight hv tau phi hphi _
        (rootRestriction_comp i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)
      rw [hweight, r.root_weightMap, ← Nat.cast_smul_eq_nsmul ℤ]
      simp only [splitTorus.exponentCharacter, Pi.smul_apply, smul_eq_mul, mul_smul,
        Finset.smul_sum]
/-- One base coefficient gives the root restriction on every coefficient algebra. -/
theorem rootRestriction_power (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A) :
    (scalarOperation (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)).app A a =
      algebraMap R A (rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) * a ^ r.rootFactor b :=
  NaturalLine.Operation.eq_mul_pow_of_laurent two_pos _
    (rootRestriction_hasLaurentPower i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) A a

/-- The coefficient formula computes the ambient restriction on every scheme test. -/
theorem rootRestriction_power_rootPoint (Z : Over (Spec (CommRingCat.of R)))
    (a : Γ(Z.left, ⊤)) :
    rootPoint u Z a ≫ phi.hom.hom =
      rootPoint v Z (baseScalar Z (rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) * a ^ r.rootFactor b) := by
  have h := rootPoint_eq_of_scalarOperation
    (rootRestriction_power i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) Z a
  have hc := congrArg (fun f : Ga R ⟶ H => VectorGroup.scalarPoint (CommRingCat.of R) Z a ≫
    f.hom.hom) (rootRestriction_comp i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)
  have hc' : rootPoint
      (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) Z a ≫
      v.hom.hom = rootPoint u Z a ≫ phi.hom.hom := by
    simpa only [Grp.comp_hom_hom, ← Category.assoc, rootPoint] using hc
  rw [h] at hc'
  exact hc'.symm

end Langlands.GroupScheme.SuppliedRootIsogeny
