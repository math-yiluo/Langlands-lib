import Langlands.GroupScheme.Reductive.CorootTorusQuotient
import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Torus.KernelDiagonalizable

/-! # Projection of a split maximal torus onto the coroot quotient -/

noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeDerived

variable {I J : Type u} [Fintype I] [DecidableEq I]
  (R : CommRingCat.{u}) (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Restrict characters of the coordinate torus to the coroot-annihilator lattice. -/
def corootProjection : splitTorus (Spec R) I ⟶ (corootQuotient R P).toGrp :=
  (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv ≫
    Diagonalizable.restrictMap R (cocenterLattice P).subtype.toAddMonoidHom

/-- Projection evaluates an annihilating character by its coordinate monomial,
on every test scheme over the coefficient ring. -/
theorem corootProjection_points (T : Over (Spec R))
    (t : T ⟶ (splitTorus (Spec R) I).X) (m : cocenterLattice P) :
    Diagonalizable.characterPointsEquiv R (cocenterLattice P) T
        (t ≫ (corootProjection R P).hom.hom) (.ofAdd m) =
      ∏ i, splitTorus.pointsEquiv I T t i ^ m.val i := by
  let b := AddEquiv.refl (I → ℤ)
  have ht : Diagonalizable.splitPointsEquiv R b T
      (t ≫ (Diagonalizable.splitIso R b).inv.hom.hom) =
        splitTorus.pointsEquiv I T t :=
    isoOfPointModels_inv (fun T : Over (Spec R) => I → (Γ(T.left, ⊤))ˣ)
      (fun a => splitTorus.unitsRestrict I a)
      (Diagonalizable.splitPointsEquiv R b) (splitTorus.pointsEquiv I)
      (fun a x => Diagonalizable.splitPointsEquiv_naturality R b a x)
      (fun a y => splitTorus.pointsEquiv_naturality I a y) T t
  change Diagonalizable.characterPointsEquiv R (cocenterLattice P) T
    ((t ≫ (Diagonalizable.splitIso R b).inv.hom.hom) ≫
      (Diagonalizable.restrictMap R (cocenterLattice P).subtype.toAddMonoidHom).hom.hom)
      (.ofAdd m) = _
  erw [Diagonalizable.pointsEquiv_restrictMap]
  change _ = (Diagonalizable.charEquiv b (Γ(T.left, ⊤))ˣ).symm
    (splitTorus.pointsEquiv I T t) (.ofAdd m.val)
  rw [← ht]
  exact congrArg (fun χ : Multiplicative (I → ℤ) →* (Γ(T.left, ⊤))ˣ => χ (.ofAdd m.val))
    ((Diagonalizable.charEquiv b (Γ(T.left, ⊤))ˣ).symm_apply_apply _).symm

/-- Every coordinate coroot is killed on all test schemes when the datum's
pairing is the coordinate integer dot product. -/
theorem corootProjection_coroot_points
    (hP : ∀ m n : I → ℤ, P.toLinearMap m n = ∑ i, m i * n i)
    (a : J) (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X) :
    (x ≫ (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec R) I (P.coroot a))).hom.hom) ≫
        (corootProjection R P).hom.hom = 1 := by
  apply (Diagonalizable.characterPointsEquiv R (cocenterLattice P) T).injective
  rw [map_one]
  apply MonoidHom.ext
  intro m
  change Diagonalizable.characterPointsEquiv R (cocenterLattice P) T _ (.ofAdd m.toAdd) = 1
  rw [corootProjection_points, splitTorus.pointsEquiv_exponentCocharacter]
  simp_rw [← zpow_mul]
  have hz : (∑ i, P.coroot a i * m.toAdd.val i) = 0 := by
    have hm := (Langlands.RootDatum.mem_corootAnnihilator P Set.univ m.toAdd.val).mp
      m.toAdd.property a (Set.mem_univ a)
    simpa only [hP, mul_comm] using hm
  have hpow (s : Finset I) :
      (∏ i ∈ s, Gm.pointsEquiv (Spec R) T x ^ (P.coroot a i * m.toAdd.val i)) =
        Gm.pointsEquiv (Spec R) T x ^ (∑ i ∈ s, P.coroot a i * m.toAdd.val i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]
  rw [hpow, hz, zpow_zero]

/-- Scheme-theoretically, the projection kills each actual coroot homomorphism. -/
theorem coroot_comp_corootProjection
    (hP : ∀ m n : I → ℤ, P.toLinearMap m n = ∑ i, m i * n i) (a : J) :
    CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec R) I (P.coroot a)) ≫
      corootProjection R P = 1 := by
  apply hom_ext_points
  intro T x
  change (x ≫ (CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec R) I (P.coroot a))).hom.hom) ≫
      (corootProjection R P).hom.hom = x ≫ (1 : (Gm (Spec R)).toGrp ⟶ _).hom.hom
  rw [corootProjection_coroot_points R P hP]
  simp

end Langlands.GroupScheme.RelativeDerived
