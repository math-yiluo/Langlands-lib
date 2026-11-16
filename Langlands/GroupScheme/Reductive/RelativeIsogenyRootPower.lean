import Langlands.GroupScheme.Reductive.RelativeIsogenyRootRestriction
import Langlands.GroupScheme.Reductive.NaturalPowerRigidity

/-! # Prescribed powers of actual root restrictions over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]

/-- A coefficient power formula determines the value on every scheme test. -/
theorem rootPoint_eq_of_scalarOperation {f : Ga R ⟶ Ga R} {c : R} {q : ℕ}
    (hf : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation f).app A a = algebraMap R A c * a ^ q)
    (Z : Over (Spec (CommRingCat.of R))) (a : Γ(Z.left, ⊤)) :
    rootPoint f Z a = VectorGroup.scalarPoint _ Z (baseScalar Z c * a ^ q) := by
  let A : CommAlgCat.{u} (CommRingCat.of R) :=
    CommAlgCat.of R (MvPolynomial (Fin 1) R)
  let x := (Scheme.ΓSpecIso (CommRingCat.of A)).hom (gaCoord (𝟙 (Ga R).X))
  have h := hf A x
  have hx : VectorGroup.scalarPoint (CommRingCat.of R) (Ga R).X
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x) = 𝟙 (Ga R).X := by
    rw [show (Scheme.ΓSpecIso (CommRingCat.of A)).inv x = gaCoord (𝟙 (Ga R).X)
      from Iso.hom_inv_id_apply _ _]
    exact VectorGroup.scalarPoint_coordinate _ _
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) (Ga R).X
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x) ≫ f.hom.hom)) = _ at h
  rw [hx, Category.id_comp] at h
  have huniv : gaCoord f.hom.hom =
      baseScalar (Ga R).X c * gaCoord (𝟙 (Ga R).X) ^ q := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom _ =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom _
    have hc := gamma_baseScalar A c
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (baseScalar (Ga R).X c) =
      algebraMap R A c at hc
    rw [map_mul, map_pow, hc]
    exact h
  apply VectorGroup.points_ext
  intro b
  rw [Subsingleton.elim b 0, VectorGroup.coordinates_scalarPoint]
  change gaCoord (VectorGroup.scalarPoint (CommRingCat.of R) Z a ≫ f.hom.hom) = _
  rw [gaCoord, VectorGroup.coordinates_comp]
  change (VectorGroup.scalarPoint (CommRingCat.of R) Z a).left.appTop
    (gaCoord f.hom.hom) = _
  rw [huniv, map_mul, map_pow, appTop_baseScalar]
  have hxcoord := congrFun (VectorGroup.coordinates_comp
    (VectorGroup.scalarPoint (CommRingCat.of R) Z a) (𝟙 (Ga R).X)) 0
  simpa only [Category.comp_id, VectorGroup.coordinates_scalarPoint] using
    congrArg (fun z => baseScalar Z c * z ^ q) hxcoord.symm

variable {I I' : Type u} [Fintype I] [Fintype I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {m : I → ℤ} {m' : I' → ℤ} {u : Ga R ⟶ G} {v : Ga R ⟶ H}

/-- A monic root restriction inherits the prescribed torus weight ratio. -/
theorem IsRootParametrization.restriction_powerWeight
    (hu : IsRootParametrization i m u) (hv : IsRootParametrization j m' v)
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (phi : G ⟶ H) (hsq : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
    (f : Ga R ⟶ Ga R) (hf : f ≫ v = u ≫ phi)
    (q : ℕ) (hweight : tau ≫ splitTorus.exponentCharacter _ I' m' =
      q • splitTorus.exponentCharacter _ I m)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (a : Γ(Z.left, ⊤)) :
    rootPoint f Z (VectorGroup.charValue (splitTorus.exponentCharacter _ I m) Z t * a) =
      VectorGroup.scalarPoint _ Z
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I m) Z t ^ q *
          gaCoord (rootPoint f Z a)) := by
  have hpoint (b : Γ(Z.left, ⊤)) :
      rootPoint f Z b ≫ v.hom.hom = rootPoint u Z b ≫ phi.hom.hom := by
    rw [rootPoint, rootPoint, Category.assoc, ← Grp.comp_hom_hom, hf,
      Grp.comp_hom_hom, Category.assoc]
  have ht : (t ≫ i.hom.hom) ≫ phi.hom.hom =
      (t ≫ tau.hom.hom) ≫ j.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hsq, Grp.comp_hom_hom, Category.assoc]
    rfl
  have hchar : VectorGroup.charValue (splitTorus.exponentCharacter _ I' m') Z
      (t ≫ tau.hom.hom) =
      VectorGroup.charValue (splitTorus.exponentCharacter _ I m) Z t ^ q := by
    change VectorGroup.charValue (tau ≫ splitTorus.exponentCharacter _ I' m') Z t = _
    have heval := comp_groupHom_zsmul
      (G := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t (q : ℤ)
      (splitTorus.exponentCharacter _ I m)
    rw [Nat.cast_smul_eq_nsmul ℤ] at heval
    rw [hweight, VectorGroup.charValue, VectorGroup.charValue, heval, map_zpow,
      zpow_natCast, Units.val_pow_eq_pow_val]
  have hcoord : rootPoint v Z (gaCoord (rootPoint f Z a)) =
      rootPoint u Z a ≫ phi.hom.hom := by
    rw [rootPoint, VectorGroup.scalarPoint_coordinate]
    exact hpoint a
  let : Mono v.hom.hom := hv.represents.1
  apply (cancel_mono v.hom.hom).mp
  change rootPoint f Z _ ≫ v.hom.hom = rootPoint v Z _
  rw [hpoint, ← hu.equivariant, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    ht, ← hchar, ← hv.equivariant, hcoord]

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
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
  apply hasLaurentPower_of_weight (P.root (r.indexEquiv b)) (P.coroot (r.indexEquiv b))
  · rw [← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
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

end Langlands.GroupScheme.RelativeIsogeny
