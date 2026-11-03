import Langlands.GroupScheme.Rational.VectorLinearAction
import Langlands.GroupScheme.Rational.TorusActionPoints
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Scalar linearity of vector actions in characteristic zero -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

private theorem polynomial_eq_linear_of_doubling
    {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    (p : Polynomial A)
    (hp : p.comp (Polynomial.C (2 : A) * Polynomial.X) = 2 * p) :
    p = Polynomial.C (p.coeff 1) * Polynomial.X := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 1
  · subst n
    simp
  · have hcoeff := congrArg (fun q : Polynomial A => q.coeff n) hp
    simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_ofNat_mul] at hcoeff
    have hmul : p.coeff n * ((2 : A) ^ n - 2) = 0 := by
      rw [mul_sub, hcoeff]
      ring
    have hne : (2 : k) ^ n - 2 ≠ 0 := by
      intro h
      have he : (2 : ℕ) ^ n = 2 ^ 1 := by
        apply Nat.cast_injective (R := k)
        simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_one] using sub_eq_zero.mp h
      exact hn (Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ)) he)
    have hu : IsUnit ((2 : A) ^ n - 2) := by
      simpa only [map_sub, map_pow, map_ofNat] using
        (isUnit_iff_ne_zero.mpr hne).map (algebraMap k A)
    rw [hu.mul_left_eq_zero] at hmul
    simpa [Polynomial.coeff_X_of_ne_one hn] using hmul

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (b : AutomorphicAction H V)
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- Scalar linearity in the supplied vector coordinates on every coefficient
algebra. Naturality of the coordinates is a separate hypothesis. -/
def IsAffineLinearVectorCoordinates : Prop :=
  ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
    (h : Lie.AffinePoints H A) (c : A) (v : Lie.AffinePoints V A),
    (vectorAffineCoordinates e A (b.act h
      ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (c • (vectorAffineCoordinates e A v).toAdd))))).toAdd =
      c • (vectorAffineCoordinates e A (b.act h v)).toAdd

variable {b e}

private def vectorAffineAction
    {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (x : Fin d → A) : Fin d → A :=
  (vectorAffineCoordinates e A
    (b.act h ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)))).toAdd

private theorem vectorAffineAction_add
    {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (x y : Fin d → A) :
    vectorAffineAction (b := b) (e := e) h (x + y) =
      vectorAffineAction (b := b) (e := e) h x +
        vectorAffineAction (b := b) (e := e) h y := by
  simp only [vectorAffineAction, ofAdd_add, map_mul, b.act_mul_right, toAdd_mul]

private theorem vectorAffineCoordinates_symm_naturality
    (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : Fin d → A) :
    Lie.affineMap V f ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)) =
      (vectorAffineCoordinates e B).symm
        (Multiplicative.ofAdd fun j => f (x j)) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]

private theorem vectorAffineAction_naturality
    (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (h : Lie.AffinePoints H A) (x : Fin d → A) :
    vectorAffineAction (b := b) (e := e) (Lie.affineMap H f h)
        (fun j => f (x j)) =
      fun j => f (vectorAffineAction (b := b) (e := e) h x j) := by
  dsimp only [vectorAffineAction]
  rw [← vectorAffineCoordinates_symm_naturality he f x,
    ← b.affineAct_naturality, he.vectorAffineCoordinates_naturality]

private theorem vectorAffineAction_smul [CharZero k]
    (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (c : A) (x : Fin d → A) :
    vectorAffineAction (b := b) (e := e) h (c • x) =
      c • vectorAffineAction (b := b) (e := e) h x := by
  let h' := Lie.affineMap H (Polynomial.CAlgHom (R := k) (A := A)) h
  let Y : Fin d → Polynomial A := fun j => Polynomial.X * Polynomial.C (x j)
  let P := vectorAffineAction (b := b) (e := e) h' Y
  let f : Polynomial A →ₐ[k] Polynomial A :=
    Polynomial.aevalTower (Polynomial.CAlgHom (R := k) (A := A)) (Polynomial.C (2 : A) * Polynomial.X)
  have hf : f.comp (Polynomial.CAlgHom (R := k) (A := A)) = Polynomial.CAlgHom (R := k) (A := A) := by
    ext a
    simp [f]
  have hconst : Lie.affineMap H f h' = h' := by
    dsimp only [h']
    rw [← Lie.affineMap_comp, hf]
  have hY : (fun j => f (Y j)) = Y + Y := by
    funext j
    simp only [Y, f, map_mul, Polynomial.aevalTower_X,
      Polynomial.aevalTower_C, Polynomial.CAlgHom_apply, Pi.add_apply,
      Polynomial.C_ofNat]
    ring
  have hnat := vectorAffineAction_naturality (b := b) he f h' Y
  rw [hconst, hY, vectorAffineAction_add] at hnat
  have hP (j : Fin d) : P j = Polynomial.C ((P j).coeff 1) * Polynomial.X := by
    apply polynomial_eq_linear_of_doubling (k := k)
    change f (P j) = 2 * P j
    have hj := congrFun hnat j
    change P j + P j = f (P j) at hj
    simpa only [two_mul] using hj.symm
  have heval (a : A) :
      vectorAffineAction (b := b) (e := e) h (a • x) =
        fun j => (P j).coeff 1 * a := by
    let g : Polynomial A →ₐ[k] A := Polynomial.aevalTower (AlgHom.id k A) a
    have hg : g.comp (Polynomial.CAlgHom (R := k) (A := A)) = AlgHom.id k A := by
      ext z
      simp [g]
    have hh : Lie.affineMap H g h' = h := by
      dsimp only [h']
      rw [← Lie.affineMap_comp, hg, Lie.affineMap_id]
    have hy : (fun j => g (Y j)) = a • x := by
      funext j
      simp only [Y, g, map_mul, Polynomial.aevalTower_X,
        Polynomial.aevalTower_C, AlgHom.id_apply, Pi.smul_apply, smul_eq_mul]
    have h := vectorAffineAction_naturality (b := b) he g h' Y
    rw [hh, hy] at h
    calc
      _ = fun j => g (P j) := h
      _ = _ := by
        funext j
        rw [hP]
        simp [g]
  have hone := heval 1
  simp only [one_smul, mul_one] at hone
  rw [heval, hone]
  funext j
  exact mul_comm _ _

/-- In characteristic zero every actual automorphic action is scalar linear
in any supplied natural vector coordinates, on all coefficient algebras. -/
theorem isAffineLinearVectorCoordinates_of_charZero [CharZero k]
    (he : IsNaturalVectorCoordinates e) :
    IsAffineLinearVectorCoordinates b e := by
  intro A h c v
  simpa only [vectorAffineAction, ofAdd_toAdd, MulEquiv.symm_apply_apply] using
    vectorAffineAction_smul (b := b) he h c (vectorAffineCoordinates e A v).toAdd

/-- Pullback through the affinization unit preserves the coefficient coordinates. -/
theorem IsNaturalVectorCoordinates.vectorAffineCoordinates_unit_comp
    (he : IsNaturalVectorCoordinates e)
    (T : Over (Spec (CommRingCat.of k)))
    (v : (algSpec (CommRingCat.of k)).obj ((algΓ (CommRingCat.of k)).obj T) ⟶ V.X) :
    (vectorAffineCoordinates e ((algΓ (CommRingCat.of k)).obj T).unop v).toAdd =
      (e T ((algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T ≫ v)).toAdd := by
  funext j
  change (Scheme.ΓSpecIso (CommRingCat.of ((algΓ (CommRingCat.of k)).obj T).unop)).hom
      ((e _ v).toAdd j) = _
  rw [he]
  have h := Corepresented.unit_appTop_ΓSpecIso_inv T
    ((Scheme.ΓSpecIso (CommRingCat.of ((algΓ (CommRingCat.of k)).obj T).unop)).hom
      ((e _ v).toAdd j))
  have hc := (Scheme.ΓSpecIso
    (CommRingCat.of ((algΓ (CommRingCat.of k)).obj T).unop)).hom_inv_id_apply
      ((e _ v).toAdd j)
  rw [hc] at h
  exact h.symm

/-- Coefficient-test scalar linearity gives scalar linearity on every scheme test
when the acting group is affine. -/
theorem IsAffineLinearVectorCoordinates.isLinearVectorCoordinates
    [IsAffineHom H.X.hom] (ha : IsAffineLinearVectorCoordinates b e)
    (he : IsNaturalVectorCoordinates e) : IsLinearVectorCoordinates b e := by
  refine ⟨he, ?_⟩
  intro T h c v
  let A := ((algΓ (CommRingCat.of k)).obj T).unop
  let c' : A := c
  let a := (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T
  let h' := Lie.affinizationFactor H h
  let v' : Lie.AffinePoints V A :=
    (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd (e T v).toAdd)
  let z' : Lie.AffinePoints V A :=
    (vectorAffineCoordinates e A).symm
      (Multiplicative.ofAdd (c' • (vectorAffineCoordinates e A v').toAdd))
  have hv : a ≫ v' = v := by
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    rw [← he.vectorAffineCoordinates_unit_comp]
    exact congrArg Multiplicative.toAdd ((vectorAffineCoordinates e A).apply_symm_apply _)
  have hz : a ≫ z' = (e T).symm (Multiplicative.ofAdd (c • (e T v).toAdd)) := by
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    rw [← he.vectorAffineCoordinates_unit_comp, MulEquiv.apply_symm_apply]
    dsimp only [z', v']
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  calc
    _ = (vectorAffineCoordinates e A (b.act h' z')).toAdd := by
      rw [he.vectorAffineCoordinates_unit_comp, b.naturality,
        Lie.unit_affinizationFactor, hz]
    _ = c' • (vectorAffineCoordinates e A (b.act h' v')).toAdd :=
      ha (CommAlgCat.of k A) h' c v'
    _ = _ := by
      rw [he.vectorAffineCoordinates_unit_comp, b.naturality,
        Lie.unit_affinizationFactor, hv]
      rfl

/-- Every actual action of an affine group on a naturally coordinatized vector
group is linear over every test's ring of global functions in characteristic zero. -/
theorem isLinearVectorCoordinates_of_charZero [CharZero k]
    [IsAffineHom H.X.hom] (he : IsNaturalVectorCoordinates e) :
    IsLinearVectorCoordinates b e :=
  (isAffineLinearVectorCoordinates_of_charZero (b := b) he).isLinearVectorCoordinates he

end Langlands.GroupScheme.RelativeRoot
