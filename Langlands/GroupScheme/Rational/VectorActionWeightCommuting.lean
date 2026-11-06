import Langlands.GroupScheme.Rational.VectorActionCharZero
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Linearity of vector actions commuting with a nonzero split-torus weight

An actual action on a vector group that commutes with a split-torus action of a single nonzero
weight `χ` is scalar linear in every system of weight-`χ` vector coordinates, in every
characteristic. The torus point `ζ(t)` over `A[t, t⁻¹]`, for a cocharacter `ζ` with
`⟨χ, ζ⟩ = D > 0`, scales by `t ^ D`; comparing with the substitution `X ↦ t ^ D` forces each
coordinate of the action on the tuple `X • x` to be linear in `X`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj LaurentPolynomial Polynomial

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}

/-- On every test scheme, a character `χ` takes the value `u ^ D` at `ζ(u)` when
`⟨χ, ζ⟩ = D`. -/
theorem pointsEquiv_cocharacter_comp_character {χ : characterLattice S}
    {ζ : cocharacterLattice S} {D : ℕ} (hD : latticePairing S χ ζ = D)
    (T : Over (Spec (CommRingCat.of k))) (u : (Γ(T.left, ⊤))ˣ) :
    Gm.pointsEquiv _ T (((Gm.pointsEquiv _ T).symm u ≫ (CommGroupScheme.groupHom ζ).hom.hom) ≫
      (CommGroupScheme.groupHom χ).hom.hom) = u ^ D := by
  have hζχ : ζ ≫ χ = (gmEndEquiv k).symm D := by
    rw [← hD, latticePairing_apply, AddEquiv.symm_apply_apply]
  rw [← comp_groupHom_comp, hζχ, gmEndEquiv_symm_comp, map_zpow, MulEquiv.apply_symm_apply,
    zpow_natCast]

variable {e : ∀ T : Over (Spec (CommRingCat.of k)),
  (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}

/-- Weight vector coordinates on a coefficient algebra: a torus point scales by the value of
the weight. -/
theorem IsWeightVectorCoordinates.vectorAffineCoordinates_act
    {c : AutomorphicAction S.toGrp V} {χ : characterLattice S}
    (he : IsWeightVectorCoordinates c χ e) {A : Type u} [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints S.toGrp A) (v : Lie.AffinePoints V A) :
    (vectorAffineCoordinates e A (c.act s v)).toAdd =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
          (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
            (s ≫ (CommGroupScheme.groupHom χ).hom.hom) :
              Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) •
        (vectorAffineCoordinates e A v).toAdd := by
  funext j
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom ((e _ (c.act s v)).toAdd j) = _
  rw [he.2]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.map_mul _ _

variable (b : AutomorphicAction H V)

/-- The actual action of a coefficient point, written in the coefficient coordinates `e`. -/
def coordinateAffineAction (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (x : Fin d → A) : Fin d → A :=
  (vectorAffineCoordinates e A
    (b.act h ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)))).toAdd

variable {b}

theorem coordinateAffineAction_add {A : Type u} [CommRing A] [Algebra k A]
    (h : Lie.AffinePoints H A) (x y : Fin d → A) :
    coordinateAffineAction b e h (x + y) =
      coordinateAffineAction b e h x + coordinateAffineAction b e h y := by
  simp only [coordinateAffineAction, ofAdd_add, map_mul, b.act_mul_right, toAdd_mul]

theorem coordinateAffineAction_naturality (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (h : Lie.AffinePoints H A) (x : Fin d → A) :
    coordinateAffineAction b e (Lie.affineMap H f h) (fun j => f (x j)) =
      fun j => f (coordinateAffineAction b e h x j) := by
  have hx : Lie.affineMap V f ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x)) =
      (vectorAffineCoordinates e B).symm (Multiplicative.ofAdd fun j => f (x j)) := by
    apply (vectorAffineCoordinates e B).injective
    apply Multiplicative.toAdd.injective
    rw [he.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  dsimp only [coordinateAffineAction]
  rw [← hx, ← b.affineAct_naturality, he.vectorAffineCoordinates_naturality]

variable {c : AutomorphicAction S.toGrp V} {χ : characterLattice S}

/-- An action commuting with a weight action commutes with scaling by weight values. -/
theorem coordinateAffineAction_weight_smul (he : IsWeightVectorCoordinates c χ e)
    (hbc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (s : T ⟶ S.X) (v : T ⟶ V.X),
      b.act h (c.act s v) = c.act s (b.act h v))
    {A : Type u} [CommRing A] [Algebra k A] (h : Lie.AffinePoints H A)
    (s : Lie.AffinePoints S.toGrp A) (y : Fin d → A) :
    coordinateAffineAction b e h
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
          (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
            (s ≫ (CommGroupScheme.groupHom χ).hom.hom) :
              Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) • y) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
          (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
            (s ≫ (CommGroupScheme.groupHom χ).hom.hom) :
              Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) •
        coordinateAffineAction b e h y := by
  have hy : (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom
          (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
            (s ≫ (CommGroupScheme.groupHom χ).hom.hom) :
              Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) • y)) =
      c.act s ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd y)) := by
    apply (vectorAffineCoordinates e A).injective
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.apply_symm_apply, he.vectorAffineCoordinates_act, MulEquiv.apply_symm_apply]
    rfl
  dsimp only [coordinateAffineAction]
  rw [hy, hbc, he.vectorAffineCoordinates_act]

/-- The coefficient map `A → A[t, t⁻¹]` as a map of `k`-algebras. -/
def laurentCAlgHom (A : Type u) [CommRing A] [Algebra k A] : A →ₐ[k] A[T;T⁻¹] :=
  { (LaurentPolynomial.C : A →+* A[T;T⁻¹]) with
    commutes' := fun r => (LaurentPolynomial.algebraMap_apply r).symm }

@[simp] theorem laurentCAlgHom_apply {A : Type u} [CommRing A] [Algebra k A] (a : A) :
    laurentCAlgHom (k := k) A a = LaurentPolynomial.C a := rfl

/-- The substitution `X ↦ t ^ D` from `A[X]` to `A[t, t⁻¹]`. -/
def laurentPowerAlgHom (A : Type u) [CommRing A] [Algebra k A] (D : ℕ) :
    A[X] →ₐ[k] A[T;T⁻¹] :=
  Polynomial.aevalTower (laurentCAlgHom (k := k) A) (LaurentPolynomial.T D)

theorem laurentPowerAlgHom_injective (A : Type u) [CommRing A] [Algebra k A] {D : ℕ}
    (hD : 0 < D) : Function.Injective (laurentPowerAlgHom (k := k) A D) := by
  have h : (laurentPowerAlgHom (k := k) A D : A[X] →+* A[T;T⁻¹]) =
      (Polynomial.toLaurent : A[X] →+* A[T;T⁻¹]).comp
        (Polynomial.expand A D : A[X] →ₐ[A] A[X]).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [laurentPowerAlgHom]
    · simp [laurentPowerAlgHom, Polynomial.toLaurent_X_pow]
  intro p q hpq
  have hpq' : (laurentPowerAlgHom (k := k) A D : A[X] →+* A[T;T⁻¹]) p =
      (laurentPowerAlgHom (k := k) A D : A[X] →+* A[T;T⁻¹]) q := hpq
  rw [h] at hpq'
  exact Polynomial.expand_injective hD (Polynomial.toLaurent_injective hpq')

/-- The unit `t` of the test scheme `Spec A[t, t⁻¹]`. -/
theorem isUnit_laurentT_global (A : Type u) [CommRing A] [Algebra k A] :
    @IsUnit Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A[T;T⁻¹]))).left, ⊤) _
      ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv (LaurentPolynomial.T 1)) :=
  (LaurentPolynomial.isUnit_T (R := A) 1).map (Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv.hom

/-- The torus point `ζ(t)` of `Spec A[t, t⁻¹]`, for a cocharacter `ζ`. -/
def laurentCocharacterPoint (A : Type u) [CommRing A] [Algebra k A]
    (ζ : cocharacterLattice S) : Lie.AffinePoints S.toGrp A[T;T⁻¹] :=
  (Gm.pointsEquiv _ _).symm (isUnit_laurentT_global (k := k) A).unit ≫
    (CommGroupScheme.groupHom ζ).hom.hom

theorem laurentCocharacterPoint_value {A : Type u} [CommRing A] [Algebra k A]
    {ζ : cocharacterLattice S} {D : ℕ} (hD : latticePairing S χ ζ = D) :
    (Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).hom
        (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A[T;T⁻¹])))
          (laurentCocharacterPoint A ζ ≫ (CommGroupScheme.groupHom χ).hom.hom) :
            Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A[T;T⁻¹]))).left, ⊤)) =
      LaurentPolynomial.T D := by
  rw [laurentCocharacterPoint, pointsEquiv_cocharacter_comp_character hD, Units.val_pow_eq_pow_val]
  change (Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).hom
    (((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv (LaurentPolynomial.T 1)) ^ D) = _
  rw [map_pow, Iso.inv_hom_id_apply, LaurentPolynomial.T_pow, mul_one]

/-- **Scalar linearity on coefficient algebras.** An action commuting with a split-torus action
of one nonzero weight is scalar linear in weight vector coordinates, in every characteristic. -/
theorem coordinateAffineAction_smul (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)
    (he : IsWeightVectorCoordinates c χ e)
    (hbc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (s : T ⟶ S.X) (v : T ⟶ V.X),
      b.act h (c.act s v) = c.act s (b.act h v))
    {A : Type u} [CommRing A] [Algebra k A] (h : Lie.AffinePoints H A) (a : A)
    (x : Fin d → A) :
    coordinateAffineAction b e h (a • x) = a • coordinateAffineAction b e h x := by
  obtain ⟨D, hD, ζ, hζ⟩ := hS.exists_pairing_eq_pos hχ
  let h' := Lie.affineMap H (Polynomial.CAlgHom (R := k) (A := A)) h
  let Y : Fin d → A[X] := fun j => Polynomial.X * Polynomial.C (x j)
  let P := coordinateAffineAction b e h' Y
  let φ := laurentPowerAlgHom (k := k) A D
  have hφC : φ.comp (Polynomial.CAlgHom (R := k) (A := A)) = laurentCAlgHom A := by
    ext a
    simp [φ, laurentPowerAlgHom]
  have hh' : Lie.affineMap H φ h' = Lie.affineMap H (laurentCAlgHom A) h := by
    dsimp only [h']
    rw [← Lie.affineMap_comp, hφC]
  have hY : (fun j => φ (Y j)) =
      (LaurentPolynomial.T D : A[T;T⁻¹]) • fun j => laurentCAlgHom (k := k) A (x j) := by
    funext j
    simp [Y, φ, laurentPowerAlgHom]
  -- the action on the constant tuple, scaled by `t ^ D`
  have hscale := coordinateAffineAction_weight_smul (b := b) he hbc
    (Lie.affineMap H (laurentCAlgHom A) h) (laurentCocharacterPoint A ζ)
    (fun j => laurentCAlgHom (k := k) A (x j))
  rw [laurentCocharacterPoint_value hζ, coordinateAffineAction_naturality he.1] at hscale
  have hnat := coordinateAffineAction_naturality (b := b) he.1 φ h' Y
  rw [hh', hY, hscale] at hnat
  have hP (j : Fin d) : P j = Polynomial.X * Polynomial.C (coordinateAffineAction b e h x j) := by
    apply laurentPowerAlgHom_injective (k := k) A hD
    have hj := congrFun hnat j
    simp only [Pi.smul_apply, smul_eq_mul] at hj
    change φ (P j) = _
    rw [← hj]
    simp [laurentPowerAlgHom]
  let g : A[X] →ₐ[k] A := Polynomial.aevalTower (AlgHom.id k A) a
  have hg : g.comp (Polynomial.CAlgHom (R := k) (A := A)) = AlgHom.id k A := by
    ext z
    simp [g]
  have hgh : Lie.affineMap H g h' = h := by
    dsimp only [h']
    rw [← Lie.affineMap_comp, hg, Lie.affineMap_id]
  have hgY : (fun j => g (Y j)) = a • x := by
    funext j
    simp [Y, g]
    exact mul_comm _ _
  have hev := coordinateAffineAction_naturality (b := b) he.1 g h' Y
  rw [hgh, hgY] at hev
  rw [hev]
  funext j
  change g (P j) = a * coordinateAffineAction b e h x j
  rw [hP]
  simp [g]
  exact mul_comm _ _

/-- Coefficient-test scalar linearity of an action commuting with a nonzero weight action. -/
theorem isAffineLinearVectorCoordinates_of_commute (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)
    (he : IsWeightVectorCoordinates c χ e)
    (hbc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (s : T ⟶ S.X) (v : T ⟶ V.X),
      b.act h (c.act s v) = c.act s (b.act h v)) :
    IsAffineLinearVectorCoordinates b e := by
  intro A h a v
  simpa only [coordinateAffineAction, ofAdd_toAdd, MulEquiv.symm_apply_apply] using
    coordinateAffineAction_smul hS hχ he hbc h a (vectorAffineCoordinates e A v).toAdd

/-- **Linearity in every characteristic.** If an affine group acts on a vector group commuting
with a split-torus action of one nonzero weight `χ`, then the action is scalar linear over every
test scheme's ring of global functions in every system of weight-`χ` vector coordinates. -/
theorem isLinearVectorCoordinates_of_commute [IsAffineHom H.X.hom] (hS : IsSplitTorus S.toGrp)
    (hχ : χ ≠ 0) (he : IsWeightVectorCoordinates c χ e)
    (hbc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (s : T ⟶ S.X) (v : T ⟶ V.X),
      b.act h (c.act s v) = c.act s (b.act h v)) :
    IsLinearVectorCoordinates b e :=
  (isAffineLinearVectorCoordinates_of_commute hS hχ he hbc).isLinearVectorCoordinates he.1

end Langlands.GroupScheme.RelativeRoot
