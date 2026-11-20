import Langlands.GroupScheme.Reductive.LocalSplitBigCellProof
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # The coordinate ring of the big-cell source over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell

section Ring

variable (k : Type u) [Field k] (I : Type u) [Fintype I] (m n : ℕ)

/-- The coordinates of the cell source: negative-root, positive-root and torus coordinates. -/
abbrev CellVar : Type u := Fin m ⊕ Fin n ⊕ I

/-- The product of the torus coordinates. -/
def torusMonomial : MvPolynomial (CellVar I m n) k :=
  ∏ i : I, MvPolynomial.X (Sum.inr (Sum.inr i))

theorem torusMonomial_ne_zero : torusMonomial k I m n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => MvPolynomial.X_ne_zero _

/-- The coordinate ring `k[v, w, t, t⁻¹]` of `𝔾ₐᵐ × 𝔾ₘ^I × 𝔾ₐⁿ`. -/
abbrev CellRing : Type u := Localization.Away (torusMonomial k I m n)

instance : IsDomain (CellRing k I m n) :=
  IsLocalization.Away.isDomain _ (torusMonomial_ne_zero k I m n)

instance : UniqueFactorizationMonoid (CellRing k I m n) := inferInstance

/-- A negative-root coordinate. -/
def negVar (r : Fin m) : CellRing k I m n :=
  algebraMap (MvPolynomial (CellVar I m n) k) (CellRing k I m n) (MvPolynomial.X (Sum.inl r))

/-- A positive-root coordinate. -/
def posVar (r : Fin n) : CellRing k I m n :=
  algebraMap (MvPolynomial (CellVar I m n) k) (CellRing k I m n)
    (MvPolynomial.X (Sum.inr (Sum.inl r)))

theorem isUnit_torusVar (i : I) :
    IsUnit (algebraMap (MvPolynomial (CellVar I m n) k) (CellRing k I m n)
      (MvPolynomial.X (Sum.inr (Sum.inr i)))) := by
  have hd : (MvPolynomial.X (Sum.inr (Sum.inr i)) : MvPolynomial (CellVar I m n) k) ∣
      torusMonomial k I m n :=
    Finset.dvd_prod_of_mem (fun i : I => MvPolynomial.X (Sum.inr (Sum.inr i))) (Finset.mem_univ i)
  exact isUnit_of_dvd_unit (map_dvd _ hd)
    (IsLocalization.Away.algebraMap_isUnit (S := CellRing k I m n) (torusMonomial k I m n))

/-- A torus coordinate, as a unit. -/
def torusVar (i : I) : (CellRing k I m n)ˣ :=
  (isUnit_torusVar k I m n i).unit

@[simp] theorem torusVar_val (i : I) :
    (torusVar k I m n i : CellRing k I m n) =
      algebraMap (MvPolynomial (CellVar I m n) k) (CellRing k I m n)
        (MvPolynomial.X (Sum.inr (Sum.inr i))) := rfl

variable {k I m n} {C : Type u} [CommRing C]

/-- Ring maps out of the cell ring agreeing on scalars and on all coordinates are equal. -/
theorem ringHom_ext {φ ψ : CellRing k I m n →+* C}
    (hk : φ.comp (algebraMap k _) = ψ.comp (algebraMap k _))
    (hneg : ∀ r, φ (negVar k I m n r) = ψ (negVar k I m n r))
    (hpos : ∀ r, φ (posVar k I m n r) = ψ (posVar k I m n r))
    (htor : ∀ i, φ (torusVar k I m n i) = ψ (torusVar k I m n i)) : φ = ψ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (torusMonomial k I m n))
  apply MvPolynomial.ringHom_ext
  · intro a
    have h := congrArg (fun f : k →+* C => f a) hk
    simp only [RingHom.comp_apply] at h ⊢
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact h
  · rintro (r | r | i)
    · exact hneg r
    · exact hpos r
    · exact htor i

/-- The ring map out of the cell ring with prescribed scalars and coordinates. -/
def liftHom (f : k →+* C) (v : Fin m → C) (w : Fin n → C) (t : I → Cˣ) :
    CellRing k I m n →+* C :=
  IsLocalization.lift (M := Submonoid.powers (torusMonomial k I m n))
    (g := MvPolynomial.eval₂Hom f (Sum.elim v (Sum.elim w fun i => (t i : C)))) <| by
      rintro ⟨_, j, rfl⟩
      simp only [map_pow, torusMonomial, map_prod, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, Sum.elim_inr]
      apply IsUnit.pow j
      rw [← Units.coe_prod]
      exact Units.isUnit _

theorem liftHom_algebraMap (f : k →+* C) (v : Fin m → C) (w : Fin n → C) (t : I → Cˣ) (a : k) :
    liftHom f v w t (algebraMap k (CellRing k I m n) a) = f a := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (CellVar I m n) k) (CellRing k I m n),
    liftHom, IsLocalization.lift_eq]
  simp

theorem liftHom_comp_algebraMap (f : k →+* C) (v : Fin m → C) (w : Fin n → C) (t : I → Cˣ) :
    (liftHom f v w t).comp (algebraMap k (CellRing k I m n)) = f :=
  RingHom.ext (liftHom_algebraMap f v w t)

@[simp] theorem liftHom_negVar (f : k →+* C) (v : Fin m → C) (w : Fin n → C) (t : I → Cˣ)
    (r : Fin m) : liftHom f v w t (negVar k I m n r) = v r := by
  simp [liftHom, negVar, IsLocalization.lift_eq]

@[simp] theorem liftHom_posVar (f : k →+* C) (v : Fin m → C) (w : Fin n → C) (t : I → Cˣ)
    (r : Fin n) : liftHom f v w t (posVar k I m n r) = w r := by
  simp [liftHom, posVar, IsLocalization.lift_eq]

@[simp] theorem liftHom_torusVar (f : k →+* C) (v : Fin m → C) (w : Fin n → C) (t : I → Cˣ)
    (i : I) : liftHom f v w t (torusVar k I m n i) = t i := by
  simp [liftHom, torusVar_val, IsLocalization.lift_eq]

variable (k I m n) in
/-- A negative-root coordinate is a prime element of the cell ring. -/
theorem prime_negVar (r : Fin m) : Prime (negVar k I m n r) := by
  classical
  have hX : Prime (MvPolynomial.X (Sum.inl r) : MvPolynomial (CellVar I m n) k) :=
    MvPolynomial.X_prime
  have hd : Disjoint (Submonoid.powers (torusMonomial k I m n) : Set (MvPolynomial (CellVar I m n) k))
      ((Ideal.span {(MvPolynomial.X (Sum.inl r) : MvPolynomial (CellVar I m n) k)} :
        Ideal (MvPolynomial (CellVar I m n) k)) : Set (MvPolynomial (CellVar I m n) k)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨j, rfl⟩ hmem
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hmem
    let φ := MvPolynomial.eval (R := k)
      (Function.update (fun _ : CellVar I m n => (1 : k)) (Sum.inl r) 0)
    have h := map_dvd φ hmem
    have h1 : φ (MvPolynomial.X (Sum.inl r)) = 0 := by simp [φ]
    have h2 : φ (torusMonomial k I m n ^ j) = 1 := by
      simp [φ, torusMonomial, map_prod, Function.update_of_ne]
    rw [h1, h2, zero_dvd_iff] at h
    exact one_ne_zero h
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (torusMonomial k I m n)) (CellRing k I m n) _
    ((Ideal.span_singleton_prime hX.ne_zero).2 hX) hd
  rw [Ideal.map_span, Set.image_singleton] at hprime
  have hne : negVar k I m n r ≠ 0 := by
    intro h0
    apply hX.ne_zero
    apply IsLocalization.injective (CellRing k I m n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (torusMonomial_ne_zero k I m n))
    rw [map_zero]
    exact h0
  exact (Ideal.span_singleton_prime hne).1 hprime

/-- The translation of a negative-root coordinate by a scalar of the ring. -/
def shiftHom (r : Fin m) (s : CellRing k I m n) : CellRing k I m n →+* CellRing k I m n :=
  liftHom (algebraMap k _) (Function.update (negVar k I m n) r (negVar k I m n r + s))
    (posVar k I m n) (torusVar k I m n)

theorem shiftHom_negVar_self (r : Fin m) (s : CellRing k I m n) :
    shiftHom r s (negVar k I m n r) = negVar k I m n r + s := by
  rw [shiftHom, liftHom_negVar, Function.update_self]

theorem shiftHom_negVar_of_ne {r r' : Fin m} (h : r' ≠ r) (s : CellRing k I m n) :
    shiftHom r s (negVar k I m n r') = negVar k I m n r' := by
  rw [shiftHom, liftHom_negVar, Function.update_of_ne h]

theorem shiftHom_posVar (r : Fin m) (s : CellRing k I m n) (r' : Fin n) :
    shiftHom r s (posVar k I m n r') = posVar k I m n r' := by
  rw [shiftHom, liftHom_posVar]

theorem shiftHom_torusVar (r : Fin m) (s : CellRing k I m n) (i : I) :
    shiftHom r s (torusVar k I m n i : CellRing k I m n) = torusVar k I m n i := by
  rw [shiftHom, liftHom_torusVar]

theorem shiftHom_comp (r : Fin m) (s s' : CellRing k I m n) (hs : shiftHom r s s' + s = 0) :
    (shiftHom r s).comp (shiftHom r s') = RingHom.id _ := by
  apply ringHom_ext
  · rw [RingHom.comp_assoc, shiftHom, shiftHom, liftHom_comp_algebraMap,
      liftHom_comp_algebraMap]
    rfl
  · intro r'
    simp only [RingHom.comp_apply, RingHom.id_apply]
    by_cases h : r' = r
    · subst h
      rw [shiftHom_negVar_self, map_add, shiftHom_negVar_self]
      linear_combination hs
    · rw [shiftHom_negVar_of_ne h, shiftHom_negVar_of_ne h]
  · intro r'
    simp only [RingHom.comp_apply, RingHom.id_apply, shiftHom_posVar]
  · intro i
    simp only [RingHom.comp_apply, RingHom.id_apply, shiftHom_torusVar]

/-- The translation `v_r ↦ v_r + 1` as a ring automorphism of the cell ring. -/
def shiftEquiv (r : Fin m) : CellRing k I m n ≃+* CellRing k I m n :=
  RingEquiv.ofRingHom (shiftHom r 1) (shiftHom r (-1))
    (shiftHom_comp r 1 (-1) (by rw [map_neg, map_one, neg_add_cancel]))
    (shiftHom_comp r (-1) 1 (by rw [map_one, add_neg_cancel]))

theorem shiftEquiv_negVar (r : Fin m) :
    shiftEquiv r (negVar k I m n r) = 1 + negVar k I m n r := by
  change shiftHom r 1 (negVar k I m n r) = _
  rw [shiftHom_negVar_self, add_comm]

variable (k I m n) in
/-- `1 + v_r` is a prime element of the cell ring. -/
theorem prime_one_add_negVar (r : Fin m) : Prime (1 + negVar k I m n r) := by
  rw [← shiftEquiv_negVar]
  exact (MulEquiv.prime_iff (shiftEquiv r).toMulEquiv).2 (prime_negVar k I m n r)

end Ring

section Scheme

variable (k : Type u) [Field k] (I : Type u) [Fintype I] (m n : ℕ)

/-- The spectrum of the cell ring, over `Spec k`. -/
abbrev cellSpec : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (CellRing k I m n))))

variable {k I m n}

/-- The ring map of a point of the cell spectrum. -/
def pointRing {W : Over (Spec (CommRingCat.of k))} (z : W ⟶ cellSpec k I m n) :
    CellRing k I m n →+* Γ(W.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (CellRing k I m n))).inv ≫ z.left.appTop).hom

theorem pointRing_comp_algebraMap {W : Over (Spec (CommRingCat.of k))}
    (z : W ⟶ cellSpec k I m n) :
    (pointRing z).comp (algebraMap k (CellRing k I m n)) = scalarMap W := by
  have h := congrArg Scheme.Hom.appTop (Over.w z)
  simp only [Over.mk_hom, Scheme.Hom.comp_appTop] at h
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (CellRing k I m n)))
  change ((CommRingCat.ofHom (algebraMap k (CellRing k I m n)) ≫
    (Scheme.ΓSpecIso (CommRingCat.of (CellRing k I m n))).inv ≫ z.left.appTop)).hom =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ W.hom.appTop).hom
  rw [← h, reassoc_of% h2]

theorem pointRing_injective {W : Over (Spec (CommRingCat.of k))} :
    Function.Injective (pointRing (W := W) (k := k) (I := I) (m := m) (n := n)) := by
  intro z z' h
  apply Over.OverMorphism.ext
  apply ext_to_Spec
  simp only [Scheme.Γ_map_op]
  exact CommRingCat.hom_ext h

theorem exists_pointRing_eq {W : Over (Spec (CommRingCat.of k))}
    (φ : CellRing k I m n →+* Γ(W.left, ⊤))
    (hφ : φ.comp (algebraMap k (CellRing k I m n)) = scalarMap W) :
    ∃ z : W ⟶ cellSpec k I m n, pointRing z = φ := by
  let zl : W.left ⟶ Spec (CommRingCat.of (CellRing k I m n)) :=
    ΓSpec.adjunction.homEquiv W.left (op (CommRingCat.of (CellRing k I m n)))
      (CommRingCat.ofHom φ).op
  have hzl : (Scheme.ΓSpecIso (CommRingCat.of (CellRing k I m n))).inv ≫ zl.appTop =
      CommRingCat.ofHom φ :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom φ)
  have hw : zl ≫ Spec.map (CommRingCat.ofHom (algebraMap k (CellRing k I m n))) = W.hom := by
    apply ext_to_Spec
    simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
    erw [← reassoc_of% (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap k (CellRing k I m n)))), hzl]
    apply CommRingCat.hom_ext
    exact hφ
  exact ⟨Over.homMk zl hw, CommRingCat.hom_ext_iff.1 hzl⟩

variable (k I m n)

/-- The negative-root coordinate functions on the cell spectrum. -/
def specNeg (r : Fin m) : Γ((cellSpec k I m n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CellRing k I m n))).inv (negVar k I m n r)

/-- The positive-root coordinate functions on the cell spectrum. -/
def specPos (r : Fin n) : Γ((cellSpec k I m n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CellRing k I m n))).inv (posVar k I m n r)

/-- The torus coordinate of the cell spectrum. -/
def specTorus : cellSpec k I m n ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X :=
  (splitTorus.pointsEquiv I (cellSpec k I m n)).symm fun i =>
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing k I m n))).inv.hom.toMonoidHom
      (torusVar k I m n i)

/-- The comparison map from the cell spectrum to the cell source `𝔾ₐᵐ × T × 𝔾ₐⁿ`. -/
def cellCoordHom : cellSpec k I m n ⟶ cellObj k I m n :=
  lift (lift ((VectorGroup.coordinates (CommRingCat.of k) m _).symm
      (Multiplicative.ofAdd (specNeg k I m n))) (specTorus k I m n))
    ((VectorGroup.coordinates (CommRingCat.of k) n _).symm
      (Multiplicative.ofAdd (specPos k I m n)))

variable {k I m n}

theorem pointsEquiv_comp_specTorus {W : Over (Spec (CommRingCat.of k))}
    (z : W ⟶ cellSpec k I m n) (i : I) :
    (splitTorus.pointsEquiv I W (z ≫ specTorus k I m n) i : Γ(W.left, ⊤)) =
      pointRing z (torusVar k I m n i) := by
  rw [splitTorus.pointsEquiv_naturality, specTorus, MulEquiv.apply_symm_apply]
  rfl

theorem coordTriple_comp_cellCoordHom {W : Over (Spec (CommRingCat.of k))}
    (z : W ⟶ cellSpec k I m n) :
    LocalSplitBigCell.coordTriple (z ≫ cellCoordHom k I m n) =
      (fun r => pointRing z (negVar k I m n r), z ≫ specTorus k I m n,
        fun r => pointRing z (posVar k I m n r)) := by
  simp only [LocalSplitBigCell.coordTriple, negCoord_comp, posCoord_comp, torusCoord_comp]
  simp only [negCoord, torusCoord, posCoord, cellCoordHom, lift_fst_assoc, lift_fst, lift_snd,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]
  rfl

theorem bijective_comp_cellCoordHom (W : Over (Spec (CommRingCat.of k))) :
    Function.Bijective fun z : W ⟶ cellSpec k I m n => z ≫ cellCoordHom k I m n := by
  have hT := LocalSplitBigCell.coordTriple_bijective k I m n W
  have hF : Function.Bijective fun z : W ⟶ cellSpec k I m n =>
      LocalSplitBigCell.coordTriple (z ≫ cellCoordHom k I m n) := by
    constructor
    · intro z z' h
      simp only [coordTriple_comp_cellCoordHom, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      apply pointRing_injective
      apply ringHom_ext
      · rw [pointRing_comp_algebraMap, pointRing_comp_algebraMap]
      · exact congrFun h1
      · exact congrFun h3
      · intro i
        rw [← pointsEquiv_comp_specTorus, ← pointsEquiv_comp_specTorus, h2]
    · rintro ⟨v, t, w⟩
      obtain ⟨z, hz⟩ := exists_pointRing_eq
        (liftHom (scalarMap W) v w (splitTorus.pointsEquiv I W t))
        (liftHom_comp_algebraMap _ _ _ _)
      refine ⟨z, ?_⟩
      simp only [coordTriple_comp_cellCoordHom, hz, liftHom_negVar, liftHom_posVar]
      congr 1
      congr 1
      apply (splitTorus.pointsEquiv I W).injective
      funext i
      apply Units.ext
      rw [pointsEquiv_comp_specTorus, hz, liftHom_torusVar]
  constructor
  · intro z z' h
    exact hF.1 (by simp only [h])
  · intro x
    obtain ⟨z, hz⟩ := hF.2 (LocalSplitBigCell.coordTriple x)
    exact ⟨z, hT.1 hz⟩

instance isIso_cellCoordHom : IsIso (cellCoordHom k I m n) := by
  rw [isIso_iff_yoneda_map_bijective]
  exact bijective_comp_cellCoordHom

end Scheme

end Langlands.GroupScheme.SplitFactorial
