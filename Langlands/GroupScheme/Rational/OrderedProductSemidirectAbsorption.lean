import Langlands.GroupScheme.AutomorphicAction.EquivariantSemidirectMap
import Langlands.GroupScheme.Rational.OrderedProductSemidirect

/-! # Absorbing an acting group in one ordered factor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {n : ℕ} {K G : GroupScheme B}
    {H : Fin n → GroupScheme B}

/-- Replace one chosen normal factor by its semidirect product with the
acting group, retaining the original indexing and order. -/
def absorbedSemidirectFamily (c : ∀ i, AutomorphicAction K (H i))
    (p : Fin n) (i : Fin n) : GroupScheme B :=
  if i = p then (c i).semidirectProduct else H i

/-- Identify the chosen factor with its actual semidirect product. -/
def absorbedSemidirectChosenIso (c : ∀ i, AutomorphicAction K (H i))
    (p i : Fin n) (hi : i = p) :
    absorbedSemidirectFamily c p i ≅ (c i).semidirectProduct :=
  eqToIso (by simp only [absorbedSemidirectFamily, ite_eq_left hi])

/-- Identify any other factor with the original normal factor. -/
def absorbedSemidirectUnchangedIso (c : ∀ i, AutomorphicAction K (H i))
    (p i : Fin n) (hi : i ≠ p) :
    absorbedSemidirectFamily c p i ≅ H i :=
  eqToIso (by simp only [absorbedSemidirectFamily, ite_eq_right hi])

private def chosenOverIso (c : ∀ i, AutomorphicAction K (H i))
    (p i : Fin n) (hi : i = p) :
    (absorbedSemidirectFamily c p i).X ≅ (H i).X ⊗ K.X :=
  (Grp.forget (Over B)).mapIso (absorbedSemidirectChosenIso c p i hi)

private def unchangedOverIso (c : ∀ i, AutomorphicAction K (H i))
    (p i : Fin n) (hi : i ≠ p) :
    (absorbedSemidirectFamily c p i).X ≅ (H i).X :=
  (Grp.forget (Over B)).mapIso (absorbedSemidirectUnchangedIso c p i hi)

/-- Reassemble the normal coordinates and the acting coordinate into the
absorbed factors. -/
def absorbedSemidirectCoordinatesInv (c : ∀ i, AutomorphicAction K (H i))
    (p : Fin n) (T : Over B)
    (x : (∀ i, T ⟶ (H i).X) × (T ⟶ K.X)) (i : Fin n) :
    T ⟶ (absorbedSemidirectFamily c p i).X :=
  if hi : i = p then
    lift (x.1 i) x.2 ≫ (chosenOverIso c p i hi).inv
  else x.1 i ≫ (unchangedOverIso c p i hi).inv

/-- Extract the normal coordinate at each index, also at the absorbed factor. -/
def absorbedSemidirectNormalCoordinates (c : ∀ i, AutomorphicAction K (H i))
    (p : Fin n) (T : Over B)
    (x : ∀ i, T ⟶ (absorbedSemidirectFamily c p i).X) (i : Fin n) :
    T ⟶ (H i).X :=
  if hi : i = p then x i ≫ (chosenOverIso c p i hi).hom ≫ fst (H i).X K.X
  else x i ≫ (unchangedOverIso c p i hi).hom

/-- Extract the acting coordinate from the one absorbed factor. -/
def absorbedSemidirectActingCoordinate (c : ∀ i, AutomorphicAction K (H i))
    (p : Fin n) (T : Over B)
    (x : ∀ i, T ⟶ (absorbedSemidirectFamily c p i).X) : T ⟶ K.X :=
  x p ≫ (chosenOverIso c p p rfl).hom ≫ snd (H p).X K.X

/-- Coordinates on all tests for the family with the acting group absorbed
at the chosen index. This is a set equivalence, not a group homomorphism. -/
def absorbedSemidirectPointsEquiv (c : ∀ i, AutomorphicAction K (H i))
    (p : Fin n) (T : Over B) :
    (∀ i, T ⟶ (absorbedSemidirectFamily c p i).X) ≃
      (∀ i, T ⟶ (H i).X) × (T ⟶ K.X) where
  toFun x := ⟨absorbedSemidirectNormalCoordinates c p T x,
    absorbedSemidirectActingCoordinate c p T x⟩
  invFun := absorbedSemidirectCoordinatesInv c p T
  left_inv x := by
    funext i
    by_cases hi : i = p
    · subst i
      simp only [absorbedSemidirectCoordinatesInv, dite_true,
        absorbedSemidirectNormalCoordinates, absorbedSemidirectActingCoordinate]
      simp only [← comp_lift, lift_fst_snd, Category.comp_id,
        Category.assoc, Iso.hom_inv_id]
    · simp only [absorbedSemidirectCoordinatesInv, dite_eq_right hi,
        absorbedSemidirectNormalCoordinates, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
  right_inv x := by
    apply Prod.ext
    · funext i
      by_cases hi : i = p
      · simp only [absorbedSemidirectNormalCoordinates,
          absorbedSemidirectCoordinatesInv, dite_eq_left hi, Category.assoc,
          Iso.inv_hom_id_assoc, lift_fst]
      · simp only [absorbedSemidirectNormalCoordinates,
          absorbedSemidirectCoordinatesInv, dite_eq_right hi, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
    · simp only [absorbedSemidirectActingCoordinate,
        absorbedSemidirectCoordinatesInv, dite_true, Category.assoc,
        Iso.inv_hom_id_assoc, lift_snd]

/-- The canonical maps of the absorbed factors into the ambient semidirect
product, using equivariance at the chosen index. -/
def absorbedSemidirectMap
    (a : AutomorphicAction K G) (c : ∀ i, AutomorphicAction K (H i))
    (j : ∀ i, H i ⟶ G)
    (heq : ∀ (i : Fin n) (T : Over B) (s : T ⟶ K.X) (h : T ⟶ (H i).X),
      (c i).act s h ≫ (j i).hom.hom = a.act s (h ≫ (j i).hom.hom))
    (p : Fin n) (i : Fin n) :
    absorbedSemidirectFamily c p i ⟶ a.semidirectProduct :=
  if hi : i = p then
    (absorbedSemidirectChosenIso c p i hi).hom ≫
      AutomorphicAction.semidirectMap (c i) a (j i) (heq i)
  else (absorbedSemidirectUnchangedIso c p i hi).hom ≫ j i ≫ a.semidirectInl

private theorem prod_single_acting {M L : Type*} [Group M] [Group L]
    (φ : L →* MulAut M) {m : ℕ} (x : Fin m → M) (p : Fin m) (k : L) :
    (List.ofFn (fun i => (⟨x i, if i = p then k else 1⟩ :
      SemidirectProduct M L φ))).prod =
      ⟨((List.ofFn x).take (p.val + 1)).prod *
        φ k (((List.ofFn x).drop (p.val + 1)).prod), k⟩ := by
  induction m with
  | zero => exact Fin.elim0 p
  | succ m ih =>
      refine Fin.cases ?_ (fun q => ?_) p
      · have ht : (List.ofFn (fun i : Fin m =>
            (⟨x i.succ, if i.succ = 0 then k else 1⟩ :
              SemidirectProduct M L φ))).prod =
            SemidirectProduct.inl ((List.ofFn (fun i => x i.succ)).prod) := by
          simp only [Fin.succ_ne_zero, ite_false]
          change (List.ofFn (fun i => SemidirectProduct.inl (φ := φ) (x i.succ))).prod = _
          simpa only [List.map_ofFn, Function.comp_def] using
            (map_list_prod (SemidirectProduct.inl (φ := φ))
              (List.ofFn (fun i => x i.succ))).symm
        rw [List.ofFn_succ, List.prod_cons, ht]
        apply SemidirectProduct.ext
        · simp
        · simp
      · have ht := ih (fun i => x i.succ) q
        rw [List.ofFn_succ, List.prod_cons]
        have hq : (0 : Fin (m + 1)) ≠ q.succ := (Fin.succ_ne_zero q).symm
        simp only [hq, ite_false, Fin.succ_inj]
        rw [ht]
        apply SemidirectProduct.ext
        · simp only [SemidirectProduct.mul_left, map_one, MulAut.one_apply,
            List.ofFn_succ, Fin.val_succ, List.take_succ_cons,
            List.drop_succ_cons, List.prod_cons, mul_assoc]
        · simp only [SemidirectProduct.mul_right, one_mul]

/-- On all tests, reassembled factor points have exactly one nontrivial
acting coordinate after mapping to the ambient semidirect product. -/
theorem absorbedSemidirectCoordinatesInv_map_points
    (a : AutomorphicAction K G) (c : ∀ i, AutomorphicAction K (H i))
    (j : ∀ i, H i ⟶ G)
    (heq : ∀ (i : Fin n) (T : Over B) (s : T ⟶ K.X) (h : T ⟶ (H i).X),
      (c i).act s h ≫ (j i).hom.hom = a.act s (h ≫ (j i).hom.hom))
    (p : Fin n) (T : Over B)
    (x : (∀ i, T ⟶ (H i).X) × (T ⟶ K.X)) (i : Fin n) :
    a.semidirectPointsEquiv T
      (absorbedSemidirectCoordinatesInv c p T x i ≫
        (absorbedSemidirectMap a c j heq p i).hom.hom) =
      ⟨x.1 i ≫ (j i).hom.hom, if i = p then x.2 else 1⟩ := by
  by_cases hi : i = p
  · simp only [absorbedSemidirectCoordinatesInv, absorbedSemidirectMap,
      dite_eq_left hi, ite_eq_left hi]
    change a.semidirectPointsEquiv T
      ((lift (x.1 i) x.2 ≫ (chosenOverIso c p i hi).inv) ≫
        (chosenOverIso c p i hi).hom ≫
          (AutomorphicAction.semidirectMap (c i) a (j i) (heq i)).hom.hom) = _
    simp only [AutomorphicAction.semidirectMap_hom]
    apply SemidirectProduct.ext
    · change ((lift (x.1 i) x.2 ≫ (chosenOverIso c p i hi).inv) ≫
        (chosenOverIso c p i hi).hom ≫ ((j i).hom.hom ⊗ₘ 𝟙 K.X)) ≫
          fst G.X K.X = x.1 i ≫ (j i).hom.hom
      simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_fst,
        lift_fst_assoc]
    · change ((lift (x.1 i) x.2 ≫ (chosenOverIso c p i hi).inv) ≫
        (chosenOverIso c p i hi).hom ≫ ((j i).hom.hom ⊗ₘ 𝟙 K.X)) ≫
          snd G.X K.X = x.2
      simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_snd,
        Category.comp_id, lift_snd]
  · simp only [absorbedSemidirectCoordinatesInv, absorbedSemidirectMap,
      dite_eq_right hi, ite_eq_right hi]
    change a.semidirectPointsEquiv T
      ((x.1 i ≫ (unchangedOverIso c p i hi).inv) ≫
        (unchangedOverIso c p i hi).hom ≫ (j i).hom.hom ≫
          a.semidirectInl.hom.hom) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact a.semidirectInl_points (x.1 i ≫ (j i).hom.hom)

/-- The original ordered multiplication of the absorbed factors has the
prefix/action/suffix formula at the cut immediately after the chosen index. -/
theorem orderedPoints_absorbedSemidirectCoordinatesInv
    (a : AutomorphicAction K G) (c : ∀ i, AutomorphicAction K (H i))
    (j : ∀ i, H i ⟶ G)
    (heq : ∀ (i : Fin n) (T : Over B) (s : T ⟶ K.X) (h : T ⟶ (H i).X),
      (c i).act s h ≫ (j i).hom.hom = a.act s (h ≫ (j i).hom.hom))
    (p : Fin n) (T : Over B)
    (x : (∀ i, T ⟶ (H i).X) × (T ⟶ K.X)) :
    orderedPoints (absorbedSemidirectMap a c j heq p)
      (absorbedSemidirectCoordinatesInv c p T x) =
      lift
        (((List.ofFn (fun i => x.1 i ≫ (j i).hom.hom)).take (p.val + 1)).prod *
          a.act x.2
            ((List.ofFn (fun i => x.1 i ≫ (j i).hom.hom)).drop (p.val + 1)).prod)
        x.2 := by
  apply (a.semidirectPointsEquiv T).injective
  unfold orderedPoints
  rw [map_list_prod]
  simp only [List.map_ofFn, Function.comp_def,
    absorbedSemidirectCoordinatesInv_map_points]
  rw [prod_single_acting, AutomorphicAction.semidirectPointsEquiv_lift]
  rfl

private theorem comp_list_prod {T V : Over B} (q : V ⟶ T)
    (l : List (T ⟶ G.X)) :
    q ≫ l.prod = (l.map (fun x => q ≫ x)).prod := by
  induction l with
  | nil => exact MonObj.comp_one q
  | cons x l ih =>
      simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

/-- Evaluate the existing insertion morphism at arbitrary normal and acting
coordinates on an arbitrary test scheme. -/
theorem lift_semidirectOrderedMultiplication
    (a : AutomorphicAction K G) (j : ∀ i, H i ⟶ G)
    (p : ℕ) (T : Over B) (x : ∀ i, T ⟶ (H i).X) (k : T ⟶ K.X) :
    lift ((finiteProductPointsEquiv H T).symm x) k ≫
        semidirectOrderedMultiplication a j p =
      lift
        (((List.ofFn (fun i => x i ≫ (j i).hom.hom)).take p).prod *
          a.act k ((List.ofFn (fun i => x i ≫ (j i).hom.hom)).drop p).prod) k := by
  change (lift ((finiteProductPointsEquiv H T).symm x) k ≫
    semidirectOrderedMultiplication a j p : T ⟶ G.X ⊗ K.X) = _
  simp only [semidirectOrderedMultiplication, comp_lift, MonObj.comp_mul,
    AutomorphicAction.naturality, comp_list_prod, List.map_take, List.map_drop,
    List.map_ofFn, Function.comp_def, lift_snd, lift_fst_assoc]
  simp only [← Category.assoc, finiteProductPointsEquiv_symm_π]

/-- Reinterpret absorbed factor coordinates as a point of the product of
the original family product with the acting group. -/
def absorbedSemidirectSchemePointsEquiv
    (c : ∀ i, AutomorphicAction K (H i)) (p : Fin n) (T : Over B) :
    (∀ i, T ⟶ (absorbedSemidirectFamily c p i).X) ≃
      (T ⟶ (∏ᶜ H).X ⊗ K.X) :=
  (absorbedSemidirectPointsEquiv c p T).trans
    ((Equiv.prodCongr (finiteProductPointsEquiv H T).symm.toEquiv
      (Equiv.refl _)).trans homEquivToProd.symm)

/-- Absorbing the acting group into a chosen original factor preserves
the ordered multiplication isomorphism. -/
theorem isIso_orderedMultiplication_absorbedSemidirect
    (a : AutomorphicAction K G) (c : ∀ i, AutomorphicAction K (H i))
    (j : ∀ i, H i ⟶ G)
    (heq : ∀ (i : Fin n) (T : Over B) (s : T ⟶ K.X) (h : T ⟶ (H i).X),
      (c i).act s h ≫ (j i).hom.hom = a.act s (h ≫ (j i).hom.hom))
    (p : Fin n) [IsIso (orderedMultiplication j)] :
    IsIso (orderedMultiplication (absorbedSemidirectMap a c j heq p)) := by
  let : IsIso (semidirectOrderedMultiplication a j (p.val + 1)) :=
    isIso_semidirectOrderedMultiplication a c j heq (p.val + 1)
  rw [isIso_orderedMultiplication_iff]
  intro T
  have hb := (isIso_iff_yoneda_map_bijective
    (semidirectOrderedMultiplication a j (p.val + 1))).mp inferInstance T
  have hf :
      orderedPoints (absorbedSemidirectMap a c j heq p) (T := T) =
        (fun z => z ≫ semidirectOrderedMultiplication a j (p.val + 1)) ∘
          absorbedSemidirectSchemePointsEquiv c p T := by
    funext x
    let y := absorbedSemidirectPointsEquiv c p T x
    have hy : absorbedSemidirectCoordinatesInv c p T y = x :=
      (absorbedSemidirectPointsEquiv c p T).symm_apply_apply x
    change orderedPoints (absorbedSemidirectMap a c j heq p) x =
      lift ((finiteProductPointsEquiv H T).symm y.1) y.2 ≫
        semidirectOrderedMultiplication a j (p.val + 1)
    rw [← hy, orderedPoints_absorbedSemidirectCoordinatesInv,
      lift_semidirectOrderedMultiplication]
  rw [hf]
  exact hb.comp (absorbedSemidirectSchemePointsEquiv c p T).bijective

end Langlands.GroupScheme.RelativeRoot
