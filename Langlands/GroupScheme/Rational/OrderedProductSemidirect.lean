import Langlands.GroupScheme.AutomorphicAction.SemidirectProduct
import Langlands.GroupScheme.Rational.OrderedProductPoints

/-! # Moving an acting factor through an ordered group-scheme product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {n : ℕ} {K G : GroupScheme B}
    {H : Fin n → GroupScheme B}

/-- Act on the coordinates at or after a cut, keeping the acting point.
This is one actual morphism of schemes. -/
def suffixActionMap (c : ∀ i, AutomorphicAction K (H i)) (p : ℕ) :
    (∏ᶜ H).X ⊗ K.X ⟶ (∏ᶜ H).X ⊗ K.X :=
  lift ((finiteProductPointsEquiv H ((∏ᶜ H).X ⊗ K.X)).symm
    (fun i => if p ≤ i.val then
      (c i).act (snd _ _) (fst _ _ ≫ (Pi.π H i).hom.hom)
      else fst _ _ ≫ (Pi.π H i).hom.hom)) (snd _ _)

@[reassoc (attr := simp)]
theorem suffixActionMap_snd (c : ∀ i, AutomorphicAction K (H i)) (p : ℕ) :
    suffixActionMap c p ≫ snd _ _ = snd _ _ := by
  simp only [suffixActionMap, lift_snd]

theorem suffixActionMap_fst_π (c : ∀ i, AutomorphicAction K (H i))
    (p : ℕ) (i : Fin n) :
    suffixActionMap c p ≫ fst _ _ ≫ (Pi.π H i).hom.hom =
      if p ≤ i.val then
        (c i).act (snd _ _) (fst _ _ ≫ (Pi.π H i).hom.hom)
      else fst _ _ ≫ (Pi.π H i).hom.hom := by
  rw [← Category.assoc, suffixActionMap, lift_fst, finiteProductPointsEquiv_symm_π]

theorem comp_suffixActionMap_fst_π (c : ∀ i, AutomorphicAction K (H i))
    (p : ℕ) {T : Over B} (x : T ⟶ (∏ᶜ H).X ⊗ K.X) (i : Fin n) :
    (x ≫ suffixActionMap c p) ≫ fst _ _ ≫ (Pi.π H i).hom.hom =
      if p ≤ i.val then
        (c i).act (x ≫ snd _ _) (x ≫ fst _ _ ≫ (Pi.π H i).hom.hom)
      else x ≫ fst _ _ ≫ (Pi.π H i).hom.hom := by
  rw [Category.assoc, suffixActionMap_fst_π]
  split_ifs <;> simp only [AutomorphicAction.naturality]

/-- Acting on a suffix is invertible over every base scheme. The inverse
uses the inverse acting point on that same suffix. -/
theorem isIso_suffixActionMap (c : ∀ i, AutomorphicAction K (H i)) (p : ℕ) :
    IsIso (suffixActionMap c p) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  constructor
  · intro x y hxy
    have hs : x ≫ snd _ _ = y ≫ snd _ _ := by
      simpa only [Category.assoc, suffixActionMap_snd] using
        congrArg (fun z => z ≫ snd (∏ᶜ H).X K.X) hxy
    apply CartesianMonoidalCategory.hom_ext
    · apply Fan.IsLimit.hom_ext (finiteProductIsLimit H)
      intro i
      change (x ≫ fst _ _) ≫ (Pi.π H i).hom.hom =
        (y ≫ fst _ _) ≫ (Pi.π H i).hom.hom
      simp only [Category.assoc]
      have hi := congrArg (fun z => z ≫ fst (∏ᶜ H).X K.X ≫
        (Pi.π H i).hom.hom) hxy
      rw [comp_suffixActionMap_fst_π, comp_suffixActionMap_fst_π, hs] at hi
      by_cases hp : p ≤ i.val
      · simp only [ite_eq_left hp] at hi
        exact ((c i).pointAut T (y ≫ snd _ _)).injective hi
      · simpa only [ite_eq_right hp] using hi
    · exact hs
  · intro y
    let xs : ∀ i, T ⟶ (H i).X := fun i =>
      if p ≤ i.val then
        (c i).act (y ≫ snd _ _)⁻¹ (y ≫ fst _ _ ≫ (Pi.π H i).hom.hom)
      else y ≫ fst _ _ ≫ (Pi.π H i).hom.hom
    let x : T ⟶ (∏ᶜ H).X ⊗ K.X :=
      lift ((finiteProductPointsEquiv H T).symm xs) (y ≫ snd _ _)
    refine ⟨x, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · apply Fan.IsLimit.hom_ext (finiteProductIsLimit H)
      intro i
      change ((x ≫ suffixActionMap c p) ≫ fst _ _) ≫ (Pi.π H i).hom.hom =
        (y ≫ fst _ _) ≫ (Pi.π H i).hom.hom
      simp only [Category.assoc]
      rw [← Category.assoc x (suffixActionMap c p)]
      rw [comp_suffixActionMap_fst_π]
      simp only [x, lift_snd, lift_fst_assoc, finiteProductPointsEquiv_symm_π]
      dsimp only [xs]
      split_ifs <;> simp only [AutomorphicAction.act_act_inv]
    · simp only [Category.assoc, suffixActionMap_snd, x, lift_snd]

private theorem prod_suffix_action {M : Type*} [Monoid M]
    (f : M →* M) {m : ℕ} (x : Fin m → M) (p : ℕ) :
    (List.ofFn (fun i => if p ≤ i.val then f (x i) else x i)).prod =
      ((List.ofFn x).take p).prod * f (((List.ofFn x).drop p).prod) := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
      cases p with
      | zero =>
          simpa only [Nat.zero_le, ite_true, List.take_zero, List.prod_nil,
            List.drop_zero, one_mul, List.map_ofFn, Function.comp_def]
            using (map_list_prod f (List.ofFn x)).symm
      | succ p =>
          have hp : ¬ p + 1 ≤ 0 := by omega
          simpa only [List.ofFn_succ, Fin.val_zero, hp, ite_false,
            List.prod_cons, List.take_succ_cons, List.drop_succ_cons, Fin.val_succ,
            Nat.succ_le_succ_iff, mul_assoc]
            using congrArg (fun z => x 0 * z) (ih (fun i => x i.succ) p)

/-- Ordered multiplication with an acting factor inserted at a cut.
In semidirect coordinates it is the prefix product times the action on
the suffix product, together with the original acting point. -/
def semidirectOrderedMultiplication (a : AutomorphicAction K G)
    (j : ∀ i, H i ⟶ G) (p : ℕ) :
    (∏ᶜ H).X ⊗ K.X ⟶ a.semidirectProduct.X :=
  let l := List.ofFn (fun i : Fin n =>
    fst (∏ᶜ H).X K.X ≫ (Pi.π H i).hom.hom ≫ (j i).hom.hom)
  lift ((l.take p).prod * a.act (snd _ _) (l.drop p).prod) (snd _ _)

/-- Equivariant factor inclusions identify insertion with an invertible
suffix action followed by the original ordered multiplication. -/
theorem suffixActionMap_comp_orderedMultiplication
    (a : AutomorphicAction K G) (c : ∀ i, AutomorphicAction K (H i))
    (j : ∀ i, H i ⟶ G)
    (heq : ∀ (i : Fin n) (T : Over B) (s : T ⟶ K.X) (h : T ⟶ (H i).X),
      (c i).act s h ≫ (j i).hom.hom = a.act s (h ≫ (j i).hom.hom))
    (p : ℕ) :
    suffixActionMap c p ≫ (orderedMultiplication j ⊗ₘ 𝟙 K.X) =
      semidirectOrderedMultiplication a j p := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, semidirectOrderedMultiplication,
      lift_fst]
    rw [← Category.assoc, comp_orderedMultiplication]
    unfold orderedPoints
    have hcoord : (List.ofFn (fun i =>
        finiteProductPointsEquiv H ((∏ᶜ H).X ⊗ K.X)
          (suffixActionMap c p ≫ fst _ _) i ≫ (j i).hom.hom)) =
        List.ofFn (fun i : Fin n => if p ≤ i.val then
          a.act (snd _ _) (fst _ _ ≫ (Pi.π H i).hom.hom ≫ (j i).hom.hom)
          else fst _ _ ≫ (Pi.π H i).hom.hom ≫ (j i).hom.hom) := by
      apply congrArg List.ofFn
      funext i
      rw [finiteProductPointsEquiv_apply]
      have hi := congrArg (fun z => z ≫ (j i).hom.hom)
        (suffixActionMap_fst_π c p i)
      by_cases hp : p ≤ i.val
      · simpa only [ite_eq_left hp, heq, Category.assoc] using hi
      · simpa only [ite_eq_right hp, Category.assoc] using hi
    rw [hcoord]
    exact prod_suffix_action
      (a.pointAut ((∏ᶜ H).X ⊗ K.X) (snd _ _)).toMonoidHom _ p
  · simp only [Category.assoc, tensorHom_snd, Category.comp_id,
      suffixActionMap_snd, semidirectOrderedMultiplication, lift_snd]

/-- If the original ordered product is a scheme isomorphism and the acting
group preserves every factor through actual actions, its insertion at any
cut is also a scheme isomorphism. -/
theorem isIso_semidirectOrderedMultiplication
    (a : AutomorphicAction K G) (c : ∀ i, AutomorphicAction K (H i))
    (j : ∀ i, H i ⟶ G)
    (heq : ∀ (i : Fin n) (T : Over B) (s : T ⟶ K.X) (h : T ⟶ (H i).X),
      (c i).act s h ≫ (j i).hom.hom = a.act s (h ≫ (j i).hom.hom))
    (p : ℕ) [IsIso (orderedMultiplication j)] :
    IsIso (semidirectOrderedMultiplication a j p) := by
  let : IsIso (suffixActionMap c p) := isIso_suffixActionMap c p
  rw [← suffixActionMap_comp_orderedMultiplication a c j heq p]
  exact (asIso (suffixActionMap c p) ≪≫
    tensorIso (asIso (orderedMultiplication j)) (Iso.refl K.X)).isIso_hom

end Langlands.GroupScheme.RelativeRoot
