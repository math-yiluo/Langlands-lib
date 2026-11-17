import Langlands.GroupScheme.Reductive.LocalSplitNegSimple
import Langlands.GroupScheme.Reductive.LocalSplitTargetWordLaws
import Langlands.GroupScheme.Reductive.LocalSplitTargetWeylLaws
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws

/-! # Negative simple-root cell relations with an arbitrary target -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

/-- Target rank-one and negative-simple character identities for cell translation.
The torus map is arbitrary; it need not be closed or fibrewise maximal. -/
structure TargetNegSimpleLaws {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (v : J → (Ga R ⟶ H)) : Prop where
  rankOne : ∀ a ∈ b.support,
    RankOneLaws i (P.coroot a) (v a) (v (P.reflectionPerm a a))
  equivariant : ∀ a ∈ b.support, ∀ (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (x : Γ(Z.left, ⊤)),
    (t ≫ i.hom.hom) * rootPoint (v (P.reflectionPerm a a)) Z x * (t ≫ i.hom.hom)⁻¹ =
      rootPoint (v (P.reflectionPerm a a)) Z
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root (P.reflectionPerm a a)))
          Z t * x)

namespace TargetNegSimpleLaws

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {H : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  {v : J → (Ga R ⟶ H)} {W : ∀ α, SimpleWord P b α}

/-- Negative simple Weyl-family bookkeeping needs only the words and the first rank-one law. -/
theorem rootPoint_weylFamily_neg (hR : TargetNegSimpleLaws i P b v)
    (hW : IsDescendingWords P b W) {a : J} (ha : a ∈ b.support)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (y : Γ((Over.mk s).left, ⊤)) :
    rootPoint (weylFamily P W v (P.reflectionPerm a a)) (Over.mk s) y =
      rootPoint (v (P.reflectionPerm a a)) (Over.mk s) (-y) := by
  have hapos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hneg : ¬ b.IsPos (P.reflectionPerm a a) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) a).mp h hapos
  have hnn : P.reflectionPerm (P.reflectionPerm a a) (P.reflectionPerm a a) = a :=
    P.root.injective (by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
        RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg])
  obtain ⟨h1, h2⟩ := hW.2.2 (P.reflectionPerm a a) hneg
  rw [hnn, (hW.1 a ha).1] at h1
  rw [hnn, (hW.1 a ha).2, (hW.1 a ha).1] at h2
  have hw : weylFamily P W v (P.reflectionPerm a a) = wordConj P v [a] (v a) := by
    unfold weylFamily
    rw [h2, h1]
    rfl
  rw [hw]
  change rootPoint (v a ≫ (H.innerIso (rootWeylPoint P v a)).hom) (Over.mk s) y = _
  rw [rootPoint_comp, GroupScheme.comp_innerIso_hom]
  exact (hR.rankOne a ha).1 (Over.mk s) y

end TargetNegSimpleLaws

namespace TargetNegSimpleProofs

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **Positive-good root points for a base.** Let `b'` be a base, `pos` an enumeration of its
positive roots by increasing `b'`-height and `negb` an enumeration of the other roots. Over a
local test ring, every point of the Weyl family at a `b'`-positive root, with its partner in `H`,
is positive-good for the products of the factors along `pos`. -/
theorem posGood_rootPoint_of_base [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hT : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    (b' : P.Base) {m n : ℕ} (negb : Fin m ≃ {α // ¬ b'.IsPos α})
    (pos : Fin n ≃ {α // b'.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b'.height (pos p : J) ≤ b'.height (pos q : J))
    {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) {β : J} (hβ : b'.IsPos β)
    (x : Γ((Over.mk s).left, ⊤)) :
    PosGood (weylFamily P W u) (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s)
      (rootPoint (weylFamily P W u β) (Over.mk s) x)
      (rootPoint (weylFamily P W u' β) (Over.mk s) x) := by
  classical
  have hWf := hdG.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum b' _
    hWf negb pos
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b'
  have hnegν : ∀ k, coPairing (P.root (negb k : J)) ν < 0 := by
    intro k
    rw [hν]
    have h0 := b'.height_ne_zero (negb k : J)
    have h1 := (negb k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd (by omega)
  have hposν : ∀ k, 0 < coPairing (P.root (pos k : J)) ν := by
    intro k
    rw [hν]
    exact mul_pos hd (pos k).2
  have hmonoν : ∀ p q, p ≤ q →
      coPairing (P.root (pos p : J)) ν ≤ coPairing (P.root (pos q : J)) ν := by
    intro p q hpq
    rw [hν, hν]
    exact mul_le_mul_of_nonneg_left (hmono p q hpq) hd.le
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  have hinj := orderedProduct_pos_injective (i := i) (u := weylFamily P W u)
    (neg := fun k => (negb k : J)) (pos := fun k => (pos k : J)) (Over.mk s)
  have := posGood_rootPoint hinj
    (fun w q c => exists_orderedProduct_mul_rootPoint_eq_pos (neg := fun k => (negb k : J))
      hequiv ν hnegν hposν (hposν q) s w c)
    (fun k l _ x y e he p hp => posComm_coord_eq_zero_of_monotone
      (neg := fun k => (negb k : J)) hequiv ν hnegν hposν hmonoν s k l x y e he p hp)
    (fun k l hkl x y e he => by
      obtain ⟨E, h1, h2⟩ := TargetWordProofs.exists_common_isUnivComm_of_base hdG hT hU b' pos hmono k l hkl
      exact posComm_transfer_of_isUnivComm (i := i) (neg := fun k => (negb k : J)) h1 h2 s
        x y e he) (pos.symm ⟨β, hβ⟩) x
  simpa only [Equiv.apply_symm_apply] using this

/-- **Laws of the negative cell factors.** Over a local test ring, take any enumeration `neg`
of non-positive roots. Every law `N(w) · v_α(c) = N(z)` of the Weyl family of `G`, for products
`N` of non-positive root points in the order `neg` and a non-positive root `α`, holds with the
same coordinates in `H`. -/
theorem negativeLaws [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hT : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    {m : ℕ} (neg : Fin m → J) (hneg : ∀ k, ¬ b.IsPos (neg k))
    {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) {α : J} (hα : ¬ b.IsPos α)
    (c : Γ((Over.mk s).left, ⊤)) (w z : Fin m → Γ((Over.mk s).left, ⊤))
    (h : orderedProduct (weylFamily P W u) neg (Over.mk s) w *
        rootPoint (weylFamily P W u α) (Over.mk s) c =
      orderedProduct (weylFamily P W u) neg (Over.mk s) z) :
    orderedProduct (weylFamily P W u') neg (Over.mk s) w *
        rootPoint (weylFamily P W u' α) (Over.mk s) c =
      orderedProduct (weylFamily P W u') neg (Over.mk s) z := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨b', hb'⟩ := Langlands.LinearAlgebra.exists_base_isPos_iff_not P b
  obtain ⟨e₀, hmono₀⟩ := exists_equiv_monotone (fun x : {α // b'.IsPos α} => b'.height (x : J))
  let pos₀ := (Fintype.equivFin {α // ¬ b'.IsPos α}).symm
  have hWf := hdG.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum b' _
    hWf pos₀ e₀
  have hinj := orderedProduct_pos_injective (i := i) (u := weylFamily P W u)
    (neg := fun k => (pos₀ k : J)) (pos := fun k => (e₀ k : J)) (Over.mk s)
  have hgood' : ∀ β, b'.IsPos β → ∀ x, PosGood (weylFamily P W u) (weylFamily P W u')
      (fun k => (e₀ k : J)) (Over.mk s) (rootPoint (weylFamily P W u β) (Over.mk s) x)
      (rootPoint (weylFamily P W u' β) (Over.mk s) x) :=
    fun β hβ x => posGood_rootPoint_of_base hdG hT hU b' pos₀ e₀ hmono₀ s hβ x
  have hprod : ∀ v : Fin m → Γ((Over.mk s).left, ⊤), PosGood (weylFamily P W u)
      (weylFamily P W u') (fun k => (e₀ k : J)) (Over.mk s)
      (orderedProduct (weylFamily P W u) neg (Over.mk s) v)
      (orderedProduct (weylFamily P W u') neg (Over.mk s) v) :=
    fun v => PosGood.prod_ofFn hinj _ _ fun p => hgood' (neg p) ((hb' _).mpr (hneg p)) (v p)
  obtain ⟨w₀, hw₀⟩ := (hprod w).1 0
  obtain ⟨z₀, hz₀⟩ := (hprod z).1 0
  have hw₀' := (hprod w).2 0 w₀ hw₀
  have hz₀' := (hprod z).2 0 z₀ hz₀
  rw [orderedProduct_zero, one_mul] at hw₀ hz₀ hw₀' hz₀'
  rw [hw₀, hz₀] at h
  rw [hw₀', hz₀']
  exact (hgood' α ((hb' α).mpr hα) c).2 w₀ z₀ h

/-- **Conjugation of the unipotent radical of `a` by `u_{-a}`.** Let the positive roots be
enumerated by increasing height, with `a` at position `pa`. A product of positive cell factors
with zero coordinate at `a`, conjugated by `u_{-a}(x)`, is again such a product, with the same
coordinates in `G` and in `H`. -/
theorem negSimple_conj_orderedProduct [DecidableEq J]
    (hdG : IsNormalSimpleData i P b W u) (hT : TargetWordRelations P b W u')
    (hU : WeylConjugationRelations P b W u u')
    (hR : TargetNegSimpleLaws i' P b u') {a : J} (ha : a ∈ b.support)
    {m n : ℕ} (negb : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J))
    {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (pa : Fin n)
    (hpa : (pos pa : J) = a) (w : Fin n → Γ((Over.mk s).left, ⊤)) (hw : w pa = 0)
    (x : Γ((Over.mk s).left, ⊤)) :
    ∃ w'' : Fin n → Γ((Over.mk s).left, ⊤), w'' pa = 0 ∧
      rootPoint (u (P.reflectionPerm a a)) (Over.mk s) x *
          orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w *
          rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-x) =
        orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w'' ∧
      rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) x *
          orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) w *
          rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) (-x) =
        orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) w'' := by
  have : Finite J := hdG.rootDatum.finite
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hWf := hdG.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum b _
    hWf negb pos
  have hinj := orderedProduct_pos_injective (i := i) (u := weylFamily P W u)
    (neg := fun k => (negb k : J)) (pos := fun k => (pos k : J)) (Over.mk s)
  have hgood : ∀ β, b.IsPos β → ∀ y, PosGood (weylFamily P W u) (weylFamily P W u')
      (fun k => (pos k : J)) (Over.mk s) (rootPoint (weylFamily P W u β) (Over.mk s) y)
      (rootPoint (weylFamily P W u' β) (Over.mk s) y) :=
    fun β hβ y => posGood_rootPoint_of_base hdG hT hU b negb pos hmono s hβ y
  have hva : weylFamily P W u a = u a := hdG.weylFamily_simple ha
  have hva' : weylFamily P W u' a = u' a := weylFamily_simple_of_words (u := u') hdG.words ha
  have hapos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hne : ∀ k, k ≠ pa → P.reflectionPerm a (pos k : J) ≠ a := by
    intro k hk h
    have h' : (pos k : J) = P.reflectionPerm a a := by
      have := congrArg (P.reflectionPerm a) h
      rwa [RootPairing.reflectionPerm_self] at this
    have hk' : b.IsPos (P.reflectionPerm a a) := h' ▸ (pos k).2
    exact (RootPairing.Base.IsPos.neg_iff_not (b := b) a).mp hk' hapos
  have hposr : ∀ k, k ≠ pa → b.IsPos (P.reflectionPerm a (pos k : J)) := fun k hk =>
    (pos k).2.reflectionPerm ha (fun h => hk (pos.injective (Subtype.ext (h.trans hpa.symm))))
  let e₁ : Fin n → J := fun k => if k = pa then a else P.reflectionPerm a (pos k : J)
  have he₁ : ∀ k, b.IsPos (e₁ k) := by
    intro k
    by_cases hk : k = pa
    · simp only [e₁, hk, ↓reduceIte]; exact hapos
    · simp only [e₁, hk, ↓reduceIte]; exact hposr k hk
  have he₁a : ∀ k, e₁ k = a → k = pa := by
    intro k h
    by_contra hk
    simp only [e₁, hk, ↓reduceIte] at h
    exact hne k hk h
  choose κ₁ hκ₁ using fun δ => hU.inv_conj_points ha δ
  choose κ₃ hκ₃ using fun δ => hU.conj_points ha δ
  set nG := G.constantPoint (rootWeylPoint P u a) (Over.mk s) with hnG
  set nH := H.constantPoint (rootWeylPoint P u' a) (Over.mk s) with hnH
  let c₁ : Fin n → Γ((Over.mk s).left, ⊤) := fun k => baseScalar (Over.mk s) (κ₁ (pos k : J) : R) * w k
  have hc₁ : c₁ pa = 0 := by
    show baseScalar (Over.mk s) (κ₁ (pos pa : J) : R) * w pa = 0
    rw [hw, mul_zero]
  -- step 1: conjugation by the inverse Weyl point
  have step1 : ∀ {G₀ : GroupScheme (Spec (CommRingCat.of R))} (v₀ : J → (Ga R ⟶ G₀))
      (n₀ : (Over.mk s) ⟶ G₀.X), (∀ δ x, n₀⁻¹ * rootPoint (v₀ δ) (Over.mk s) x * n₀ =
        rootPoint (v₀ (P.reflectionPerm a δ)) (Over.mk s) (baseScalar (Over.mk s) (κ₁ δ : R) * x)) →
      n₀⁻¹ * orderedProduct v₀ (fun k => (pos k : J)) (Over.mk s) w * n₀ = orderedProduct v₀ e₁ (Over.mk s) c₁ := by
    intro G₀ v₀ n₀ hn₀
    have e : n₀⁻¹ * orderedProduct v₀ (fun k => (pos k : J)) (Over.mk s) w * n₀ =
        n₀⁻¹ * orderedProduct v₀ (fun k => (pos k : J)) (Over.mk s) w * n₀⁻¹⁻¹ := by rw [inv_inv]
    rw [e, orderedProduct, orderedProduct, conj_prod_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun k => ?_)
    by_cases hk : k = pa
    · subst hk
      simp only [e₁, ↓reduceIte, hc₁, rootPoint_zero]
      rw [hw, rootPoint_zero, mul_one, inv_inv, inv_mul_cancel]
    · simp only [e₁, hk, ↓reduceIte, inv_inv]
      exact hn₀ _ (w k)
  have s1G := step1 (weylFamily P W u) nG (fun δ x => (hκ₁ δ).1 (Over.mk s) x)
  have s1H := step1 (weylFamily P W u') nH (fun δ x => (hκ₁ δ).2 (Over.mk s) x)
  -- step 2: conjugation by `u_a`
  have hprod₁ : PosGood (weylFamily P W u) (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s)
      (orderedProduct (weylFamily P W u) e₁ (Over.mk s) c₁) (orderedProduct (weylFamily P W u') e₁ (Over.mk s) c₁) :=
    PosGood.prod_ofFn hinj _ _ fun k => hgood (e₁ k) (he₁ k) (c₁ k)
  obtain ⟨w₂, hw₂G, hw₂H⟩ := (((hgood a hapos (-x)).mul hprod₁).mul (hgood a hapos x)).exists_eq
  have hzero₁ : (fun k => if e₁ k = a then c₁ k else 0) = (0 : Fin n → Γ((Over.mk s).left, ⊤)) := by
    funext k
    by_cases hk : e₁ k = a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), he₁a k hk, hc₁]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]; rfl
  have hw₂ : w₂ pa = 0 := by
    refine hdG.coord_eq_zero_of_simple ha negb pos s
      (e := Fin.cons a (Fin.snoc e₁ a : Fin (n + 1) → J))
      (fun k => Fin.cases hapos (fun k => Fin.lastCases (by simpa using hapos)
        (fun k => by simpa using he₁ k) k) k)
      (Fin.cons (-x) (Fin.snoc c₁ x : Fin (n + 1) → Γ((Over.mk s).left, ⊤))) ?_ w₂ ?_ pa hpa
    · have hf : (fun k : Fin (n + 2) =>
          if (Fin.cons a (Fin.snoc e₁ a : Fin (n + 1) → J) : Fin (n + 2) → J) k = a then
            (Fin.cons (-x) (Fin.snoc c₁ x : Fin (n + 1) → Γ((Over.mk s).left, ⊤)) :
              Fin (n + 2) → Γ((Over.mk s).left, ⊤)) k else 0) =
          Fin.cons (-x) (Fin.snoc (0 : Fin n → Γ((Over.mk s).left, ⊤)) x : Fin (n + 1) → Γ((Over.mk s).left, ⊤)) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · refine Fin.lastCases ?_ (fun k => ?_) k
          · simp
          · simp only [Fin.cons_succ, Fin.snoc_castSucc]
            exact congrFun hzero₁ k
      rw [hf, orderedProduct_cons, orderedProduct_snoc, orderedProduct_zero, one_mul,
        rootPoint_neg, inv_mul_cancel]
    · rw [orderedProduct_cons, orderedProduct_snoc, ← mul_assoc]
      exact hw₂G
  -- step 3: conjugation by the Weyl point
  let c₃ : Fin n → Γ((Over.mk s).left, ⊤) := fun k => baseScalar (Over.mk s) (κ₃ (pos k : J) : R) * w₂ k
  have hc₃ : c₃ pa = 0 := by
    show baseScalar (Over.mk s) (κ₃ (pos pa : J) : R) * w₂ pa = 0
    rw [hw₂, mul_zero]
  have step3 : ∀ {G₀ : GroupScheme (Spec (CommRingCat.of R))} (v₀ : J → (Ga R ⟶ G₀))
      (n₀ : (Over.mk s) ⟶ G₀.X), (∀ δ x, n₀ * rootPoint (v₀ δ) (Over.mk s) x * n₀⁻¹ =
        rootPoint (v₀ (P.reflectionPerm a δ)) (Over.mk s) (baseScalar (Over.mk s) (κ₃ δ : R) * x)) →
      n₀ * orderedProduct v₀ (fun k => (pos k : J)) (Over.mk s) w₂ * n₀⁻¹ = orderedProduct v₀ e₁ (Over.mk s) c₃ := by
    intro G₀ v₀ n₀ hn₀
    rw [orderedProduct, orderedProduct, conj_prod_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun k => ?_)
    by_cases hk : k = pa
    · subst hk
      simp only [e₁, ↓reduceIte, hc₃, rootPoint_zero]
      rw [hw₂, rootPoint_zero, mul_one, mul_inv_cancel]
    · simp only [e₁, hk, ↓reduceIte]
      exact hn₀ _ (w₂ k)
  have s3G := step3 (weylFamily P W u) nG (fun δ x => (hκ₃ δ).1 (Over.mk s) x)
  have s3H := step3 (weylFamily P W u') nH (fun δ x => (hκ₃ δ).2 (Over.mk s) x)
  have hprod₃ : PosGood (weylFamily P W u) (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s)
      (orderedProduct (weylFamily P W u) e₁ (Over.mk s) c₃) (orderedProduct (weylFamily P W u') e₁ (Over.mk s) c₃) :=
    PosGood.prod_ofFn hinj _ _ fun k => hgood (e₁ k) (he₁ k) (c₃ k)
  obtain ⟨w'', hw''G, hw''H⟩ := hprod₃.exists_eq
  have hzero₃ : (fun k => if e₁ k = a then c₃ k else 0) = (0 : Fin n → Γ((Over.mk s).left, ⊤)) := by
    funext k
    by_cases hk : e₁ k = a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), he₁a k hk, hc₃]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]; rfl
  have hw'' : w'' pa = 0 :=
    hdG.coord_eq_zero_of_simple ha negb pos s e₁ he₁ c₃
      (by rw [hzero₃]; exact orderedProduct_zero _ _ _) w'' hw''G pa hpa
  -- rank one: `u_{-a}(y) = n u_a(-y) n⁻¹`
  have hRG : ∀ y, nG * rootPoint (u a) (Over.mk s) y * nG⁻¹ = rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-y) :=
    (hdG.rankOne a ha).1 A s
  have hRH : ∀ y, nH * rootPoint (u' a) (Over.mk s) y * nH⁻¹ =
      rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) (-y) :=
    (hR.rankOne a ha).1 (Over.mk s)
  refine ⟨w'', hw'', ?_, ?_⟩
  · have e1 : rootPoint (u (P.reflectionPerm a a)) (Over.mk s) x = nG * rootPoint (u a) (Over.mk s) (-x) * nG⁻¹ := by
      rw [hRG, neg_neg]
    rw [e1, ← hRG x, ← hw''G, ← s3G, hw₂G.symm.trans (by rw [← s1G]), hva]
    group
  · have e1 : rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) x =
        nH * rootPoint (u' a) (Over.mk s) (-x) * nH⁻¹ := by
      rw [hRH, neg_neg]
    rw [e1, ← hRH x, ← hw''H, ← s3H, hw₂H.symm.trans (by rw [← s1H]), hva']
    group

/-- **Splitting off the simple factor.** A product of positive cell factors (enumerated by
increasing height, with `a` at position `pa`) is `u_a(c) · V` with `c` its coordinate at `a`
and `V` a product with zero coordinate at `a`, with the same coordinates in `G` and `H`. -/
theorem split_simple_orderedProduct [DecidableEq J]
    (hdG : IsNormalSimpleData i P b W u) (hT : TargetWordRelations P b W u')
    (hU : WeylConjugationRelations P b W u u') {a : J} (ha : a ∈ b.support)
    {m n : ℕ} (negb : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J))
    {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (pa : Fin n)
    (hpa : (pos pa : J) = a) (w : Fin n → Γ((Over.mk s).left, ⊤)) :
    ∃ w₁ : Fin n → Γ((Over.mk s).left, ⊤), w₁ pa = 0 ∧
      orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w =
        rootPoint (u a) (Over.mk s) (w pa) *
          orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w₁ ∧
      orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) w =
        rootPoint (u' a) (Over.mk s) (w pa) *
          orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) w₁ := by
  have : Finite J := hdG.rootDatum.finite
  have hWf := hdG.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum b _
    hWf negb pos
  have hinj := orderedProduct_pos_injective (i := i) (u := weylFamily P W u)
    (neg := fun k => (negb k : J)) (pos := fun k => (pos k : J)) (Over.mk s)
  have hgood : ∀ β, b.IsPos β → ∀ y, PosGood (weylFamily P W u) (weylFamily P W u')
      (fun k => (pos k : J)) (Over.mk s) (rootPoint (weylFamily P W u β) (Over.mk s) y)
      (rootPoint (weylFamily P W u' β) (Over.mk s) y) :=
    fun β hβ y => posGood_rootPoint_of_base hdG hT hU b negb pos hmono s hβ y
  have hva : weylFamily P W u a = u a := hdG.weylFamily_simple ha
  have hva' : weylFamily P W u' a = u' a := weylFamily_simple_of_words (u := u') hdG.words ha
  have hapos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hprod : PosGood (weylFamily P W u) (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s)
      (orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w)
      (orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) w) :=
    PosGood.prod_ofFn hinj _ _ fun k => hgood (pos k : J) (pos k).2 (w k)
  obtain ⟨w₁, hG, hH⟩ := ((hgood a hapos (-(w pa))).mul hprod).exists_eq
  have hw₁ : w₁ pa = 0 := by
    refine hdG.coord_eq_zero_of_simple ha negb pos s
      (e := Fin.cons a (fun k => (pos k : J)))
      (fun k => Fin.cases hapos (fun k => by simpa using (pos k).2) k)
      (Fin.cons (-(w pa)) w) ?_ w₁ ?_ pa hpa
    · have hf : (fun k : Fin (n + 1) =>
          if (Fin.cons a (fun k => (pos k : J)) : Fin (n + 1) → J) k = a then
            (Fin.cons (-(w pa)) w : Fin (n + 1) → Γ((Over.mk s).left, ⊤)) k else 0) =
          Fin.cons (-(w pa)) (fun k => if (pos k : J) = a then w k else 0) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · simp only [Fin.cons_succ]
      rw [hf, orderedProduct_cons,
        orderedProduct_eq_rootPoint_of_eq_zero _ _ _ _ pa (fun l hl => by
          have : (pos l : J) ≠ a := fun h => hl (pos.injective (Subtype.ext (h.trans hpa.symm)))
          simp only [this, ↓reduceIte]),
        hpa, ite_eq_left_of_eq_true _ _ (eq_true rfl), rootPoint_neg, inv_mul_cancel]
    · rw [orderedProduct_cons]
      exact hG
  refine ⟨w₁, hw₁, ?_, ?_⟩
  · rw [← hG, ← hva, rootPoint_neg]
    group
  · rw [← hH, ← hva', rootPoint_neg]
    group

/-- **Transfer of right translation by `u_{-a}(-1)`.** -/
theorem negSimple_transfer [DecidableEq J] (hdG : IsNormalSimpleData i P b W u)
    (hT : TargetWordRelations P b W u') (hU : WeylConjugationRelations P b W u u')
    (hR : TargetNegSimpleLaws i' P b u')
    {a : J} (ha : a ∈ b.support) (hBG : RankOneBruhat i P u a)
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J))
    {A : Type u} [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (x y : Over.mk s ⟶ cellObj R I m n)
    (hxy : (x ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
        rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) =
      y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) :
    (x ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) *
        rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) (-1) =
      y ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J)) := by
  have hBH : RankOneBruhat i' P u' a := by
    intro B _ s x y d hd
    exact (hR.rankOne a ha).2.2.2 (Over.mk s) x y d hd
  have : Finite J := hdG.rootDatum.finite
  have hapos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hnegpos : ¬ b.IsPos (P.reflectionPerm a a) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) a).mp h hapos
  have hWf := hdG.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum b _
    hWf neg pos
  have hmonoG : Mono (cellMap i (weylFamily P W u) (fun k => (neg k : J))
      (fun k => (pos k : J))) := Over.mono_of_mono_left _
  have hinj := orderedProduct_pos_injective (i := i) (u := weylFamily P W u)
    (neg := fun k => (neg k : J)) (pos := fun k => (pos k : J)) (Over.mk s)
  have hgood : ∀ β, b.IsPos β → ∀ y, PosGood (weylFamily P W u) (weylFamily P W u')
      (fun k => (pos k : J)) (Over.mk s) (rootPoint (weylFamily P W u β) (Over.mk s) y)
      (rootPoint (weylFamily P W u' β) (Over.mk s) y) :=
    fun β hβ y => posGood_rootPoint_of_base hdG hT hU b neg pos hmono s hβ y
  have hva : weylFamily P W u a = u a := hdG.weylFamily_simple ha
  have hva' : weylFamily P W u' a = u' a := weylFamily_simple_of_words (u := u') hdG.words ha
  set pa := pos.symm ⟨a, hapos⟩ with hpadef
  have hpa : (pos pa : J) = a := by rw [hpadef, Equiv.apply_symm_apply]
  obtain ⟨w₁, hw₁, hsG, hsH⟩ :=
    split_simple_orderedProduct hdG hT hU ha neg pos hmono s pa hpa (posCoord x)
  obtain ⟨w₂, -, hcG, hcH⟩ :=
    negSimple_conj_orderedProduct hdG hT hU hR ha neg pos hmono s pa hpa w₁ hw₁ 1
  set c := posCoord x pa with hcdef
  by_cases hc : IsUnit (1 - c)
  · -- the unit case: the rank-one Bruhat relation
    set d := hc.unit with hddef
    have hd : (d : Γ((Over.mk s).left, ⊤)) = 1 + c * (-1) := by
      rw [hddef, IsUnit.unit_spec]; ring
    have hbG := hBG A s c (-1) d hd
    have hbH := hBH A s c (-1) d hd
    set χ := torusChar (P.root (P.reflectionPerm a a)) (Over.mk s) (torusCoord x) with hχ
    have heG : (torusCoord x ≫ i.hom.hom) *
        rootPoint (u (P.reflectionPerm a a)) (Over.mk s)
          ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * -1) * (torusCoord x ≫ i.hom.hom)⁻¹ =
        rootPoint (u (P.reflectionPerm a a)) (Over.mk s)
          (χ * ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * -1)) :=
      (hdG.param a ha).2.equivariant _ _ _
    have heH : (torusCoord x ≫ i'.hom.hom) *
        rootPoint (u' (P.reflectionPerm a a)) (Over.mk s)
          ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * -1) * (torusCoord x ≫ i'.hom.hom)⁻¹ =
        rootPoint (u' (P.reflectionPerm a a)) (Over.mk s)
          (χ * ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * -1)) :=
      hR.equivariant a ha _ _ _
    -- the negative factor
    obtain ⟨z, hzG⟩ := hdG.exists_negProduct_mul neg s (negCoord x) hnegpos
      (-(χ * ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * -1)))
    have hzH := negativeLaws hdG hT hU (fun k => (neg k : J)) (fun k => (neg k).2) s hnegpos
      _ (negCoord x) z hzG
    rw [hdG.rootPoint_weylFamily_neg ha, neg_neg] at hzG
    rw [hR.rootPoint_weylFamily_neg hdG.words ha, neg_neg] at hzH
    -- the positive factor
    obtain ⟨w₃, hw₃G, hw₃H⟩ := ((hgood a hapos ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * c)).mul
      (PosGood.prod_ofFn hinj _ _ fun k => hgood (pos k : J) (pos k).2 (w₂ k))).exists_eq
    rw [hva] at hw₃G
    rw [hva'] at hw₃H
    have hG := cell_mul_negSimple_eq i (weylFamily P W u) (u a) (u (P.reflectionPerm a a))
      (fun k => (neg k : J)) (fun k => (pos k : J)) x c χ w₁ w₂ w₃ z d (P.coroot a) hsG hcG hbG
      heG hzG hw₃G
    have hH := cell_mul_negSimple_eq i' (weylFamily P W u') (u' a) (u' (P.reflectionPerm a a))
      (fun k => (neg k : J)) (fun k => (pos k : J)) x c χ w₁ w₂ w₃ z d (P.coroot a) hsH hcH hbH
      heH hzH hw₃H
    have hy := (cancel_mono _).mp (hxy.symm.trans hG)
    rw [hH, hy]
  · -- the non-unit case cannot occur: pass to the residue field
    exfalso
    set K := IsLocalRing.ResidueField A
    have : Infinite K := infinite_of_isSepClosed K
    obtain ⟨l, hl0, hl4⟩ := exists_ne_zero_pow_four_ne_one K
    set π := IsLocalRing.residue A
    set sK := Spec.map (CommRingCat.ofHom π) ≫ s with hsK
    let f : Over.mk sK ⟶ Over.mk s := specHom π rfl
    set gK := (Scheme.ΓSpecIso (CommRingCat.of K)).inv with hgK
    let l₀ : (Γ((Over.mk sK).left, ⊤))ˣ := Units.map gK.hom.toMonoidHom (Units.mk0 l hl0)
    have hl₀ : ((l₀ : Γ((Over.mk sK).left, ⊤))) ^ 4 ≠ 1 := by
      intro h
      apply hl4
      have h' : gK (l ^ 4) = gK 1 := by rw [map_pow, map_one]; exact h
      exact (ConcreteCategory.injective_of_mono_of_preservesPullback gK) h'
    -- pull back the relation
    have hxyK := congrArg (fun g => f ≫ g) hxy
    simp only [MonObj.comp_mul, ← Category.assoc, comp_rootPoint, map_neg, map_one] at hxyK
    -- the coordinate at `a` becomes `1`
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : A, (Scheme.ΓSpecIso (CommRingCat.of A)).inv c₀ = c :=
      ⟨_, Iso.hom_inv_id_apply _ _⟩
    have hc1 : posCoord (f ≫ x) pa = 1 := by
      rw [posCoord_comp]
      change (specHom π (sL := s) rfl).left.appTop (posCoord x pa) = 1
      rw [← hcdef, ← hc₀]
      have key : (specHom π (sL := s) rfl).left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c₀) =
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv (π c₀) := specMap_appTop_ΓSpecIso_inv π c₀
      rw [key]
      have hres : π c₀ = 1 := by
        have hnu : ¬ IsUnit (1 - c₀) := by
          intro hu₀
          apply hc
          have e : (1 : Γ((Over.mk s).left, ⊤)) - c =
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv (1 - c₀) := by
            rw [map_sub, map_one, hc₀]
          rw [e]
          exact hu₀.map _
        have := (IsLocalRing.residue_eq_zero_iff (1 - c₀)).mpr
          ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
        rw [map_sub, map_one, sub_eq_zero] at this
        exact this.symm
      rw [hres, map_one]
    obtain ⟨w₁', hw₁', hs'G, -⟩ :=
      split_simple_orderedProduct hdG hT hU ha neg pos hmono sK pa hpa (posCoord (f ≫ x))
    obtain ⟨w₂', -, hc'G, -⟩ :=
      negSimple_conj_orderedProduct hdG hT hU hR ha neg pos hmono sK pa hpa w₁' hw₁' 1
    rw [hc1] at hs'G
    obtain ⟨w₃', hw₃'⟩ := hdG.exists_posProduct_mul_list neg pos sK
      ((List.ofFn fun k => ((pos k : J), w₂' k))) (fun p hp => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
        exact (pos k).2) (fun k => if k = pa then -1 else 0)
    rw [← orderedProduct_eq_list_prod,
      orderedProduct_eq_rootPoint_of_eq_zero _ _ _ _ pa (fun l hl => by simp [hl]),
      ite_eq_left_of_eq_true _ _ (eq_true rfl), hpa, hva] at hw₃'
    refine hdG.false_of_weylPoint_mem ha neg pos sK l₀ hl₀ (negCoord (f ≫ x))
      (torusCoord (f ≫ x)) w₃' (f ≫ y) ?_
    rw [← hxyK, comp_cellMap, cellPoint, hs'G, ← hw₃']
    have hV : orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk sK) w₁' *
        rootPoint (u (P.reflectionPerm a a)) (Over.mk sK) (-1) =
        rootPoint (u (P.reflectionPerm a a)) (Over.mk sK) (-1) *
          orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk sK) w₂' := by
      rw [← hc'G, rootPoint_neg]
      group
    have hr := hdG.rootPoint_one_mul_neg ha sK
    symm
    calc _ = orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk sK)
            (negCoord (f ≫ x)) * (torusCoord (f ≫ x) ≫ i.hom.hom) *
          rootPoint (u a) (Over.mk sK) 1 *
          (orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk sK) w₁' *
            rootPoint (u (P.reflectionPerm a a)) (Over.mk sK) (-1)) := by group
      _ = orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk sK)
            (negCoord (f ≫ x)) * (torusCoord (f ≫ x) ≫ i.hom.hom) *
          (rootPoint (u a) (Over.mk sK) 1 *
            rootPoint (u (P.reflectionPerm a a)) (Over.mk sK) (-1)) *
          orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk sK) w₂' := by
          rw [hV]; group
      _ = _ := by rw [hr]; group


end TargetNegSimpleProofs

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- Negative-simple cell relations need source geometry and exact target map laws. -/
def LocalSplitTargetNegSimpleStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I J : Type u) [Fintype I] [DecidableEq I]
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (G H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (b : P.Base) (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) (v : J → (Ga R ⟶ H)),
    IsNormalSimpleData i P b W u → TargetWordRelations P b W v →
    WeylConjugationRelations P b W u v → TargetNegSimpleLaws i' P b v →
    (∀ a ∈ b.support, RankOneBruhat i P u a) →
    ∀ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
    (∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) →
    NegSimpleRelations P
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (cellMap i' (weylFamily P W v) (fun k => (neg k : J)) (fun k => (pos k : J))) b u v

/-- The arbitrary-target negative-simple reduction holds in every universe. -/
theorem localSplitTargetNegSimple : LocalSplitTargetNegSimpleStatement.{u} := by
  classical
  intro R _ _ I J _ _ P G H _ i i' b W u v hd hT hU hR hBG m n neg pos hmono
    A _ _ _ s x y a ha hxy
  exact TargetNegSimpleProofs.negSimple_transfer hd hT hU hR ha (hBG a ha)
    neg pos hmono s x y hxy

end Langlands.GroupScheme
