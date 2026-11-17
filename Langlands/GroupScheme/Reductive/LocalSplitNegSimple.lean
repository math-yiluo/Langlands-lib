import Langlands.GroupScheme.Reductive.LocalSplitNegativeLaws
import Langlands.GroupScheme.Reductive.LocalSplitRankOneBruhatStatement

/-! # Right translation of big-cell points by negative simple root points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section FieldFacts

/-- A separably closed field is infinite. -/
theorem infinite_of_isSepClosed (K : Type*) [Field K] [IsSepClosed K] : Infinite K := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite K
  have hn : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  have hn' : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (1 : K) (-1) (-1) hn hn'
    (by norm_num)
  rw [FiniteField.pow_card] at hx
  have : (-1 : K) = 0 := by linear_combination hx
  exact one_ne_zero (neg_eq_zero.mp this)

/-- An infinite field has a nonzero element whose fourth power is not `1`. -/
theorem exists_ne_zero_pow_four_ne_one (K : Type*) [Field K] [Infinite K] :
    ∃ l : K, l ≠ 0 ∧ l ^ 4 ≠ 1 := by
  classical
  obtain ⟨l, hl⟩ := Infinite.exists_notMem_finset
    ((Polynomial.X ^ 4 - Polynomial.C (1 : K)).roots.toFinset ∪ {0})
  refine ⟨l, fun h => hl (by simp [h]), fun h => hl ?_⟩
  rw [Finset.mem_union, Multiset.mem_toFinset]
  left
  rw [Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero (by norm_num) _)]
  simp [h]

end FieldFacts

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Weights

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- Pulling back an equality of ordered products along a ring map. -/
theorem orderedProduct_specHom {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {s' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    (hs : Spec.map (CommRingCat.ofHom κ) ≫ s = s') {r : ℕ} (e : Fin r → J) (c : Fin r → L)
    (w : Fin n → L)
    (h : orderedProduct u e (Over.mk s)
        (fun k => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (c k)) =
      orderedProduct u pos (Over.mk s) (fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (w q))) :
    orderedProduct u e (Over.mk s')
        (fun k => (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ (c k))) =
      orderedProduct u pos (Over.mk s')
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ (w q))) := by
  have key : ∀ a : L, (specHom κ hs).left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ a) := specMap_appTop_ΓSpecIso_inv κ
  have h' := congrArg (fun g => specHom κ hs ≫ g) h
  simp only [comp_orderedProduct, key] at h'
  exact h'

/-- **Vanishing of coordinates by weights.** Let `ω` be a cocharacter. Take an ordered product
of root points along `e`, all of whose characters pair non-negatively with `ω`, such that the
factors of weight zero alone multiply to `1`. Written as a product of positive cell factors, it
has zero coordinate at every position whose character pairs non-positively with `ω`. -/
theorem coord_eq_zero_of_weight [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (ω : I → ℤ) {r : ℕ} (e : Fin r → J)
    (he : ∀ k, 0 < coPairing (ch (e k)) ν) (heω : ∀ k, 0 ≤ coPairing (ch (e k)) ω)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (c : Fin r → B) (w : Fin n → B)
    (h1 : orderedProduct u e (Over.mk s) (fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv
      (if coPairing (ch (e k)) ω = 0 then c k else 0)) = 1)
    (h : orderedProduct u e (Over.mk s)
        (fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv (c k)) =
      orderedProduct u pos (Over.mk s) (fun q => (Scheme.ΓSpecIso (CommRingCat.of B)).inv (w q)))
    (p : Fin n) (hp : coPairing (ch (pos p)) ω ≤ 0) : w p = 0 := by
  classical
  let dk : Fin r → ℕ := fun k => (coPairing (ch (e k)) ω).toNat
  have hdk : ∀ k, coPairing (ch (e k)) ω = dk k :=
    fun k => (Int.toNat_of_nonneg (heω k)).symm
  obtain ⟨dp, hdp⟩ : ∃ d : ℕ, coPairing (ch (pos p)) ω = -d :=
    ⟨(-coPairing (ch (pos p)) ω).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  -- the deformation over `B[X]`, scaling the `k`-th coordinate by `X ^ dk k`
  obtain ⟨z, hz⟩ := exists_orderedProduct_eq_pos_of_ring (pos := pos) hu ν hneg e he
    (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) ≫ s)
    (fun k => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).inv
      (Polynomial.C (c k) * Polynomial.X ^ dk k))
  obtain ⟨z0, rfl⟩ : ∃ z0 : Fin n → Polynomial B,
      (fun q => ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).inv (z0 q) :
        Γ((Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) ≫
          s)).left, ⊤))) = z :=
    ⟨fun q => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).hom (z q),
      funext fun q => Iso.hom_inv_id_apply _ _⟩
  -- at `X = 0` the deformation is trivial
  have h0 : ∀ q, Polynomial.evalRingHom (0 : B) (z0 q) = 0 := by
    have H := orderedProduct_specHom (Polynomial.evalRingHom (0 : B)) rfl e _ _ hz
    have h1z : orderedProduct u e (Over.mk s) (fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv
        (if coPairing (ch (e k)) ω = 0 then c k else 0)) =
        orderedProduct u pos (Over.mk s)
          (fun q => (Scheme.ΓSpecIso (CommRingCat.of B)).inv ((0 : Fin n → B) q)) := by
      rw [h1]
      simp only [Pi.zero_apply, map_zero]
      exact (orderedProduct_zero u pos _).symm
    have H1 := orderedProduct_specHom ((Polynomial.evalRingHom (0 : B)).comp Polynomial.C)
      (specMap_comp_specMap _ _ s).symm e _ _ h1z
    have hfun : (fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv
        (Polynomial.evalRingHom (0 : B) (Polynomial.C (c k) * Polynomial.X ^ dk k))) =
        fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv
          (((Polynomial.evalRingHom (0 : B)).comp Polynomial.C)
            (if coPairing (ch (e k)) ω = 0 then c k else 0)) := by
      funext k
      congr 1
      by_cases hk : dk k = 0
      · have : coPairing (ch (e k)) ω = 0 := by have := hdk k; omega
        simp [hk, this]
      · have : coPairing (ch (e k)) ω ≠ 0 := by have := hdk k; omega
        simp [hk, this]
    rw [hfun, H1] at H
    have := coord_eq_of_orderedProduct_eq (i := i) (neg := neg) _ H
    intro q
    have hq := congrFun this q
    simp only [Pi.zero_apply, map_zero] at hq
    exact hq.symm
  -- Laurent polynomials, where `X` becomes a unit
  have H6 := orderedProduct_specHom (Polynomial.C : B →+* Polynomial B) (s := s) rfl e c w h
  have HzL := orderedProduct_specHom (Polynomial.toLaurent (R := B)) rfl e _ _ hz
  have H6L := orderedProduct_specHom (Polynomial.toLaurent (R := B)) rfl e _ _ H6
  set Z := Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := B))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) ≫ s) with hZ
  set gm := (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial B))).inv with hgm
  let uT : (Γ(Z.left, ⊤))ˣ :=
    Units.map gm.hom.toMonoidHom (LaurentPolynomial.isUnit_T (R := B) 1).unit
  have huT : ((uT : (Γ(Z.left, ⊤))ˣ) : Γ(Z.left, ⊤)) = gm (LaurentPolynomial.T 1) := rfl
  have hpow : ∀ d : ℕ, (gm (LaurentPolynomial.T 1)) ^ d = gm (LaurentPolynomial.T (d : ℤ)) :=
    fun d => by rw [← map_pow, LaurentPolynomial.T_pow, mul_one]
  have hmul : ∀ a b : LaurentPolynomial B,
      ((gm a : Γ(Z.left, ⊤)) * (gm b : Γ(Z.left, ⊤))) = gm (a * b) :=
    fun a b => (map_mul _ a b).symm
  have Hc := congrArg (fun g => (cocharPoint ω Z uT ≫ i.hom.hom) * g *
    (cocharPoint ω Z uT ≫ i.hom.hom)⁻¹) H6L
  simp only at Hc
  rw [torus_mul_orderedProduct_mul_inv hu, torus_mul_orderedProduct_mul_inv hu] at Hc
  have hL : (fun k => @HMul.hMul Γ(Z.left, ⊤) Γ(Z.left, ⊤) Γ(Z.left, ⊤) _
      (torusChar (ch (e k)) Z (cocharPoint ω Z uT))
      (gm (Polynomial.toLaurent (Polynomial.C (c k))))) =
      fun k => gm (Polynomial.toLaurent (Polynomial.C (c k) * Polynomial.X ^ dk k)) := by
    funext k
    rw [torusChar_cocharPoint_of_eq (hdk k), huT, hpow, hmul]
    congr 1
    rw [Polynomial.toLaurent_C_mul_X_pow, Polynomial.toLaurent_C]
    ring
  rw [hL, HzL] at Hc
  have hinj := orderedProduct_pos_injective (i := i) (neg := neg) (u := u) (pos := pos) Z Hc
  have hpq := congrFun hinj p
  simp only at hpq
  -- divide by the character at `p`
  have hinv := inverse_torusChar_cocharPoint_of_eq hdp Z uT
  have hw : (gm (Polynomial.toLaurent (Polynomial.C (w p))) : Γ(Z.left, ⊤)) =
      gm (Polynomial.toLaurent (Polynomial.X ^ dp * z0 p)) := by
    have e1 : (gm (Polynomial.toLaurent (Polynomial.C (w p))) : Γ(Z.left, ⊤)) =
        Ring.inverse (torusChar (ch (pos p)) Z (cocharPoint ω Z uT)) *
          (@HMul.hMul Γ(Z.left, ⊤) Γ(Z.left, ⊤) Γ(Z.left, ⊤) _
            (torusChar (ch (pos p)) Z (cocharPoint ω Z uT))
            (gm (Polynomial.toLaurent (Polynomial.C (w p))))) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_torusChar _ _ _), one_mul]
    rw [e1, ← hpq, hinv, huT, hpow, hmul]
    congr 1
    rw [map_mul, Polynomial.toLaurent_X_pow]
  have hw' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial B))).hom hw
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at hw'
  have hw'' := Polynomial.toLaurent_injective hw'
  have := congrArg (Polynomial.eval (0 : B)) hw''
  rw [Polynomial.eval_C] at this
  rw [this, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  have hz0 := h0 p
  rw [Polynomial.coe_evalRingHom] at hz0
  rw [hz0, mul_zero]

/-- An ordered product as the product of a list of root points. -/
theorem orderedProduct_eq_list_prod {r : ℕ} (e : Fin r → J) (Z : Over (Spec (CommRingCat.of R)))
    (c : Fin r → Γ(Z.left, ⊤)) :
    orderedProduct u e Z c =
      ((List.ofFn fun k => (e k, c k)).map fun p => rootPoint (u p.1) Z p.2).prod := by
  rw [orderedProduct, List.map_ofFn]
  rfl

/-- The inverse of an ordered product as the product of a list of root points. -/
theorem orderedProduct_inv_eq_list_prod {r : ℕ} (e : Fin r → J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    (orderedProduct u e Z c)⁻¹ =
      ((List.ofFn fun k => (e k, -c k)).reverse.map fun p => rootPoint (u p.1) Z p.2).prod := by
  have hl : (List.ofFn fun k => rootPoint (u (e k)) Z (c k)).map (fun x => x⁻¹) =
      (List.ofFn fun k => (e k, -c k)).map fun p => rootPoint (u p.1) Z p.2 := by
    rw [List.map_ofFn, List.map_ofFn]
    exact List.ofFn_inj.mpr (funext fun k => (rootPoint_neg _ _ _).symm)
  rw [orderedProduct, List.prod_inv_reverse, hl, List.map_reverse]

/-- Right translation of a product of positive cell factors by a list of root points whose
characters pair positively with `ν`. -/
theorem exists_orderedProduct_mul_list [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (L : List (J × Γ((Over.mk s).left, ⊤))) (hL : ∀ p ∈ L, 0 < coPairing (ch p.1) ν)
    (w : Fin n → Γ((Over.mk s).left, ⊤)) :
    ∃ z, orderedProduct u pos (Over.mk s) w *
        (L.map fun p => rootPoint (u p.1) (Over.mk s) p.2).prod =
      orderedProduct u pos (Over.mk s) z := by
  induction L generalizing w with
  | nil => exact ⟨w, by simp⟩
  | cons p L ih =>
    obtain ⟨z₁, hz₁⟩ := exists_orderedProduct_mul_rootPoint_eq_pos hu ν hneg hpos
      (hL p List.mem_cons_self) s w p.2
    obtain ⟨z, hz⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) z₁
    exact ⟨z, by rw [List.map_cons, List.prod_cons, ← mul_assoc, hz₁, hz]⟩

/-- Left multiplication of a cell point by a torus point. -/
theorem torus_mul_comp_cellMap (hu : TorusEquivariant i ch u)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n)
    (τ : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (τ ≫ i.hom.hom) * (x ≫ cellMap i u neg pos) =
      mkCellPoint Z (fun k => torusChar (ch (neg k)) Z τ * negCoord x k)
        (splitTorus.pointsEquiv I Z (τ * torusCoord x)) (posCoord x) ≫ cellMap i u neg pos := by
  have hT : torusCoord (mkCellPoint Z (fun k => torusChar (ch (neg k)) Z τ * negCoord x k)
      (splitTorus.pointsEquiv I Z (τ * torusCoord x)) (posCoord x)) = τ * torusCoord x :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint])
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, negCoord_mkCellPoint,
    posCoord_mkCellPoint, hT, MonObj.mul_comp, ← torus_mul_orderedProduct_mul_inv hu]
  group

/-- Right multiplication of a cell point by a torus point. -/
theorem comp_cellMap_mul_torus' (hu : TorusEquivariant i ch u)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n)
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (x ≫ cellMap i u neg pos) * (t ≫ i.hom.hom) =
      mkCellPoint Z (negCoord x) (splitTorus.pointsEquiv I Z (torusCoord x * t))
        (fun k => Ring.inverse (torusChar (ch (pos k)) Z t) * posCoord x k) ≫
        cellMap i u neg pos :=
  comp_cellMap_mul_torus hu x _ t (negCoord_mkCellPoint _ _ _ _)
    ((splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint]))
    (posCoord_mkCellPoint _ _ _ _)

end Weights

section Conjugation

theorem orderedProduct_cons {R : Type u} [CommRing R] {J : Type u}
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (u : J → (Ga R ⟶ G)) {r : ℕ} (e : Fin r → J) (α : J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) (a : Γ(Z.left, ⊤)) :
    orderedProduct u (Fin.cons α e : Fin (r + 1) → J) Z (Fin.cons a c) =
      rootPoint (u α) Z a * orderedProduct u e Z c := by
  simp only [orderedProduct, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

theorem conj_prod_ofFn {M : Type*} [Group M] (g : M) {r : ℕ} (f : Fin r → M) :
    g * (List.ofFn f).prod * g⁻¹ = (List.ofFn fun k => g * f k * g⁻¹).prod := by
  rw [← MulAut.conj_apply, map_list_prod, List.map_ofFn]
  rfl

end Conjugation

section CellComputation

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}

/-- **Right translation by `u_{-a}(-1)`, by a computation in one group.** Let a cell point `x`
have positive factor `u_a(c) · V'`, let `u_{-a}(1) V' u_{-a}(-1) = V''`, and let the rank-one
relation `u_a(c) u_{-a}(-1) = u_{-a}(d⁻¹ · (-1)) a^∨(d) u_a(d⁻¹ c)` hold. If the torus factor
of `x` moves `u_{-a}(d⁻¹ · (-1))` to `u_{-a}(χ d⁻¹ · (-1))`, which the negative factor
absorbs, and `u_a(d⁻¹ c) V''` is a positive factor, then the translate of `x` is the cell
point with these factors. -/
theorem cell_mul_negSimple_eq {G₀ : GroupScheme (Spec (CommRingCat.of R))}
    (i₀ : splitTorus (Spec (CommRingCat.of R)) I ⟶ G₀) (v₀ : J → (Ga R ⟶ G₀))
    (ua una : Ga R ⟶ G₀) {m n : ℕ} (negf : Fin m → J) (posf : Fin n → J)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) (c χ : Γ(Z.left, ⊤))
    (w₁ w₂ w₃ : Fin n → Γ(Z.left, ⊤)) (z : Fin m → Γ(Z.left, ⊤)) (d : (Γ(Z.left, ⊤))ˣ)
    (cor : I → ℤ)
    (hsplit : orderedProduct v₀ posf Z (posCoord x) =
      rootPoint ua Z c * orderedProduct v₀ posf Z w₁)
    (hconj : rootPoint una Z 1 * orderedProduct v₀ posf Z w₁ * rootPoint una Z (-1) =
      orderedProduct v₀ posf Z w₂)
    (hbruhat : rootPoint ua Z c * rootPoint una Z (-1) =
      rootPoint una Z ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * -1) * (cocharPoint cor Z d ≫ i₀.hom.hom) *
        rootPoint ua Z ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * c))
    (hequiv : (torusCoord x ≫ i₀.hom.hom) * rootPoint una Z ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * -1) *
        (torusCoord x ≫ i₀.hom.hom)⁻¹ = rootPoint una Z (χ * ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * -1)))
    (hneg : orderedProduct v₀ negf Z (negCoord x) *
        rootPoint una Z (χ * ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * -1)) = orderedProduct v₀ negf Z z)
    (hpos : rootPoint ua Z ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * c) * orderedProduct v₀ posf Z w₂ =
      orderedProduct v₀ posf Z w₃) :
    (x ≫ cellMap i₀ v₀ negf posf) * rootPoint una Z (-1) =
      mkCellPoint Z z (splitTorus.pointsEquiv I Z (torusCoord x * cocharPoint cor Z d)) w₃ ≫
        cellMap i₀ v₀ negf posf := by
  have hT : torusCoord (mkCellPoint Z z
      (splitTorus.pointsEquiv I Z (torusCoord x * cocharPoint cor Z d)) w₃) =
      torusCoord x * cocharPoint cor Z d :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint])
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, negCoord_mkCellPoint,
    posCoord_mkCellPoint, hT, MonObj.mul_comp, ← hneg, ← hpos, hsplit, ← hequiv, ← hconj]
  have hl : rootPoint una Z ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * -1) =
      rootPoint ua Z c * rootPoint una Z (-1) *
        (rootPoint ua Z ((d⁻¹ : (Γ(Z.left, ⊤))ˣ) * c))⁻¹ *
        (cocharPoint cor Z d ≫ i₀.hom.hom)⁻¹ := by
    rw [hbruhat]
    group
  rw [hl, rootPoint_neg]
  group

end CellComputation

section NegSimpleConj

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [IsAffineHom H.X.hom] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- A cocharacter vanishing on a simple root `a` and positive on the other positive roots:
its pairing with a root `α` is a positive multiple of `ht(α) + ht(s_a α)`. -/
theorem IsNormalSimpleData.exists_weight (hd : IsNormalSimpleData i P b W u) {a : J}
    (ha : a ∈ b.support) :
    ∃ ω : I → ℤ, ∀ α, b.IsPos α →
      (coPairing (P.root α) ω = 0 ↔ α = a) ∧ 0 ≤ coPairing (P.root α) ω := by
  classical
  have : Finite J := hd.rootDatum.finite
  have : P.IsReduced := hd.rootDatum.isReduced
  obtain ⟨d, hd0, ν, hν⟩ := exists_coPairing_eq_height P b
  refine ⟨fun j => 2 * ν j - coPairing (P.root a) ν * P.coroot a j, fun α hα => ?_⟩
  have e1 : coPairing (P.root α) (fun j => 2 * ν j - coPairing (P.root a) ν * P.coroot a j) =
      2 * coPairing (P.root α) ν - coPairing (P.root a) ν * coPairing (P.root α) (P.coroot a) := by
    simp only [coPairing, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
  have hval : coPairing (P.root α) (fun j => 2 * ν j - coPairing (P.root a) ν * P.coroot a j) =
      d * (b.height α + b.height (P.reflectionPerm a α)) := by
    rw [e1, hν, hν, coPairing_root_coroot hd.rootDatum,
      RootPairing.Base.height_one_of_mem_support ha, height_reflectionPerm_of_mem P ha α,
      pairing_eq_of_pairingIn rfl]
    ring
  rw [hval]
  have h1 : 0 < b.height α := hα
  by_cases hαa : α = a
  · subst hαa
    rw [height_reflectionPerm_of_mem P ha α, RootPairing.pairing_same,
      RootPairing.Base.height_one_of_mem_support ha]
    simp
  · have h2 : 0 < b.height (P.reflectionPerm a α) := hα.reflectionPerm ha hαa
    refine ⟨⟨fun h => ?_, fun h => absurd h hαa⟩, by nlinarith⟩
    nlinarith

/-- **Vanishing of the coordinate at a simple root.** In an ordered product of positive root
points of the Weyl family whose factors at the simple root `a` alone multiply to `1`, written as
a product of positive cell factors, the coordinate at `a` vanishes. -/
theorem IsNormalSimpleData.coord_eq_zero_of_simple [DecidableEq J]
    (hd : IsNormalSimpleData i P b W u) {a : J} (ha : a ∈ b.support) {m n : ℕ} (negb : Fin m ≃ {α // ¬ b.IsPos α})
    (pos : Fin n ≃ {α // b.IsPos α}) {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) {r : ℕ} (e : Fin r → J)
    (he : ∀ k, b.IsPos (e k)) (c : Fin r → Γ((Over.mk s).left, ⊤))
    (h1 : orderedProduct (weylFamily P W u) e (Over.mk s)
      (fun k => if e k = a then c k else 0) = 1)
    (w : Fin n → Γ((Over.mk s).left, ⊤))
    (h : orderedProduct (weylFamily P W u) e (Over.mk s) c =
      orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w)
    (p : Fin n) (hp : (pos p : J) = a) : w p = 0 := by
  classical
  obtain ⟨ω, hω⟩ := hd.exists_weight ha
  have hWf := hd.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hd.reductive hd.maximal hd.rootDatum b _
    hWf negb pos
  obtain ⟨d, hd0, ν, hν⟩ := exists_coPairing_eq_height P b
  have hnegν : ∀ k, coPairing (P.root (negb k : J)) ν < 0 := by
    intro k
    rw [hν]
    have h0 := b.height_ne_zero (negb k : J)
    have h1 := (negb k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd0 (by omega)
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  obtain ⟨c0, rfl⟩ : ∃ c0 : Fin r → B,
      (fun k => ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (c0 k) : Γ((Over.mk s).left, ⊤))) =
        c :=
    ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).hom (c k),
      funext fun k => Iso.hom_inv_id_apply _ _⟩
  obtain ⟨w0, rfl⟩ : ∃ w0 : Fin n → B,
      (fun k => ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (w0 k) : Γ((Over.mk s).left, ⊤))) =
        w :=
    ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).hom (w k),
      funext fun k => Iso.hom_inv_id_apply _ _⟩
  have h1' : orderedProduct (weylFamily P W u) e (Over.mk s)
      (fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv
        (if coPairing ((fun α => P.root α) (e k)) ω = 0 then c0 k else 0)) = 1 := by
    rw [← h1]
    congr 1
    funext k
    by_cases hk : e k = a
    · simp only [hk, ↓reduceIte, (hω a (hk ▸ he k)).1.mpr rfl]
    · have : coPairing (P.root (e k)) ω ≠ 0 := fun h0 => hk ((hω _ (he k)).1.mp h0)
      simp only [hk, ↓reduceIte, this, map_zero]
  have := coord_eq_zero_of_weight (pos := fun k => (pos k : J)) hequiv ν hnegν ω e
    (fun k => by rw [hν]; exact mul_pos hd0 (he k))
    (fun k => (hω _ (he k)).2) s c0 w0 h1' h p
    (by rw [hp, (hω a (hp ▸ (pos p).2)).1.mpr rfl])
  simp only [this, map_zero]

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
/-- Conjugation of points by a global point, from an identity of maps `𝔾ₐ → G`. -/
theorem conj_rootPoint_of_comp_eq {w w' : Ga R ⟶ G}
    {N : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X} {κ : R}
    (h : w ≫ (G.innerIso N).hom = scaleHom κ ≫ w') (Z : Over (Spec (CommRingCat.of R)))
    (x : Γ(Z.left, ⊤)) :
    G.constantPoint N Z * rootPoint w Z x * (G.constantPoint N Z)⁻¹ =
      rootPoint w' Z (baseScalar Z κ * x) := by
  have := congrArg (fun f => rootPoint f Z x) h
  rwa [rootPoint_comp, GroupScheme.comp_innerIso_hom, rootPoint_scaleHom] at this

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Conjugation of Weyl-family points by a simple Weyl point, with common units. -/
theorem WeylConjugationRelations.conj_points (hU : WeylConjugationRelations P b W u u')
    {c : J} (hc : c ∈ b.support) (d : J) :
    ∃ κ : Rˣ, (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
        G.constantPoint (rootWeylPoint P u c) Z * rootPoint (weylFamily P W u d) Z x *
            (G.constantPoint (rootWeylPoint P u c) Z)⁻¹ =
          rootPoint (weylFamily P W u (P.reflectionPerm c d)) Z (baseScalar Z (κ : R) * x)) ∧
      (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
        H.constantPoint (rootWeylPoint P u' c) Z * rootPoint (weylFamily P W u' d) Z x *
            (H.constantPoint (rootWeylPoint P u' c) Z)⁻¹ =
          rootPoint (weylFamily P W u' (P.reflectionPerm c d)) Z (baseScalar Z (κ : R) * x)) := by
  obtain ⟨κ, h1, h2⟩ := hU c hc d
  exact ⟨κ, conj_rootPoint_of_comp_eq h1, conj_rootPoint_of_comp_eq h2⟩

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Conjugation of Weyl-family points by the inverse of a simple Weyl point, with common
units. -/
theorem WeylConjugationRelations.inv_conj_points (hU : WeylConjugationRelations P b W u u')
    {c : J} (hc : c ∈ b.support) (δ : J) :
    ∃ κ : Rˣ, (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
        (G.constantPoint (rootWeylPoint P u c) Z)⁻¹ * rootPoint (weylFamily P W u δ) Z x *
            G.constantPoint (rootWeylPoint P u c) Z =
          rootPoint (weylFamily P W u (P.reflectionPerm c δ)) Z (baseScalar Z (κ : R) * x)) ∧
      (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
        (H.constantPoint (rootWeylPoint P u' c) Z)⁻¹ * rootPoint (weylFamily P W u' δ) Z x *
            H.constantPoint (rootWeylPoint P u' c) Z =
          rootPoint (weylFamily P W u' (P.reflectionPerm c δ)) Z (baseScalar Z (κ : R) * x)) := by
  obtain ⟨κ, h1, h2⟩ := hU.conj_points hc (P.reflectionPerm c δ)
  rw [RootPairing.reflectionPerm_self] at h1 h2
  refine ⟨κ⁻¹, fun Z x => ?_, fun Z x => ?_⟩
  · have := h1 Z (baseScalar Z ((κ⁻¹ : Rˣ) : R) * x)
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] at this
    rw [← this]
    group
  · have := h2 Z (baseScalar Z ((κ⁻¹ : Rˣ) : R) * x)
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] at this
    rw [← this]
    group

/-- **Conjugation of the unipotent radical of `a` by `u_{-a}`.** Let the positive roots be
enumerated by increasing height, with `a` at position `pa`. A product of positive cell factors
with zero coordinate at `a`, conjugated by `u_{-a}(x)`, is again such a product, with the same
coordinates in `G` and in `H`. -/
theorem negSimple_conj_orderedProduct [DecidableEq J]
    (hdG : IsNormalSimpleData i P b W u) (hdH : IsNormalSimpleData i' P b W u')
    (hU : WeylConjugationRelations P b W u u') {a : J} (ha : a ∈ b.support)
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
    fun β hβ y => posGood_rootPoint_of_base hdG hdH hU b negb pos hmono s hβ y
  have hva : weylFamily P W u a = u a := hdG.weylFamily_simple ha
  have hva' : weylFamily P W u' a = u' a := hdH.weylFamily_simple ha
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
    (hdH.rankOne a ha).1 A s
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
    (hdG : IsNormalSimpleData i P b W u) (hdH : IsNormalSimpleData i' P b W u')
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
    fun β hβ y => posGood_rootPoint_of_base hdG hdH hU b negb pos hmono s hβ y
  have hva : weylFamily P W u a = u a := hdG.weylFamily_simple ha
  have hva' : weylFamily P W u' a = u' a := hdH.weylFamily_simple ha
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

omit [IsLocalRing R] in
/-- Right translation of a product of non-positive root points of the Weyl family, in any
order enumerating the non-positive roots, by a non-positive root point is again such a
product. -/
theorem IsNormalSimpleData.exists_negProduct_mul (hd : IsNormalSimpleData i P b W u)
    {m : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (w : Fin m → Γ((Over.mk s).left, ⊤)) {α : J} (hα : ¬ b.IsPos α)
    (c : Γ((Over.mk s).left, ⊤)) :
    ∃ z, orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) w *
        rootPoint (weylFamily P W u α) (Over.mk s) c =
      orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) z := by
  classical
  have : Finite J := hd.rootDatum.finite
  have : Fintype J := Fintype.ofFinite J
  have : P.IsReduced := hd.rootDatum.isReduced
  obtain ⟨b', hb'⟩ := Langlands.LinearAlgebra.exists_base_isPos_iff_not P b
  let negb' : Fin m ≃ {α // b'.IsPos α} :=
    neg.trans (Equiv.subtypeEquivRight fun j => (hb' j).symm)
  let pos₀ := (Fintype.equivFin {α // ¬ b'.IsPos α}).symm
  have hWf := hd.isRootParametrization
  have : IsOpenImmersion (cellMap i (weylFamily P W u) (fun k => (pos₀ k : J))
      (fun k => (neg k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hd.reductive hd.maximal hd.rootDatum b' _ hWf
      pos₀ negb'
  obtain ⟨d, hd0, ν, hν⟩ := exists_coPairing_eq_height P b'
  have hnegν : ∀ k, coPairing (P.root (pos₀ k : J)) ν < 0 := by
    intro k
    rw [hν]
    have h0 := b'.height_ne_zero (pos₀ k : J)
    have h1 := (pos₀ k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd0 (by omega)
  have hposν : ∀ β, b'.IsPos β → 0 < coPairing (P.root β) ν := by
    intro β hβ
    rw [hν]
    exact mul_pos hd0 hβ
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  exact exists_orderedProduct_mul_rootPoint_eq_pos (neg := fun k => (pos₀ k : J)) hequiv ν
    hnegν (fun k => hposν _ ((hb' _).mpr (neg k).2)) (hposν α ((hb' α).mpr hα)) s w c

omit [IsLocalRing R] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Moving a torus point by an exponent automorphism `e` changes the exponent of a character
by `e`. -/
theorem torusChar_comp_exponentIso_hom (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (m : I → ℤ)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    torusChar m Z (t ≫ (splitTorus.exponentIso _ I e).hom.hom.hom) = torusChar (e m) Z t := by
  rw [torusChar, torusChar, VectorGroup.charValue, VectorGroup.charValue, Category.assoc,
    show splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (e m) =
      splitTorus.exponentHom _ I I e.toLinearMap ≫ splitTorus.exponentCharacter _ I m from
      (splitTorus.exponentHom_comp_exponentCharacter _ I I e.toLinearMap m).symm]
  rfl

omit [IsLocalRing R] in
/-- Right translation of a product of non-positive root points of the Weyl family, in any
order enumerating the non-positive roots, by a list of non-positive root points. -/
theorem IsNormalSimpleData.exists_negProduct_mul_list (hd : IsNormalSimpleData i P b W u)
    {m : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (L : List (J × Γ((Over.mk s).left, ⊤))) (hL : ∀ p ∈ L, ¬ b.IsPos p.1)
    (w : Fin m → Γ((Over.mk s).left, ⊤)) :
    ∃ z, orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) w *
        (L.map fun p => rootPoint (weylFamily P W u p.1) (Over.mk s) p.2).prod =
      orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) z := by
  classical
  have : Finite J := hd.rootDatum.finite
  have : Fintype J := Fintype.ofFinite J
  have : P.IsReduced := hd.rootDatum.isReduced
  obtain ⟨b', hb'⟩ := Langlands.LinearAlgebra.exists_base_isPos_iff_not P b
  let negb' : Fin m ≃ {α // b'.IsPos α} :=
    neg.trans (Equiv.subtypeEquivRight fun j => (hb' j).symm)
  let pos₀ := (Fintype.equivFin {α // ¬ b'.IsPos α}).symm
  have hWf := hd.isRootParametrization
  have : IsOpenImmersion (cellMap i (weylFamily P W u) (fun k => (pos₀ k : J))
      (fun k => (neg k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hd.reductive hd.maximal hd.rootDatum b' _ hWf
      pos₀ negb'
  obtain ⟨d, hd0, ν, hν⟩ := exists_coPairing_eq_height P b'
  have hnegν : ∀ k, coPairing (P.root (pos₀ k : J)) ν < 0 := by
    intro k
    rw [hν]
    have h0 := b'.height_ne_zero (pos₀ k : J)
    have h1 := (pos₀ k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd0 (by omega)
  have hposν : ∀ β, b'.IsPos β → 0 < coPairing (P.root β) ν := by
    intro β hβ
    rw [hν]
    exact mul_pos hd0 hβ
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  exact exists_orderedProduct_mul_list (neg := fun k => (pos₀ k : J)) hequiv ν hnegν
    (fun k => hposν _ ((hb' _).mpr (neg k).2)) s L
    (fun p hp => hposν _ ((hb' _).mpr (hL p hp))) w

omit [IsLocalRing R] in
/-- Right translation of a product of positive cell factors by a list of positive root points of
the Weyl family. -/
theorem IsNormalSimpleData.exists_posProduct_mul_list (hd : IsNormalSimpleData i P b W u)
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (L : List (J × Γ((Over.mk s).left, ⊤))) (hL : ∀ p ∈ L, b.IsPos p.1)
    (w : Fin n → Γ((Over.mk s).left, ⊤)) :
    ∃ z, orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w *
        (L.map fun p => rootPoint (weylFamily P W u p.1) (Over.mk s) p.2).prod =
      orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) z := by
  have : Finite J := hd.rootDatum.finite
  have hWf := hd.isRootParametrization
  have := LocalSplitBigCell.isOpenImmersion_cellMap hd.reductive hd.maximal hd.rootDatum b _
    hWf neg pos
  obtain ⟨d, hd0, ν, hν⟩ := exists_coPairing_eq_height P b
  have hnegν : ∀ k, coPairing (P.root (neg k : J)) ν < 0 := by
    intro k
    rw [hν]
    have h0 := b.height_ne_zero (neg k : J)
    have h1 := (neg k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd0 (by omega)
  have hposν : ∀ β, b.IsPos β → 0 < coPairing (P.root β) ν := by
    intro β hβ
    rw [hν]
    exact mul_pos hd0 hβ
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  exact exists_orderedProduct_mul_list (neg := fun k => (neg k : J)) hequiv ν hnegν
    (fun k => hposν _ (pos k).2) s L (fun p hp => hposν _ (hL p hp)) w

omit [DecidableEq I] in
theorem coPairing_neg (ch ν : I → ℤ) : coPairing (-ch) ν = -coPairing ch ν := by
  simp only [coPairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- **The simple Weyl point is not in the big cell.** No expression
`N · T · n_a · X`, with `N` a product of non-positive cell factors, `T` a torus point and `X` a
product of positive cell factors, is a big-cell point, provided the test ring has a unit `l₀`
with `l₀⁴ ≠ 1`. -/
theorem IsNormalSimpleData.false_of_weylPoint_mem (hd : IsNormalSimpleData i P b W u)
    {a : J} (ha : a ∈ b.support) {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α})
    (pos : Fin n ≃ {α // b.IsPos α}) {A : Type u} [CommRing A] [IsLocalRing A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (l₀ : (Γ((Over.mk s).left, ⊤))ˣ) (hl₀ : ((l₀ : Γ((Over.mk s).left, ⊤))) ^ 4 ≠ 1)
    (v : Fin m → Γ((Over.mk s).left, ⊤))
    (T : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (w : Fin n → Γ((Over.mk s).left, ⊤)) (y : Over.mk s ⟶ cellObj R I m n)
    (h : orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) v *
        (T ≫ i.hom.hom) * G.constantPoint (rootWeylPoint P u a) (Over.mk s) *
        orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w =
      y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) :
    False := by
  classical
  have : Finite J := hd.rootDatum.finite
  have hWf := hd.isRootParametrization
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  have := LocalSplitBigCell.isOpenImmersion_cellMap hd.reductive hd.maximal hd.rootDatum b _
    hWf neg pos
  have hmono : Mono (cellMap i (weylFamily P W u) (fun k => (neg k : J))
      (fun k => (pos k : J))) := Over.mono_of_mono_left _
  set t := cocharPoint (P.coroot a) (Over.mk s) l₀ with ht
  set ft := t ≫ (splitTorus.exponentIso _ I (P.reflection a)).hom.hom.hom with hft
  set nG := G.constantPoint (rootWeylPoint P u a) (Over.mk s) with hnG
  have hW : nG * (t ≫ i.hom.hom) = (ft ≫ i.hom.hom) * nG := by
    have := hd.weyl a ha (Over.mk s) t
    rw [toUnit_comp_eq_constantPoint, ← hnG] at this
    have this' : ft ≫ i.hom.hom = nG * (t ≫ i.hom.hom) * nG⁻¹ := by
      rw [hft, Category.assoc]; exact this.symm
    rw [this']
    group
  -- the conjugated negative factor
  let v' : Fin m → Γ((Over.mk s).left, ⊤) := fun k =>
    Ring.inverse (torusChar (P.root (neg k : J)) (Over.mk s) ft) * v k
  have hN' : (ft ≫ i.hom.hom)⁻¹ *
      orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) v * (ft ≫ i.hom.hom) =
      orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) v' := by
    have e := torus_mul_orderedProduct_mul_inv hequiv (fun k => (neg k : J)) ft v'
    have hv : (fun k => torusChar (P.root (neg k : J)) (Over.mk s) ft * v' k) = v := by
      funext k
      simp only [v']
      rw [← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_torusChar _ _ _), one_mul]
    simp only at e
    rw [hv] at e
    rw [← e]
    group
  -- the conjugated positive factor
  obtain hX := orderedProduct_mul_torus hequiv (fun k => (pos k : J)) t w
  set w'' : Fin n → Γ((Over.mk s).left, ⊤) := fun k =>
    Ring.inverse (torusChar (P.root (pos k : J)) (Over.mk s) t) * w k with hw''
  -- existence of the new coordinates
  obtain ⟨z₁, hz₁⟩ := hd.exists_negProduct_mul_list neg s
    ((List.ofFn fun k => ((neg k : J), -v k)).reverse ++
      List.ofFn fun k => ((neg k : J), negCoord y k))
    (by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hp)
        exact (neg k).2
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
        exact (neg k).2) v'
  obtain ⟨z₃, hz₃⟩ := hd.exists_posProduct_mul_list neg pos s
    ((List.ofFn fun k => ((pos k : J), -w k)).reverse ++
      List.ofFn fun k => ((pos k : J), w'' k))
    (by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hp)
        exact (pos k).2
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
        exact (pos k).2) (posCoord y)
  rw [List.map_append, List.prod_append, ← orderedProduct_inv_eq_list_prod,
    ← orderedProduct_eq_list_prod] at hz₁ hz₃
  -- the cell point `K = (ft)⁻¹ · E · t`
  set N := orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) v with hNdef
  set X := orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w with hXdef
  set X'' := orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) w'' with hX''def
  have hc : (T ≫ i.hom.hom) * (ft ≫ i.hom.hom) = (ft ≫ i.hom.hom) * (T ≫ i.hom.hom) :=
    (torus_comp_mul_comm i T ft).symm
  have e1 : nG * X * (t ≫ i.hom.hom) = (ft ≫ i.hom.hom) * nG * X'' := by
    rw [mul_assoc, hX, ← mul_assoc, hW]
  have step : (ft ≫ i.hom.hom)⁻¹ * (N * (T ≫ i.hom.hom) * nG * X) * (t ≫ i.hom.hom) =
      orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) v' * N⁻¹ *
        (N * (T ≫ i.hom.hom) * nG * X) * X⁻¹ * X'' := by
    calc (ft ≫ i.hom.hom)⁻¹ * (N * (T ≫ i.hom.hom) * nG * X) * (t ≫ i.hom.hom)
        = (ft ≫ i.hom.hom)⁻¹ * N * (T ≫ i.hom.hom) * (nG * X * (t ≫ i.hom.hom)) := by group
      _ = (ft ≫ i.hom.hom)⁻¹ * N * ((T ≫ i.hom.hom) * (ft ≫ i.hom.hom)) * nG * X'' := by
          rw [e1]; group
      _ = (ft ≫ i.hom.hom)⁻¹ * N * ((ft ≫ i.hom.hom) * (T ≫ i.hom.hom)) * nG * X'' := by
          rw [hc]
      _ = _ := by rw [← hN']; group
  have hR : mkCellPoint (Over.mk s) z₁ (splitTorus.pointsEquiv I _ (torusCoord y)) z₃ ≫
      cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) =
      orderedProduct (weylFamily P W u) (fun k => (neg k : J)) (Over.mk s) z₁ *
        (torusCoord y ≫ i.hom.hom) *
        orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) z₃ := by
    have hT : torusCoord (mkCellPoint (Over.mk s) z₁
        (splitTorus.pointsEquiv I _ (torusCoord y)) z₃) = torusCoord y :=
      (splitTorus.pointsEquiv I _).injective (by rw [torusCoord_mkCellPoint])
    rw [comp_cellMap, negCoord_mkCellPoint, posCoord_mkCellPoint, hT]
    rfl
  have hK : (ft ≫ i.hom.hom)⁻¹ *
      (y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
      (t ≫ i.hom.hom) =
      mkCellPoint (Over.mk s) z₁ (splitTorus.pointsEquiv I _ (torusCoord y)) z₃ ≫
        cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) := by
    rw [← h, step, h, hR, ← hz₁, ← hz₃, comp_cellMap, cellPoint]
    group

  -- compare the torus coordinates of `E · t`
  have h1 := comp_cellMap_mul_torus' (neg := fun k => (neg k : J)) (pos := fun k => (pos k : J))
    hequiv y t
  have h2 := torus_mul_comp_cellMap (neg := fun k => (neg k : J)) (pos := fun k => (pos k : J))
    hequiv (mkCellPoint (Over.mk s) z₁
    (splitTorus.pointsEquiv I _ (torusCoord y)) z₃) ft
  have hEq : (ft ≫ i.hom.hom) * (mkCellPoint (Over.mk s) z₁
      (splitTorus.pointsEquiv I _ (torusCoord y)) z₃ ≫
        cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) =
      (y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
        (t ≫ i.hom.hom) := by
    rw [← hK]
    group
  rw [h1, h2] at hEq
  have hpts := congrArg (fun q => splitTorus.pointsEquiv I _ (torusCoord q))
    ((cancel_mono _).mp hEq)
  simp only [torusCoord_mkCellPoint] at hpts
  rw [map_mul, map_mul, torusCoord_mkCellPoint] at hpts
  have htor : ft = t := by
    apply (splitTorus.pointsEquiv I (Over.mk s)).injective
    rw [mul_comm (splitTorus.pointsEquiv I (Over.mk s) (torusCoord y))] at hpts
    exact mul_right_cancel hpts
  -- the character of `a` distinguishes `t` and its reflection
  have hχ := congrArg (torusChar (P.root a) (Over.mk s)) htor
  rw [hft, torusChar_comp_exponentIso_hom, RootPairing.reflection_apply_self, ht,
    torusChar_cocharPoint, torusChar_cocharPoint, coPairing_neg,
    coPairing_root_coroot hd.rootDatum, RootPairing.pairingIn_same] at hχ
  have hu : l₀ ^ (-(2 : ℤ)) = l₀ ^ (2 : ℤ) := Units.ext hχ
  have h4 : l₀ ^ (4 : ℕ) = 1 := by
    have : l₀ ^ (4 : ℤ) = 1 := by
      calc l₀ ^ (4 : ℤ) = l₀ ^ (2 : ℤ) * l₀ ^ (2 : ℤ) := by rw [← zpow_add]; norm_num
        _ = l₀ ^ (2 : ℤ) * l₀ ^ (-2 : ℤ) := by rw [hu]
        _ = 1 := by rw [← zpow_add]; norm_num
    exact_mod_cast this
  apply hl₀
  rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]

omit [IsLocalRing R] in
/-- The Weyl family at `-a`, for a simple root `a` and descending words, is `u_{-a}` up to the
sign of the argument. -/
theorem IsNormalSimpleData.rootPoint_weylFamily_neg (hd : IsNormalSimpleData i P b W u)
    {a : J} (ha : a ∈ b.support) {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y : Γ((Over.mk s).left, ⊤)) :
    rootPoint (weylFamily P W u (P.reflectionPerm a a)) (Over.mk s) y =
      rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-y) := by
  have hapos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hneg : ¬ b.IsPos (P.reflectionPerm a a) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) a).mp h hapos
  have hnn : P.reflectionPerm (P.reflectionPerm a a) (P.reflectionPerm a a) = a :=
    P.root.injective (by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
        RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg])
  obtain ⟨h1, h2⟩ := hd.words.2.2 (P.reflectionPerm a a) hneg
  rw [hnn, (hd.words.1 a ha).1] at h1
  rw [hnn, (hd.words.1 a ha).2, (hd.words.1 a ha).1] at h2
  have hw : weylFamily P W u (P.reflectionPerm a a) = wordConj P u [a] (u a) := by
    unfold weylFamily
    rw [h2, h1]
    rfl
  rw [hw]
  change rootPoint (u a ≫ (G.innerIso (rootWeylPoint P u a)).hom) (Over.mk s) y = _
  rw [rootPoint_comp, GroupScheme.comp_innerIso_hom]
  exact (hd.rankOne a ha).1 B s y

omit [IsLocalRing R] in
/-- The rank-one identity `u_a(1) u_{-a}(-1) = n_a u_a(-1)`. -/
theorem IsNormalSimpleData.rootPoint_one_mul_neg (hd : IsNormalSimpleData i P b W u)
    {a : J} (ha : a ∈ b.support) {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    rootPoint (u a) (Over.mk s) 1 * rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) =
      G.constantPoint (rootWeylPoint P u a) (Over.mk s) * rootPoint (u a) (Over.mk s) (-1) := by
  set n := G.constantPoint (rootWeylPoint P u a) (Over.mk s) with hn
  have h1 : ∀ y, n * rootPoint (u a) (Over.mk s) y * n⁻¹ =
      rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-y) := (hd.rankOne a ha).1 B s
  have h2 : ∀ y, n * rootPoint (u (P.reflectionPerm a a)) (Over.mk s) y * n⁻¹ =
      rootPoint (u a) (Over.mk s) (-y) := (hd.rankOne a ha).2.1 B s
  have hdef : n = rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) *
      rootPoint (u a) (Over.mk s) 1 * rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) := by
    rw [hn]
    exact constantPoint_weylPoint _ _ _
  have hn2 : n = rootPoint (u a) (Over.mk s) 1 *
      rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) * rootPoint (u a) (Over.mk s) 1 := by
    calc n = n * (rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) *
          rootPoint (u a) (Over.mk s) 1 *
          rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1)) * n⁻¹ := by
          rw [← hdef]; group
      _ = (n * rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) * n⁻¹) *
          (n * rootPoint (u a) (Over.mk s) 1 * n⁻¹) *
          (n * rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) * n⁻¹) := by group
      _ = _ := by rw [h2, h1, neg_neg]
  rw [hn2, rootPoint_neg (u a) _ 1]
  group

/-- **Transfer of right translation by `u_{-a}(-1)`.** -/
theorem negSimple_transfer [DecidableEq J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {a : J} (ha : a ∈ b.support) (hBG : RankOneBruhat i P u a) (hBH : RankOneBruhat i' P u' a)
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
    fun β hβ y => posGood_rootPoint_of_base hdG hdH hU b neg pos hmono s hβ y
  have hva : weylFamily P W u a = u a := hdG.weylFamily_simple ha
  have hva' : weylFamily P W u' a = u' a := hdH.weylFamily_simple ha
  set pa := pos.symm ⟨a, hapos⟩ with hpadef
  have hpa : (pos pa : J) = a := by rw [hpadef, Equiv.apply_symm_apply]
  obtain ⟨w₁, hw₁, hsG, hsH⟩ :=
    split_simple_orderedProduct hdG hdH hU ha neg pos hmono s pa hpa (posCoord x)
  obtain ⟨w₂, -, hcG, hcH⟩ :=
    negSimple_conj_orderedProduct hdG hdH hU ha neg pos hmono s pa hpa w₁ hw₁ 1
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
      (hdH.param a ha).2.equivariant _ _ _
    -- the negative factor
    obtain ⟨z, hzG⟩ := hdG.exists_negProduct_mul neg s (negCoord x) hnegpos
      (-(χ * ((d⁻¹ : (Γ((Over.mk s).left, ⊤))ˣ) * -1)))
    have hzH := negativeLaws hdG hdH hU (fun k => (neg k : J)) (fun k => (neg k).2) s hnegpos
      _ (negCoord x) z hzG
    rw [hdG.rootPoint_weylFamily_neg ha, neg_neg] at hzG
    rw [hdH.rootPoint_weylFamily_neg ha, neg_neg] at hzH
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
      split_simple_orderedProduct hdG hdH hU ha neg pos hmono sK pa hpa (posCoord (f ≫ x))
    obtain ⟨w₂', -, hc'G, -⟩ :=
      negSimple_conj_orderedProduct hdG hdH hU ha neg pos hmono sK pa hpa w₁' hw₁' 1
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

end NegSimpleConj


end LocalSplitCell

open LocalSplitCell in
/-- **Negative simple relations from rank one and Weyl conjugation.** The rank-one
normalization statement, the rank-one Bruhat statement and the Weyl-conjugation statement imply
the negative simple relations of Weyl families over a local ring. -/
theorem localSplitWeylNegSimple_of_rankOne (hR : LocalSplitRankOneNormalStatement.{u})
    (hB : LocalSplitRankOneBruhatStatement.{u}) (hC : LocalSplitWeylConjugationStatement.{u}) :
    LocalSplitWeylNegSimpleStatement.{u} := by
  intro R _ _ I _ _ J G H _ _ hG hH i i' hi hi' hmax hmax' P hP hP' b W hW u u' hu hw hu' hw'
    m n neg pos hmono
  classical
  have hR1 : ∀ a ∈ b.support, RankOneNormal i P u a := hR R G hG I i hi hmax J P hP b u hu hw
  have hR2 : ∀ a ∈ b.support, RankOneNormal i' P u' a :=
    hR R H hH I i' hi' hmax' J P hP' b u' hu' hw'
  have hB1 : ∀ a ∈ b.support, RankOneBruhat i P u a := hB R G hG I i hi hmax J P hP b u hu hw
  have hB2 : ∀ a ∈ b.support, RankOneBruhat i' P u' a :=
    hB R H hH I i' hi' hmax' J P hP' b u' hu' hw'
  have hU := hC R I J G H hG hH i i' hi hi' hmax hmax' P hP hP' b W hW u u' hu hw hu' hw' hR1 hR2
  have hdG : IsNormalSimpleData i P b W u := ⟨hG, hmax, hP, hu, hw, hW, hR1⟩
  have hdH : IsNormalSimpleData i' P b W u' := ⟨hH, hmax', hP', hu', hw', hW, hR2⟩
  intro A _ _ _ s x y a ha hxy
  exact negSimple_transfer hdG hdH hU ha (hB1 a ha) (hB2 a ha) neg pos hmono s x y hxy

/-- **Statement: the negative simple relations of Weyl families reduce to rank one and Weyl
conjugation.** Over local rings, `LocalSplitRankOneNormalStatement`,
`LocalSplitRankOneBruhatStatement` and `LocalSplitWeylConjugationStatement` imply
`LocalSplitWeylNegSimpleStatement`. -/
def LocalSplitWeylNegSimpleReductionStatement : Prop :=
  LocalSplitRankOneNormalStatement.{u} → LocalSplitRankOneBruhatStatement.{u} →
    LocalSplitWeylConjugationStatement.{u} → LocalSplitWeylNegSimpleStatement.{u}

theorem localSplitWeylNegSimpleReduction : LocalSplitWeylNegSimpleReductionStatement.{u} :=
  localSplitWeylNegSimple_of_rankOne

end Langlands.GroupScheme
