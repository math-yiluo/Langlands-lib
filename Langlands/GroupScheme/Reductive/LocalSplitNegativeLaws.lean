import Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction

/-! # Laws of the negative cell factors of Weyl families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LinearAlgebra

open Module Matrix Langlands.GroupScheme.SplitExistence

/-- **The opposite base.** Some base has as positive roots exactly the roots that are not
positive for a given base. -/
theorem exists_base_isPos_iff_not {I J : Type u} [Fintype I] [Finite J]
    (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced] (b : P.Base) :
    ∃ b' : P.Base, ∀ j, b'.IsPos j ↔ ¬ b.IsPos j := by
  have := Fintype.ofFinite J
  obtain ⟨d, hd, ν, hν⟩ := Langlands.GroupScheme.LocalSplitCell.exists_coPairing_eq_height P b
  let f : Dual ℤ (I → ℤ) :=
    { toFun := fun v => -(v ⬝ᵥ ν)
      map_add' := fun v v' => by rw [add_dotProduct, neg_add]
      map_smul' := fun r v => by rw [smul_dotProduct, smul_neg]; rfl }
  have hfval : ∀ j, f (P.root j) = -(d * b.height j) := fun j => by
    have h : P.root j ⬝ᵥ ν = d * b.height j := hν j
    show -(P.root j ⬝ᵥ ν) = _
    rw [h]
  have hf : ∀ j, f (P.root j) ≠ 0 := by
    intro j
    rw [hfval]
    have h0 := b.height_ne_zero j
    have : d * b.height j ≠ 0 := mul_ne_zero hd.ne' h0
    omega
  let g : Dual ℤ (I → ℤ) := f ∘ₗ P.flip.Polarization
  have hg : ∀ j, g (P.coroot j) ≠ 0 := fun j => dual_polarization_root_ne_zero P.flip hf j
  have hgf : ∀ j, 0 < g (P.coroot j) ↔ 0 < f (P.root j) :=
    fun j => dual_polarization_root_pos_iff P.flip f j
  obtain ⟨b', hb'⟩ := exists_base_isPos_iff P g hg
  refine ⟨b', fun j => ?_⟩
  rw [hb', hgf, hfval, RootPairing.Base.isPos_iff]
  have h0 := b.height_ne_zero j
  constructor
  · intro h h'
    nlinarith
  · intro h
    have h' : b.height j < 0 := by omega
    nlinarith

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

namespace LocalSplitCell

section NegativeLaws

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [IsAffineHom H.X.hom] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **Positive-good root points for a base.** Let `b'` be a base, `pos` an enumeration of its
positive roots by increasing `b'`-height and `negb` an enumeration of the other roots. Over a
local test ring, every point of the Weyl family at a `b'`-positive root, with its partner in `H`,
is positive-good for the products of the factors along `pos`. -/
theorem posGood_rootPoint_of_base [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
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
      obtain ⟨E, h1, h2⟩ := exists_common_isUnivComm_of_base hdG hdH hU b' pos hmono k l hkl
      exact posComm_transfer_of_isUnivComm (i := i) (neg := fun k => (negb k : J)) h1 h2 s
        x y e he) (pos.symm ⟨β, hβ⟩) x
  simpa only [Equiv.apply_symm_apply] using this

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsLocalRing R] [Fintype I] [DecidableEq I] in
/-- A positive-good pair has the same coordinates in `G` and `H`. -/
theorem PosGood.exists_eq {Z : Over (Spec (CommRingCat.of R))} {v : J → (Ga R ⟶ G)}
    {v' : J → (Ga R ⟶ H)} {n : ℕ} {pos : Fin n → J} {g : Z ⟶ G.X} {h : Z ⟶ H.X}
    (hg : PosGood v v' pos Z g h) :
    ∃ w, g = LocalSplitCell.orderedProduct v pos Z w ∧
      h = LocalSplitCell.orderedProduct v' pos Z w := by
  obtain ⟨w, hw⟩ := hg.1 0
  have hw' := hg.2 0 w hw
  rw [orderedProduct_zero, one_mul] at hw hw'
  exact ⟨w, hw, hw'⟩

/-- **Laws of the negative cell factors.** Over a local test ring, take any enumeration `neg`
of non-positive roots. Every law `N(w) · v_α(c) = N(z)` of the Weyl family of `G`, for products
`N` of non-positive root points in the order `neg` and a non-positive root `α`, holds with the
same coordinates in `H`. -/
theorem negativeLaws [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
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
    fun β hβ x => posGood_rootPoint_of_base hdG hdH hU b' pos₀ e₀ hmono₀ s hβ x
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

end NegativeLaws

end LocalSplitCell

end Langlands.GroupScheme
