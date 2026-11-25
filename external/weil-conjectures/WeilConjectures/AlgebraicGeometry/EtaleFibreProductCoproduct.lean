/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Iterated fibre products of a finite coproduct

Source: Stacks Project, Schemes, Tags 01JB and 01JC, and Section 26.17
(blueprint: lem-sc-etale-fibre-product-coproduct).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- The canonical cofan of products indexed by all choices of summands.
private noncomputable def powerCofan {C : Type*} [Category C] [HasFiniteProducts C]
    {I : Type*} (A : I → C) {V : C} (c : ∀ i, A i ⟶ V) (n : ℕ) :
    Cofan (fun J : Fin n → I ↦ ∏ᶜ fun r ↦ A (J r)) :=
  Cofan.mk (∏ᶜ fun _ : Fin n ↦ V) fun J ↦
    Pi.lift (fun r ↦ Pi.π (fun s ↦ A (J s)) r ≫ c (J r))

-- Split a finite product into its first coordinate and its remaining coordinates.
private noncomputable def splitProduct {C : Type*} [Category C] [HasFiniteProducts C]
    {n : ℕ} (B : Fin (n + 1) → C) :
    BinaryFan (B 0) (∏ᶜ fun r : Fin n ↦ B r.succ) :=
  BinaryFan.mk (P := ∏ᶜ B) (Pi.π B 0) (Pi.lift fun r ↦ Pi.π B r.succ)

private theorem splitProduct_isLimit {C : Type*} [Category C] [HasFiniteProducts C]
    {n : ℕ} (B : Fin (n + 1) → C) : Nonempty (IsLimit (splitProduct B)) := by
  refine ⟨BinaryFan.isLimitMk (fun s ↦ Pi.lift (Fin.cases s.fst
    (fun r ↦ s.snd ≫ Pi.π (fun t : Fin n ↦ B t.succ) r))) ?_ ?_ ?_⟩
  · intro s
    simp
  · intro s
    apply Pi.hom_ext
    intro r
    simp
  · intro s m h₀ h₁
    apply Pi.hom_ext
    intro r
    refine Fin.cases ?_ (fun t ↦ ?_) r
    · simpa [splitProduct] using h₀
    · have h := congrArg (fun f ↦ f ≫ Pi.π (fun t : Fin n ↦ B t.succ) t) h₁
      simpa [splitProduct] using h

-- Universal finite coproducts distribute over products; include zero factors for induction.
private theorem powerCofan_isColimit {C : Type*} [Category C] [HasFiniteLimits C]
    [FinitaryExtensive C] {I : Type*} [Finite I] (A : I → C) {V : C}
    (c : ∀ i, A i ⟶ V) (hc : IsColimit (Cofan.mk V c)) (n : ℕ) :
    Nonempty (IsColimit (powerCofan A c n)) := by
  induction n with
  | zero =>
    refine ⟨Cofan.IsColimit.mk _ (fun s ↦
      Pi.lift (fun r : Fin 0 ↦ Fin.elim0 r) ≫ s.inj Fin.elim0) ?_ ?_⟩
    · intro s J
      have hJ : J = Fin.elim0 := funext (fun r ↦ Fin.elim0 r)
      subst J
      have h : (powerCofan A c 0).inj Fin.elim0 ≫
          Pi.lift (fun r : Fin 0 ↦ Fin.elim0 r) = 𝟙 _ := by
        apply Pi.hom_ext
        intro r
        exact Fin.elim0 r
      simp only [← Category.assoc, h, Category.id_comp]
    · intro s m hm
      have h := hm Fin.elim0
      rw [← h]
      have h' : Pi.lift (fun r : Fin 0 ↦ Fin.elim0 r) ≫
          (powerCofan A c 0).inj Fin.elim0 = 𝟙 _ := by
        apply Pi.hom_ext
        intro r
        exact Fin.elim0 r
      simp only [← Category.assoc, h', Category.id_comp]
  | succ n ih =>
    let E : (Fin (n + 1) → I) ≃ I × (Fin n → I) :=
      { toFun := fun J ↦ (J 0, fun r ↦ J r.succ)
        invFun := fun ij ↦ Fin.cons (α := fun _ : Fin (n + 1) ↦ I) ij.1 ij.2
        left_inv := fun J ↦ by funext r; exact Fin.cases rfl (fun _ ↦ rfl) r
        right_inv := fun ij ↦ rfl }
    let d := Cofan.mk (powerCofan A c (n + 1)).pt
      (fun ij : I × (Fin n → I) ↦ (powerCofan A c (n + 1)).inj (E.symm ij))
    have hd : Nonempty (IsColimit d) := by
      refine IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
        (Z := ∏ᶜ fun _ : Fin (n + 1) ↦ V)
        (P := fun ij : I × (Fin n → I) ↦
          ∏ᶜ fun r : Fin (n + 1) ↦ A (Fin.cons (α := fun _ : Fin (n + 1) ↦ I) ij.1 ij.2 r))
        (FinitaryPreExtensive.isUniversal_finiteCoproducts hc)
        (FinitaryPreExtensive.isUniversal_finiteCoproducts ih.some)
        (fun i ↦ terminalIsTerminal.from (A i))
        (fun J ↦ terminalIsTerminal.from (∏ᶜ fun r : Fin n ↦ A (J r)))
        (terminalIsTerminal.from V) (terminalIsTerminal.from (∏ᶜ fun _ : Fin n ↦ V))
        (fun (i : I) (J : Fin n → I) ↦ IsPullback.of_is_product
          (splitProduct_isLimit (fun r : Fin (n + 1) ↦
            A (Fin.cons (α := fun _ : Fin (n + 1) ↦ I) i J r))).some terminalIsTerminal)
        (IsPullback.of_is_product
          (splitProduct_isLimit (fun _ : Fin (n + 1) ↦ V)).some terminalIsTerminal)
        (d := d) (Iso.refl _) ?_ ?_ ?_ ?_
      · intro i
        apply terminalIsTerminal.hom_ext
      · intro J
        apply terminalIsTerminal.hom_ext
      · intro i J
        simp only [Cofan.mk_pt, Equiv.symm_mk, Equiv.coe_fn_mk, powerCofan,
          cofan_mk_inj, Iso.refl_hom, splitProduct, BinaryFan.mk_fst, Category.id_comp,
          limit.lift_π, Fan.mk_pt, Fan.mk_π_app, d, E]
        rfl
      · intro i J
        apply Pi.hom_ext
        intro r
        simp only [Equiv.symm_mk, Equiv.coe_fn_mk, powerCofan, Cofan.mk_pt,
          cofan_mk_inj, Iso.refl_hom, splitProduct, BinaryFan.mk_snd, Category.id_comp,
          Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, d, E]
        dsimp [Fin.cons]
        rw [Pi.lift_comp_π_assoc]
    exact ⟨(Cofan.isColimitEquivOfEquiv E.symm (powerCofan A c (n + 1))).symm hd.some⟩

/-- Source: Stacks Project, Schemes, Tags 01JB and 01JC and Section 26.17
(blueprint: lem-sc-etale-fibre-product-coproduct).
Products in `Over X` are iterated fibre products over `X`. The canonical isomorphisms
are oriented from the coproduct of indexed fibre products to the fibre product of the
coproduct. Their component equations specify the canonical map, and the final equations
specify compatibility with every omitted-factor projection.

Proof: (1) Form the component maps from the coprojections using fibre-product universality
(`def-pc-fibre-product`), then glue using `lem-weil-pbc-scheme-coproduct-family`.
(2) For one factor the map is the identity by coproduct uniqueness.
(3) Induct on the number of factors, using
`lem-sc-etale-fibre-product-base-change-coproduct` first on the last factor and then on
the preceding factors; exchange factors and flatten the resulting coproduct of coproducts.
Fibre-product uniqueness identifies the composite with the component map from (1).
(4) After omitting a factor, the two component maps have identical projections to all
remaining factors, so fibre-product uniqueness proves their equality. -/
theorem etale_fibre_product_coproduct (X : Scheme.{u}) (I : Type v) [Finite I]
    (U : I → Scheme.{u}) (u : ∀ i : I, U i ⟶ X) :
    let A : I → Over X := fun i => Over.mk (u i)
    let V : Over X := Over.mk (Sigma.desc u)
    let P := fun (p : ℕ) (J : Fin (p + 1) → I) => ∏ᶜ fun r => A (J r)
    let Q := fun p : ℕ => ∏ᶜ fun _ : Fin (p + 1) => V
    let c : ∀ i : I, A i ⟶ V := fun i =>
      Over.homMk (Sigma.ι U i) (Sigma.ι_comp_desc u i)
    ∃ e : ∀ p : ℕ, (∐ P p) ≅ Q p,
      (∀ (p : ℕ) (J : Fin (p + 1) → I) (r : Fin (p + 1)),
        Sigma.ι (P p) J ≫ (e p).hom ≫ Pi.π (fun _ : Fin (p + 1) => V) r =
          Pi.π (fun s : Fin (p + 1) => A (J s)) r ≫ c (J r)) ∧
      (∀ (p : ℕ) (J : Fin (p + 2) → I) (r : Fin (p + 2)),
        Sigma.ι (P (p + 1)) J ≫ (e (p + 1)).hom ≫
            Pi.lift (fun s : Fin (p + 1) =>
              Pi.π (fun _ : Fin (p + 2) => V) (r.succAbove s)) =
          Pi.lift (fun s : Fin (p + 1) =>
              Pi.π (fun t : Fin (p + 2) => A (J t)) (r.succAbove s)) ≫
            Sigma.ι (P p) (fun s => J (r.succAbove s)) ≫ (e p).hom) := by
  classical
  dsimp only
  let A : I → Over X := fun i ↦ Over.mk (u i)
  let V : Over X := Over.mk (Sigma.desc u)
  let c : ∀ i : I, A i ⟶ V := fun i ↦
    Over.homMk (Sigma.ι U i) (Sigma.ι_comp_desc u i)
  let : FinitaryExtensive (Over X) :=
    finitaryExtensive_of_preserves_and_reflects_isomorphism (Over.forget X)
  have hc : IsColimit (Cofan.mk V c) := by
    apply isColimitOfReflects (Over.forget X)
    exact (Cofan.isColimitMapCoconeEquiv (Over.forget X) A (Cofan.mk V c)).symm
      (coproductIsCoproduct U)
  let e (p : ℕ) := (coproductIsCoproduct _).coconePointUniqueUpToIso
    (powerCofan_isColimit A c hc (p + 1)).some
  have he (p : ℕ) (J : Fin (p + 1) → I) (r : Fin (p + 1)) :
      Sigma.ι _ J ≫ (e p).hom ≫ Pi.π _ r =
        Pi.π (fun s ↦ A (J s)) r ≫ c (J r) := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct _) (powerCofan_isColimit A c hc (p + 1)).some ⟨J⟩
    simpa [Category.assoc, powerCofan] using congrArg (fun f ↦ f ≫ Pi.π _ r) h
  refine ⟨e, he, ?_⟩
  intro p J r
  apply Pi.hom_ext
  intro s
  simp only [Category.assoc, Pi.lift_comp_π]
  rw [he (p + 1) J (r.succAbove s), he p (fun t ↦ J (r.succAbove t)) s]
  simp only [A, Pi.lift_comp_π_assoc]

end AlgebraicGeometry
