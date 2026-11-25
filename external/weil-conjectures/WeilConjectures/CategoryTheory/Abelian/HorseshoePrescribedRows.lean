/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Extending a fixed initial horseshoe embedding to a complex

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized
by the cokernel induction to objects with prescribed outer resolutions.
(blueprint: lem-sp-horseshoe-prescribed-row-construction).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.InjectiveResolution

set_option backward.isDefEq.respectTransparency false in
/-- Construct the off-diagonal entries of the biproduct differential by extending
successively into the injective left terms. The initial equation preserves the
specified augmentation, and the recursive equation makes the differential square zero. -/
private theorem offDiagonal
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IC : InjectiveResolution S.X₃)
    (lift : S.X₂ ⟶ IA.cocomplex.X 0) (hlift : S.f ≫ lift = IA.ι.f 0) :
    ∃ t : ∀ n : ℕ, IC.cocomplex.X n ⟶ IA.cocomplex.X (n + 1),
      lift ≫ IA.cocomplex.d 0 1 + S.g ≫ IC.ι.f 0 ≫ t 0 = 0 ∧
      ∀ n, t n ≫ IA.cocomplex.d (n + 1) (n + 2) +
        IC.cocomplex.d n (n + 1) ≫ t (n + 1) = 0 := by
  classical
  -- Descend the first obstruction along S.g and extend across the right augmentation.
  have hu : S.f ≫ (-(lift ≫ IA.cocomplex.d 0 1)) = 0 := by
    simp [← Category.assoc, hlift]
  let u := hS.exact.descToInjective (-(lift ≫ IA.cocomplex.d 0 1)) hu
  have hgu : S.g ≫ u = -(lift ≫ IA.cocomplex.d 0 1) :=
    hS.exact.comp_descToInjective _ _
  let t₀ := Injective.factorThru u (IC.ι.f 0)
  have ht₀ : IC.ι.f 0 ≫ t₀ = u := Injective.comp_factorThru _ _
  have hz : IC.ι.f 0 ≫ (-(t₀ ≫ IA.cocomplex.d 1 2)) = 0 := by
    have := hS.epi_g
    apply (cancel_epi S.g).1
    rw [Preadditive.comp_neg, ← Category.assoc, ht₀, Preadditive.comp_neg, ← Category.assoc, hgu]
    simp [Category.assoc]
  let t₁ := IC.exact₀.descToInjective (-(t₀ ≫ IA.cocomplex.d 1 2)) hz
  have ht₁ : IC.cocomplex.d 0 1 ≫ t₁ = -(t₀ ≫ IA.cocomplex.d 1 2) :=
    IC.exact₀.comp_descToInjective _ _
  -- Retain two consecutive entries and their compatibility in the induction state.
  let P := fun n : ℕ ↦ Σ' a : IC.cocomplex.X n ⟶ IA.cocomplex.X (n + 1),
    Σ' b : IC.cocomplex.X (n + 1) ⟶ IA.cocomplex.X (n + 2),
      IC.cocomplex.d n (n + 1) ≫ b = -(a ≫ IA.cocomplex.d (n + 1) (n + 2))
  let step : ∀ n, P n → P (n + 1) := fun n p ↦ by
    have hz' : IC.cocomplex.d n (n + 1) ≫
        (-(p.2.1 ≫ IA.cocomplex.d (n + 2) (n + 3))) = 0 := by
      rw [Preadditive.comp_neg, ← Category.assoc, p.2.2]
      simp [Category.assoc]
    exact ⟨p.2.1, (IC.exact_succ n).descToInjective _ hz',
      (IC.exact_succ n).comp_descToInjective _ hz'⟩
  let p : ∀ n, P n := fun n ↦ Nat.rec (motive := P) ⟨t₀, t₁, ht₁⟩ step n
  refine ⟨fun n ↦ (p n).1, ?_, ?_⟩
  · change lift ≫ IA.cocomplex.d 0 1 + S.g ≫ IC.ι.f 0 ≫ t₀ = 0
    rw [ht₀, hgu, add_neg_cancel]
  · intro n
    change (p n).1 ≫ IA.cocomplex.d (n + 1) (n + 2) +
      IC.cocomplex.d n (n + 1) ≫ (p n).2.1 = 0
    rw [(p n).2.2, add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- Extend a chosen initial horseshoe embedding to compatible augmented complexes
with short exact rows. This only constructs a complex: positive-degree exactness,
injectivity of its terms, and the quasi-isomorphism of its augmentation are not
part of the conclusion and are verified separately.

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized
by the following cokernel induction to prescribed resolutions of objects.
(blueprint: lem-sp-horseshoe-prescribed-row-construction).

Proof: put `K.X 0 = IA.X 0 ⊞ IC.X 0` and augment by
`w = (lift, S.g ≫ IC.ι.f 0)`. The hypothesis on `lift` gives a morphism from
`S` to the split biproduct row. Its outer vertical maps are monomorphisms,
so the snake lemma makes `w` a monomorphism and gives a short exact sequence
of the three cokernels. For either outer resolution, exactness identifies the
cokernel of its augmentation with a subobject of its degree-one term. Use
these two embeddings at the next step. Extend the left embedding across the
monomorphism of the cokernel sequence into the injective left degree-one term;
pair this extension with the right embedding composed with the quotient map.
This gives the middle embedding into the degree-one biproduct. Apply the
snake lemma again to obtain the next short exact sequence of cokernels.
Continue recursively, always using the embeddings supplied by exactness of
the prescribed outer resolutions into their next injective terms.

Define each middle differential as the quotient map onto the current middle
cokernel followed by its new embedding. Consecutive differentials compose to
zero because the quotient kills the preceding embedding. The squares defining
the induced cokernel maps, followed by the embedding squares, show that the
biproduct inclusions and projections commute with differentials; hence they
assemble into `α` and `β`. Their composite is zero degreewise. The degree-zero
squares give the augmentation equalities. Each row is the canonical split
biproduct row. The identity in degree zero gives `e₀` and its equation.
Finally, the first middle differential factors through the cokernel of `w`
followed by a monomorphism, so its kernel is the image of `w`; this is the
asserted degree-zero exactness. The augmentation is the complex map determined
by `w`, which is killed by the first differential. -/
theorem exists_horseshoe_prescribed_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IC : InjectiveResolution S.X₃)
    (lift : S.X₂ ⟶ IA.cocomplex.X 0) (hlift : S.f ≫ lift = IA.ι.f 0) :
    ∃ (K : CochainComplex C ℕ)
      (ι : (CochainComplex.single₀ C).obj S.X₂ ⟶ K)
      (α : IA.cocomplex ⟶ K) (β : K ⟶ IC.cocomplex),
      IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ ι ∧
      ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      (∃ e₀ : K.X 0 ≅ IA.cocomplex.X 0 ⊞ IC.cocomplex.X 0,
        ι.f 0 ≫ e₀.hom = biprod.lift lift (S.g ≫ IC.ι.f 0)) ∧
      (ShortComplex.mk (ι.f 0) (K.d 0 1) (by simp)).Exact ∧
      ∃ (hαβ : α ≫ β = 0), ∀ n : ℕ,
        ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact := by
  classical
  obtain ⟨t, ht₀, ht⟩ := offDiagonal S hS IA IC lift hlift
  -- The two diagonal entries are prescribed; only the upper-right entry is new.
  let X := fun n ↦ IA.cocomplex.X n ⊞ IC.cocomplex.X n
  let d : ∀ n, X n ⟶ X (n + 1) := fun n ↦
    biprod.desc (IA.cocomplex.d n (n + 1) ≫ biprod.inl)
      (biprod.lift (t n) (IC.cocomplex.d n (n + 1)))
  have hd₁ (n) : biprod.inl ≫ d n = IA.cocomplex.d n (n + 1) ≫ biprod.inl := by
    simp [d]
  have hd₂ (n) : d n ≫ biprod.snd = biprod.snd ≫ IC.cocomplex.d n (n + 1) := by
    ext <;> simp [d]
  have hd (n) : d n ≫ d (n + 1) = 0 := by
    apply biprod.hom_ext'
    · simp [d, Category.assoc]
    · apply biprod.hom_ext
      · simpa [d, Category.assoc, Preadditive.comp_add, Preadditive.add_comp] using ht n
      · simp [d, Category.assoc]
  let K := CochainComplex.of X d hd
  let α : IA.cocomplex ⟶ K := CochainComplex.ofHom (fun _ ↦ biprod.inl) (by
    intro n
    simpa [K] using hd₁ n)
  let β : K ⟶ IC.cocomplex := CochainComplex.ofHom (fun _ ↦ biprod.snd) (by
    intro n
    simpa [K] using (hd₂ n).symm)
  let w : S.X₂ ⟶ K.X 0 := biprod.lift lift (S.g ≫ IC.ι.f 0)
  have hw : w ≫ K.d 0 1 = 0 := by
    apply biprod.hom_ext
    · simpa [w, K, CochainComplex.of.d, d, Category.assoc,
        Preadditive.comp_add, Preadditive.add_comp] using ht₀
    · simp [w, K, CochainComplex.of.d, d, Category.assoc]
  let ι := (CochainComplex.fromSingle₀Equiv K S.X₂).symm ⟨w, hw⟩
  refine ⟨K, ι, α, β, ?_, ?_, ?_, ?_, ?_⟩
  · apply (CochainComplex.fromSingle₀Equiv K S.X₁).injective
    apply Subtype.ext
    dsimp [CochainComplex.fromSingle₀Equiv]
    simp only [α, ι, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    ext <;> simp [w, hlift, Category.assoc]
  · apply (CochainComplex.fromSingle₀Equiv IC.cocomplex S.X₂).injective
    apply Subtype.ext
    dsimp [CochainComplex.fromSingle₀Equiv]
    simp [ι, β, w]
  · exact ⟨Iso.refl _, by simp [ι, w]⟩
  · simp only [ι, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    change T ⟶ K.X 0 at x
    change x ≫ K.d 0 1 = 0 at hx
    have hxc : (x ≫ biprod.snd) ≫ IC.cocomplex.d 0 1 = 0 := by
      simpa [K, CochainComplex.of.d, hd₂, Category.assoc] using hx =≫ biprod.snd
    -- Lift the right coordinate, then correct the residual left coordinate.
    let c := IC.exact₀.lift (x ≫ biprod.snd) hxc
    have hc : c ≫ IC.ι.f 0 = x ≫ biprod.snd := IC.exact₀.lift_f _ _
    have := hS.epi_g
    obtain ⟨T', π, hπ, b, hb⟩ := surjective_up_to_refinements_of_epi S.g c
    let y := π ≫ x - b ≫ w
    have hy : y ≫ K.d 0 1 = 0 := by simp [y, Preadditive.sub_comp, Category.assoc, hx, hw]
    have hys : y ≫ biprod.snd = 0 := by
      simp only [y, Preadditive.sub_comp, Category.assoc, w, biprod.lift_snd]
      rw [← Category.assoc b S.g (IC.ι.f 0), ← hb, Category.assoc, hc, sub_self]
    have hyd : (y ≫ biprod.fst) ≫ IA.cocomplex.d 0 1 = 0 := by
      have hy' : y ≫ d 0 ≫ biprod.fst = 0 := by
        simpa [K, CochainComplex.of.d, Category.assoc] using hy =≫ biprod.fst
      rw [show d 0 ≫ biprod.fst =
          biprod.fst ≫ IA.cocomplex.d 0 1 + biprod.snd ≫ t 0 by
            ext <;> simp [d, Preadditive.comp_add]] at hy'
      simpa [Preadditive.comp_add, ← Category.assoc, hys] using hy'
    let a := IA.exact₀.lift (y ≫ biprod.fst) hyd
    have ha : a ≫ IA.ι.f 0 = y ≫ biprod.fst := IA.exact₀.lift_f _ _
    refine ⟨T', π, hπ, b + a ≫ S.f, ?_⟩
    apply biprod.hom_ext
    · have ha' : a ≫ IA.ι.f 0 = π ≫ x ≫ biprod.fst - b ≫ lift := by
        simpa [y, w, Preadditive.sub_comp, Category.assoc] using ha
      simp only [Preadditive.add_comp, Category.assoc, w, biprod.lift_fst, hlift]
      rw [ha']
      abel
    · simp only [w, Preadditive.add_comp, Category.assoc, biprod.lift_snd, S.zero_assoc]
      rw [← Category.assoc b S.g (IC.ι.f 0), ← hb, Category.assoc, hc]
      simp
  · have hαβ : α ≫ β = 0 := by
      ext n
      simp [α, β]
    refine ⟨hαβ, fun n ↦ ?_⟩
    exact (ShortComplex.Splitting.ofHasBinaryBiproduct
      (IA.cocomplex.X n) (IC.cocomplex.X n)).shortExact

end CategoryTheory.InjectiveResolution
