/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import all WeilConjectures.CategoryTheory.Exact.ExactFunctorCouple
import WeilConjectures.CategoryTheory.AbutmentImageFiltration
import WeilConjectures.CategoryTheory.KInjectiveBridge
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Hypercohomology filtrations for an étale base-change square

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1315;
Stacks Project, Tags 0DDE and 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

The three functors are Rf_*, g^{-1}Rf_*, and Rf'_*g'^{-1}. The generic construction
below applies cohomology to their images of the canonical truncation triangles.
The index of `pageCouple` is the actual page minus two.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option synthInstance.maxSize 2048

universe u v₁ u₁ v₂ u₂ w₁ w₂ uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Transport an exact pair along three object isomorphisms. -/
private theorem exact_transport
    {C : Type uC} [Category.{vC, uC} C] [Abelian C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (w : a ≫ b = 0) (h : (ShortComplex.mk a b w).Exact)
    {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (h₁ : e₁.hom ≫ a' = a ≫ e₂.hom)
    (h₂ : e₂.hom ≫ b' = b ≫ e₃.hom) :
    ∃ w' : a' ≫ b' = 0, (ShortComplex.mk _ _ w').Exact := by
  have w' : a' ≫ b' = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, h₁, Category.assoc, h₂,
      ← Category.assoc, w, zero_comp, comp_zero]
  refine ⟨w', ShortComplex.exact_of_iso ?_ h⟩
  exact ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂

/-- Naturality of an indexed morphism with respect to equality transports. -/
private theorem cast_naturality
    {C : Type uC} [Category.{vC, uC} C] {I : Type*} (X Y : I → C)
    (f : ∀ i, X i ⟶ Y i) {i j : I} (h : i = j) :
    eqToHom (congrArg X h) ≫ f j = f i ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

/-- Naturality with a common target, including its final equality transports. -/
private theorem cast_naturality_last
    {C : Type uC} [Category.{vC, uC} C] {I : Type*} (X Y : I → C)
    (f : ∀ i, X i ⟶ Y i) {i j : I} (h : i = j) {Z : C}
    (hi : Y i = Z) (hj : Y j = Z) :
    eqToHom (congrArg X h) ≫ f j ≫ eqToHom hj = f i ≫ eqToHom hi := by
  subst j
  simp

/-- Reindex a family of morphisms along equalities of the two indices. -/
private theorem reindex_hom
    {C : Type uC} [Category.{vC, uC} C] (X Y : ℤ → ℤ → C)
    (f : ∀ p q, X p q ⟶ Y p q) {p q p' q' : ℤ}
    (hp : p = p') (hq : q = q') :
    eqToHom (congrArg₂ X hp hq) ≫ f p' q' =
      f p q ≫ eqToHom (congrArg₂ Y hp hq) := by
  subst p'
  subst q'
  simp

/-- Adding the zero bidegree does not change an exact pair. -/
private theorem exact_zero_right
    {C : Type uC} [Category.{vC, uC} C] [Abelian C] (D E : ℤ → ℤ → C)
    (g : ∀ p q, D p q ⟶ E p q)
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1)) (p q : ℤ)
    (h : ∃ w : g p q ≫ f p q = 0, (ShortComplex.mk _ _ w).Exact) :
    ∃ w : (g p q ≫ eqToHom (by simp : E p q = E (p + (0 : ℕ)) (q - (0 : ℕ)))) ≫
        f (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
      (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨w, h⟩ := h
  refine exact_transport _ _ w h (Iso.refl _) (eqToIso ?_) (eqToIso ?_) ?_ ?_
  · simp
  · simp
  · simp
  · exact reindex_hom E (fun p q ↦ D (p + 2) (q - 1)) f
      (by simp) (by simp)

/-- Postcomposing the last map with an equality isomorphism preserves exactness. -/
private theorem exact_cast_last
    {C : Type uC} [Category.{vC, uC} C] [Abelian C] {X Y Z Z' : C}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : ∃ w : a ≫ b = 0, (ShortComplex.mk _ _ w).Exact) (hz : Z = Z') :
    ∃ w : a ≫ (b ≫ eqToHom hz) = 0, (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨w, h⟩ := h
  exact exact_transport a b w h (Iso.refl _) (Iso.refl _) (eqToIso hz)
    (by simp) (by simp)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
  (K : CochainComplex.Plus A)
omit [Abelian A] [HasDerivedCategory A] in
private theorem inverse_square {V W V' W' : A} (a : V ⟶ W) (b : V' ⟶ W')
    (e : V ≅ V') (f : W ≅ W') (h : a ≫ f.hom = e.hom ≫ b) :
    b ≫ f.inv = e.inv ≫ a := by
  rw [← cancel_epi e.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h]
  simp

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option backward.isDefEq.respectTransparency false in
private theorem hypercohomology_initialG (p q : ℤ) :
    (hypercohomologyCouple F K).initialG p q =
      (DerivedCategory.homologyFunctor B (p + q)).map
        (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) := by
  simp only [hypercohomologyCouple, BigradedExactCouple.initialG,
    BigradedExactCouple.ofShifted_g, hypercohomologyG, Category.assoc]
  change (DerivedCategory.homologyFunctor B (p + q)).map
      (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
        eqToHom (by simp : hypercohomologyE F K p q =
          hypercohomologyE F K (p + (0 : ℕ)) (q - (0 : ℕ))) ≫
        eqToHom (by simp : hypercohomologyE F K (p + (0 : ℕ)) (q - (0 : ℕ)) =
          hypercohomologyE F K p q) = _
  erw [eqToHom_trans, eqToHom_refl]
  exact Category.comp_id _
-/

attribute [local irreducible] TruncationCouple.bridgeIso

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option backward.isDefEq.respectTransparency false in
private theorem hypercohomology_bridge [IsGrothendieckAbelian.{v₁} A]
    [IsGrothendieckAbelian.{v₂} B] (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] :
    (∀ p q : ℤ, hypercohomologyAlpha G.rightDerivedFunctor K p q ≫
        (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K (q + 1)) (p - 1 + (q + 1))).hom =
      (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.alpha G K p q) ∧
    (∀ p q : ℤ, hypercohomologyBoundary G.rightDerivedFunctor K p q ≫
        (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K (q - 1)) (p + 2 + (q - 1))).hom =
      (TruncationCouple.bridgeIso G
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom ≫
        TruncationCouple.f G K p q) ∧
    (∀ p q : ℤ, (hypercohomologyCouple G.rightDerivedFunctor K).initialG p q ≫
        (TruncationCouple.bridgeIso G
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom =
      (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.g G K p q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    simp only [hypercohomologyAlpha, TruncationCouple.alpha, Category.assoc,
      Iso.hom_inv_id_assoc]
    congr 1
    exact (eqToHom_iso_hom_naturality
      (fun n : ℤ ↦ TruncationCouple.bridgeIso (G)
        (TruncationCouple.truncation K (q + 1)) n)
      (by omega : p + q = p - 1 + (q + 1))).symm
  · intro p q
    simp only [hypercohomologyBoundary, TruncationCouple.f, Category.assoc,
      Iso.hom_inv_id_assoc]
    congr 1
    exact (eqToHom_iso_hom_naturality
      (fun n : ℤ ↦ TruncationCouple.bridgeIso (G)
        (TruncationCouple.truncation K (q - 1)) n)
      (by omega : p + q + 1 = p + 2 + (q - 1))).symm
  · intro p q
    rw [hypercohomology_initialG]
    simp only [TruncationCouple.g, TruncationCouple.derivedTriangle,
      Functor.mapTriangle, TruncationCouple.triangle,
      Pretriangulated.Triangle.mk_mor₂, Iso.hom_inv_id_assoc]
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private theorem hypercohomology_convergence_of_bounds (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (hypercohomologyD F K p q))
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (hypercohomologyE F K p q))
    (hiso : ∀ n : ℤ, IsIso (hypercohomologyAbutmentMap F K n n)) :
    (∀ n : ℤ, (hypercohomologyFiltration F K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration F K n).step p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p → ((hypercohomologyFiltration F K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple F K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple F K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple F K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple F K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦ (DerivedCategory.homologyFunctor B m).obj
            (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap F K n (n - p)) ∧
        (∀ n p : ℤ, (Subobject.«exists» (eqToHom (hT n))).obj
          (((hypercohomologyCouple F K).imageFiltration n (T n)).step p) =
            (hypercohomologyFiltration F K n).step p)) := by
  let X := hypercohomologyCouple F K
  let H (n : ℤ) := (DerivedCategory.homologyFunctor B n).obj
    (F.obj (DerivedCategory.Q.obj K.obj))
  let j (n q : ℤ) : X.D (n - q) q ⟶ H n :=
    eqToHom (by dsimp [X, hypercohomologyCouple, hypercohomologyD]; congr 2; omega) ≫
      hypercohomologyAbutmentMap F K n q
  let c (n : ℤ) : X.D 0 n ⟶ H n :=
    eqToHom (by congr 1; omega) ≫ j n n
  have hco (n p : ℤ) : X.alphaDiagonal n p ≫
      eqToHom (by congr 1; omega) ≫ j n (n - p) =
        eqToHom (by congr 1; omega) ≫ j n (n - (p + 1)) := by
    have ha (p q n t : ℤ) (hn : p + q = n) (ht : q + 1 = t) :
        hypercohomologyAlpha F K p q =
          eqToHom (by unfold hypercohomologyD; rw [hn]; rfl) ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.map (DerivedCategory.Q.map
              (eqToHom (congrArg (fun r : ℤ ↦ K.obj.truncLE r)
                (by omega : q = t - 1)) ≫ TruncationCouple.transition K t))) ≫
          eqToHom (by unfold hypercohomologyD; rw [← ht, ← hn]; congr 2; omega) := by
      subst n
      subst t
      simp only [eqToHom_refl, Category.id_comp]
      rfl
    dsimp only [BigradedExactCouple.alphaDiagonal]
    simp only [X, hypercohomologyCouple, BigradedExactCouple.ofShifted_alpha,
      Category.assoc]
    rw [ha (p + 1) (n - (p + 1)) n (n - p) (by omega) (by omega)]
    simp only [j, hypercohomologyAbutmentMap, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    have hq : n - (p + 1) = n - p - 1 := by omega
    simp only [Category.assoc, TruncationCouple.transition_comp_ιTruncLE]
    have hι := eqToHom_naturality (fun r : ℤ ↦ K.obj.ιTruncLE r) hq
    simp only [eqToHom_refl, Category.comp_id] at hι
    rw [hι]
  have hn : ∀ (n p : ℤ) (_ : 0 ≤ p), eqToHom (by congr 1 <;> omega) ≫ j n (n - p) =
      X.incomingAlphaIter p.toNat 0 n ≫ c n := by
    let k (n p : ℤ) : X.D p (n - p) ⟶ H n :=
      eqToHom (by congr 1; omega) ≫ j n (n - p)
    have hk (n p : ℤ) : X.alphaDiagonal n p ≫ k n p = k n (p + 1) := hco n p
    have hi (n : ℤ) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
        X.alphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ k n (p - r) =
          eqToHom (by congr 1; omega) ≫ k n p := by
      induction r generalizing p q with
      | zero =>
        simp only [BigradedExactCouple.alphaIter, eqToHom_trans_assoc]
        have he := eqToHom_naturality (k n) (by omega : p - (↑(0 : ℕ) : ℤ) = p)
        simp only [eqToHom_refl, Category.comp_id] at he
        rw [he, eqToHom_trans_assoc]
      | succ r ih =>
        simp only [BigradedExactCouple.alphaIter, Category.assoc, eqToHom_trans_assoc]
        have he := ih (p - 1) (q + 1) (by omega)
        have hidx : p - ↑(r + 1 : ℕ) = p - 1 - ↑r := by omega
        have hcast := eqToHom_naturality (k n) hidx
        simp only [eqToHom_refl, Category.comp_id] at hcast
        rw [hcast, eqToHom_trans_assoc, he]
        have hq : q = n - p := by omega
        subst q
        have he' := hk n (p - 1)
        simp only [BigradedExactCouple.alphaDiagonal, Category.assoc] at he'
        dsimp only [k] at he' ⊢
        simp only [eqToHom_trans_assoc] at he' ⊢
        convert! he' using 1 <;> congr! 4 <;> omega
    intro n p hp
    lift p to ℕ using hp
    have he := hi n p (p : ℤ) (n - p) (by omega)
    have hend := eqToHom_naturality (k n) (by omega : (p : ℤ) - p = 0)
    simp only [eqToHom_refl, Category.comp_id] at hend
    rw [hend, eqToHom_trans_assoc] at he
    simp only [k, eqToHom_trans_assoc] at he
    simp only [Int.toNat_natCast, BigradedExactCouple.incomingAlphaIter, c,
      Category.assoc, eqToHom_trans_assoc]
    convert! he.symm using 1 <;> congr! 4 <;> omega
  have hc (n : ℤ) : IsIso (c n) := by
    dsimp [c, j]
    infer_instance
  obtain ⟨Z, T₀, hT₀, hT₀ι, hsupport, _⟩ :=
    BigradedExactCouple.halfPlaneConvergence X a hD hE
  obtain ⟨FA, FH, hFA, hFA0, hFH, hj, htop, hbot, hfinite, hneg, T, hT, hι, hconv⟩ :=
    abutment_image_filtration X a hD hE Z H j c (fun _ ↦ rfl) hc hco hn
  have ext {V : B} (F G : DecreasingFiltration V) (h : F.F = G.F) : F = G := by
    cases F
    cases G
    cases h
    rfl
  have hFH' (n : ℤ) : FH n = hypercohomologyFiltration F K n := by
    apply ext
    funext p
    simpa only [DecreasingFiltration.step, hypercohomologyFiltration, j,
      imageSubobject_comp_eq_of_epi] using hj n p
  refine ⟨?_, ?_, ⟨T, Z, hT, hconv, ?_, ?_⟩⟩
  · intro n
    refine ⟨hFH' n ▸ (hfinite n).1, ?_, ?_⟩
    · intro p hp
      rw [← hFH' n]
      exact htop n p hp
    · intro p hp
      apply Subobject.mk_eq_bot_iff_zero.mp
      simpa only [Subobject.mk_arrow, hFH' n] using hbot n p hp
  · intro r p q hr hpq
    by_contra hnz
    have hs := hsupport (r - 2) (p + q) p q rfl hnz
    rcases hpq with hq | hp
    · omega
    · omega
  · intro n p
    simpa only [j, Category.assoc, eqToHom_trans_assoc] using hι n p
  · intro n p
    rw [Subobject.exists_obj_eq_imageSubobject]
    change imageSubobject ((imageSubobject ((T n).ι p)).arrow ≫ eqToHom (hT n)) = _
    rw [← imageSubobject_comp_eq_of_epi (factorThruImageSubobject ((T n).ι p)),
      ← Category.assoc, imageSubobject_arrow_comp, hι]
    simp only [j, eqToHom_trans_assoc, imageSubobject_comp_eq_of_epi]
    rfl
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option backward.isDefEq.respectTransparency false in
private theorem hypercohomology_exactFunctor
    {C : Type uC} [Category.{vC, uC} C] [Abelian C] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (∃ δ : ∀ p q : ℤ, G.obj ((hypercohomologyCouple
      F K).D p q) ≅ (hypercohomologyCouple
      (F ⋙ G.mapDerivedCategory) K).D p q,
      ∃ φ : ∀ (r : ℕ) (p q : ℤ),
        G.obj (((hypercohomologyCouple
          F K).pageCouple r).E p q) ≅
          ((hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).pageCouple r).E p q,
        (∀ p q : ℤ, δ p q =
          (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
            (F.obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K q).obj))) ∧
        (∀ p q : ℤ, φ 0 p q =
          (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
            (F.obj (DerivedCategory.Q.obj
              (TruncationCouple.cohomologyComplex K q).obj))) ∧
        (∀ p q : ℤ, G.map ((hypercohomologyCouple
          F K).alpha p q) ≫
          (δ (p - 1) (q + 1)).hom = (δ p q).hom ≫ (hypercohomologyCouple
            (F ⋙ G.mapDerivedCategory) K).alpha p q) ∧
        (∀ p q : ℤ, G.map ((hypercohomologyCouple
          F K).f p q) ≫
          (δ (p + 2) (q - 1)).hom = (φ 0 p q).hom ≫ (hypercohomologyCouple
            (F ⋙ G.mapDerivedCategory) K).f p q) ∧
        (∀ p q : ℤ, G.map ((hypercohomologyCouple
          F K).initialG p q) ≫
          (φ 0 p q).hom = (δ p q).hom ≫
            (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).initialG p q) ∧
        (∀ (r : ℕ) (p q : ℤ),
          G.map (((hypercohomologyCouple
            F K).pageCouple r).d p q) ≫
            (φ r (p + 2 + r) (q - 1 - r)).hom =
          (φ r p q).hom ≫ ((hypercohomologyCouple (F ⋙ G.mapDerivedCategory)
            K).pageCouple r).d p q)) := by
  let δ (p q : ℤ) := (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj))
  let ε (p q : ℤ) := (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K q).obj))
  have hα (p q : ℤ) : G.map ((hypercohomologyCouple F K).alpha p q) ≫
      (δ (p - 1) (q + 1)).hom =
        (δ p q).hom ≫ (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).alpha p q := by
    simp only [hypercohomologyCouple, BigradedExactCouple.ofShifted_alpha,
      hypercohomologyAlpha, Functor.comp_map]
    exact exact_homology_naturality_cast G
      (F.map (DerivedCategory.Q.map
        (eqToHom (congrArg (fun n : ℤ ↦ K.obj.truncLE n)
          (by omega : q = (q + 1) - 1)) ≫ TruncationCouple.transition K (q + 1))))
      (p + q) (p - 1 + (q + 1)) (by omega)
  have hf (p q : ℤ) : G.map ((hypercohomologyCouple F K).f p q) ≫
      (δ (p + 2) (q - 1)).hom =
        (ε p q).hom ≫ (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).f p q := by
    simp only [hypercohomologyCouple, BigradedExactCouple.ofShifted_f,
      hypercohomologyBoundary]
    have h := exact_boundary_naturality_cast G
      (F.mapTriangle.obj (TruncationCouple.triangle K q))
      (p + q) (p + q + 1) (p + 2 + (q - 1)) (by omega) (by omega)
    have hδ : DerivedCategory.HomologySequence.δ
        (G.mapDerivedCategory.mapTriangle.obj
          (F.mapTriangle.obj (TruncationCouple.triangle K q))) (p + q) (p + q + 1) =
        DerivedCategory.HomologySequence.δ
          ((F ⋙ G.mapDerivedCategory).mapTriangle.obj (TruncationCouple.triangle K q))
            (p + q) (p + q + 1) := by
      dsimp only [DerivedCategory.HomologySequence.δ, Functor.shiftMap,
        Functor.mapTriangle, Functor.mapTriangle_obj, Pretriangulated.Triangle.mk,
        Functor.comp_obj, Functor.comp_map]
      simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
    rw [hδ] at h
    exact h
  have hg (p q : ℤ) : G.map ((hypercohomologyCouple F K).initialG p q) ≫
      (ε p q).hom =
        (δ p q).hom ≫ (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).initialG p q := by
    rw [hypercohomology_initialG, hypercohomology_initialG]
    exact (G.mapDerivedCategoryHomologyFunctorIso (p + q)).hom.naturality
      (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q)))
  obtain ⟨φ, hφ, hd⟩ := exact_couple_pages G (hypercohomologyCouple F K)
    (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K) δ ε hα hf hg
  refine ⟨δ, φ, fun _ _ => rfl, hφ, hα, ?_, ?_, hd⟩
  · intro p q
    rw [hφ]
    exact hf p q
  · intro p q
    rw [hφ]
    exact hg p q
-/

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

attribute [local irreducible] TruncationCouple.bridgeIso

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/ -- The three spectral sequences have the stated E₂ terms, finite filtrations, and unconditional
  convergence, the first couple is the truncation couple of def-sp-truncation-couple for f_*
  through `TruncationCouple.bridgeIso`, and the middle one is the exact inverse image of the
  first.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: Transfer the lower cohomological bound along the supplied representative isomorphism.
  Each of the three functors preserves lower bounds: use the bounded-below compatibility of
  right derived functors and exact inverse image. The truncation cone then shows that the
  degree-n abutment map from tau≤n is invertible. Apply half-plane convergence and
  lem-sp-abutment-image-filtration, using the actual truncation inclusions as the cocone, to
  obtain the finite canonical image filtrations and all three abutments. The bridge equations
  follow from the definitions and equality-transport naturality. Shift the single complex to
  degree zero to identify each E₂ term with the classical right derived functor. For termwise
  inverse image, factor the mapped truncation inclusion through the target truncation; its
  components are invertible below the cutoff, its top cycle map is invertible by exactness,
  and both sides vanish above it. The cohomology comparison is natural and commutes with shifts,
  hence with all three couple maps, including the boundary. Apply lem-sp-exact-functor-couple
  and couple functoriality in both directions; cancellation at the kernel inclusions and
  quotient projections proves that the page maps are inverses. Finally, exactness preserves
  the epi-image factorization of each abutment map, giving the stated filtration comparison. - /
theorem hypercohomologyFiltrations_spec
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p =
        ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).page r p
        q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n (T
                n)).step p) =
            (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p)) ∧
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K
        n).step p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p).arrow =
          0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
        K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            n).obj
            ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologyBaseChangeFunctor f g) K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).imageFiltration n
                (T n)).step p) =
            (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p)) ∧
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step
        p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor f' g')
        K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            n).obj
            ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
                (T n)).step p) =
            (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p)) ∧
    (∀ p q : ℤ, hypercohomologyAlpha (hypercohomologyFirstFunctor f) K p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K (q + 1)) (p - 1 + (q + 1))).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.alpha (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ p q : ℤ, hypercohomologyBoundary (hypercohomologyFirstFunctor f) K p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K (q - 1)) (p + 2 + (q - 1))).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom ≫
        TruncationCouple.f (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ p q : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).initialG p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.g (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).E p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q))) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).E p q ≅
        (upperStar AddCommGrpCat.{u + 1} g).obj
          (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q)))) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).E p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f').rightDerived p).obj
          ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)))) ∧
    (∀ i : ℤ, i < a → IsZero
      ((((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj).X i)) ∧
    (∀ q : ℤ, ∃ c :
        ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (K.obj.truncLE q) ≅
        CochainComplex.truncLE
          (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K.obj) q,
      c.hom ≫
        CochainComplex.ιTruncLE
          (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K.obj) q =
        ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).map
          (K.obj.ιTruncLE q)) ∧
    (∀ q : ℤ, Nonempty
      ((((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj).homology q ≅ (upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q))) ∧
    (∃ δ : ∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).obj ((hypercohomologyCouple
      (hypercohomologyFirstFunctor f) K).D p q) ≅ (hypercohomologyCouple
      (hypercohomologyBaseChangeFunctor f g) K).D p q,
      ∃ φ : ∀ (r : ℕ) (p q : ℤ),
        (upperStar AddCommGrpCat.{u + 1} g).obj (((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).pageCouple r).E p q) ≅
          ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E p q,
        (∀ p q : ℤ, δ p q =
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso (p + q)).app
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K q).obj))) ∧
        (∀ p q : ℤ, φ 0 p q =
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso (p + q)).app
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.cohomologyComplex K q).obj))) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).alpha p q) ≫
          (δ (p - 1) (q + 1)).hom = (δ p q).hom ≫ (hypercohomologyCouple
            (hypercohomologyBaseChangeFunctor f g) K).alpha p q) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).f p q) ≫
          (δ (p + 2) (q - 1)).hom = (φ 0 p q).hom ≫ (hypercohomologyCouple
            (hypercohomologyBaseChangeFunctor f g) K).f p q) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).initialG p q) ≫
          (φ 0 p q).hom = (δ p q).hom ≫ (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f
            g) K).initialG p q) ∧
        (∀ (r : ℕ) (p q : ℤ),
          (upperStar AddCommGrpCat.{u + 1} g).map (((hypercohomologyCouple
            (hypercohomologyFirstFunctor f) K).pageCouple r).d p q) ≫
            (φ r (p + 2 + r) (q - 1 - r)).hom =
          (φ r p q).hom ≫ ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
            K).pageCouple r).d p q)) ∧
    (∀ n : ℤ, ∃ c : (upperStar AddCommGrpCat.{u + 1} g).obj
        ((DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ≅
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
      c = (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso n).app
        ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ∧
      ∀ p : ℤ, imageSubobject ((upperStar AddCommGrpCat.{u + 1} g).map
          ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow ≫ c.hom) =
        (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p) := by
  have haK (q : ℤ) (hq : q < a) : IsZero (K.obj.homology q) :=
    (ha q hq).of_iso
      (((DerivedCategory.homologyFunctorFactors _ q).app K.obj).symm ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e)
  have hF₁ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologyFirstFunctor f).obj M).IsGE n :=
    rightDerived_preserves_isGE _ M n
  have hF₂ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologyBaseChangeFunctor f g).obj M).IsGE n := by
    have := hF₁ M n hM
    exact Functor.isGE_mapDerivedCategory_obj _ _ n
  have hF₃ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologySecondFunctor f' g').obj M).IsGE n := by
    have := Functor.isGE_mapDerivedCategory_obj
      (upperStar AddCommGrpCat.{u + 1} g') M n
    exact rightDerived_preserves_isGE _ _ n
  obtain ⟨hD₁, hE₁, hi₁⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologyFirstFunctor f) K a haK hF₁
  obtain ⟨hD₂, hE₂, hi₂⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologyBaseChangeFunctor f g) K a haK hF₂
  obtain ⟨hD₃, hE₃, hi₃⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologySecondFunctor f' g') K a haK hF₃
  obtain ⟨hb₁, hp₁, hc₁⟩ :=
    hypercohomology_convergence_of_bounds (hypercohomologyFirstFunctor f) K a hD₁ hE₁ hi₁
  obtain ⟨hb₂, hp₂, hc₂⟩ :=
    hypercohomology_convergence_of_bounds (hypercohomologyBaseChangeFunctor f g) K a hD₂ hE₂ hi₂
  obtain ⟨hb₃, hp₃, hc₃⟩ :=
    hypercohomology_convergence_of_bounds (hypercohomologySecondFunctor f' g') K a hD₃ hE₃ hi₃
  obtain ⟨hα, hf, hg⟩ := hypercohomology_bridge K (lowerStar AddCommGrpCat.{u + 1} f)
  refine ⟨hb₁, hp₁, hc₁, hb₂, hp₂, hc₂, hb₃, hp₃, hc₃, hα, hf, hg, ?_⟩
  have e₁ (p : ℕ) (q : ℤ) :
      hypercohomologyE (hypercohomologyFirstFunctor f) K p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q) :=
    (DerivedCategory.homologyFunctor _ ((p : ℤ) + q)).mapIso
        ((hypercohomologyFirstFunctor f).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ q).app (K.obj.homology q)).symm) ≪≫
      single_cohomology_iso (hypercohomologyFirstFunctor f) (K.obj.homology q) p q ≪≫
      (lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorObjSingleFunctorIso
        (K.obj.homology q) p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    exact ⟨e₁ p q⟩
  · intro p q
    exact ⟨((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso
        ((p : ℤ) + q)).symm.app _ ≪≫
      (upperStar AddCommGrpCat.{u + 1} g).mapIso (e₁ p q)⟩
  · intro p q
    exact ⟨(DerivedCategory.homologyFunctor _ ((p : ℤ) + q)).mapIso
        ((hypercohomologySecondFunctor f' g').mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ q).app (K.obj.homology q)).symm) ≪≫
      (DerivedCategory.homologyFunctor _ ((p : ℤ) + q)).mapIso
        ((hypercohomologyFirstFunctor f').mapIso
          (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategorySingleFunctor q).app
            (K.obj.homology q))) ≪≫
      single_cohomology_iso (hypercohomologyFirstFunctor f')
        ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)) p q ≪≫
      (lowerStar AddCommGrpCat.{u + 1} f').homologyRightDerivedFunctorObjSingleFunctorIso
        ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)) p⟩
  · intro i hi
    exact (upperStar AddCommGrpCat.{u + 1} g').map_isZero (hterms i hi)
  · intro q
    exact exact_truncation_comparison (upperStar AddCommGrpCat.{u + 1} g') K.obj q
  · intro q
    exact ⟨((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplexHomologyIso
      (.up ℤ) q).app K.obj⟩
  · exact hypercohomology_exactFunctor (hypercohomologyFirstFunctor f) K
      (upperStar AddCommGrpCat.{u + 1} g)
  · intro n
    let G := upperStar AddCommGrpCat.{u + 1} g
    let c := (G.mapDerivedCategoryHomologyFunctorIso n).app
      ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))
    refine ⟨c, rfl, ?_⟩
    intro p
    let i := hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)
    change imageSubobject (G.map (imageSubobject i).arrow ≫ c.hom) = _
    rw [← imageSubobject_comp_eq_of_epi (G.map (factorThruImageSubobject i))
      (G.map (imageSubobject i).arrow ≫ c.hom)]
    rw [← Functor.map_comp_assoc, imageSubobject_arrow_comp]
    have hc := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
      ((hypercohomologyFirstFunctor f).map (DerivedCategory.Q.map
        (K.obj.ιTruncLE (n - p))))
    dsimp only [Functor.comp_map] at hc
    change G.map i ≫ c.hom = _ at hc
    rw [hc, imageSubobject_comp_eq_of_epi]
    rfl
-/

end AlgebraicGeometry.Etale
