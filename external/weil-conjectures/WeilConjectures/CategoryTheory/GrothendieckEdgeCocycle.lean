/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.CategoryTheory.GrothendieckCocycleComparison

/-!
# Cocycle description of the Grothendieck left edge

Source: Stacks Project, Derived Categories, Lemma 015N and the second spectral sequence
of Lemma 015J (blueprint: lem-pc-grothendieck-edge-cocycle).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem interval_isZero
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (Y : Abelian.SpectralObject C EInt) [Y.IsFirstQuadrant]
    (m : ℤ) (a : ℕ)
    (h : ∀ q : ℕ, q < a → IsZero ((Y.H m).obj
      (ComposableArrows.mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))))) :
    IsZero ((Y.H m).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : ℤ))))) := by
  induction a with
  | zero =>
    exact Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl m
  | succ a ih =>
    exact (Y.exact₂
      (homOfLE (bot_le : (⊥ : EInt) ≤ (a : ℤ)))
      (homOfLE (show ((a : ℤ) : EInt) ≤ ((a + 1 : ℤ) : EInt) by simp))
      (homOfLE bot_le) (Subsingleton.elim _ _) m).isZero_of_both_isZero
        (ih fun q hq => h q (by omega)) (h a (by omega))

private theorem spectral_left_edge_isIso
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (Y : Abelian.SpectralObject C EInt) [Y.IsFirstQuadrant]
    (h : ∀ p q : ℕ, 0 < p → IsZero ((Y.H (p + q : ℕ)).obj
      (ComposableArrows.mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp)))))
    (n : ℕ) : IsIso (Y.leftEdge n) := by
  have hz (m : ℕ) (hm : n ≤ m) :
      IsZero ((Y.H m).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (n : ℤ))))) := by
    apply interval_isZero
    intro q hq
    have hp : 0 < m - q := by omega
    have hmq : m - q + q = m := by omega
    simpa only [hmq] using h (m - q) q hp
  have := Y.isIso_H_map_twoδ₁Toδ₀' (n : ℤ) ((n : ℤ) + 1) rfl
    ⊥ ((n : ℤ) : EInt) ⊤ bot_le le_top (hz n le_rfl)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hz (n + 1) (by omega))
  have := Y.isIso_H_map_self_succ_top n
  dsimp [Abelian.SpectralObject.leftEdge]
  infer_instance

/-- The left edge is induced by applying `G` to the cocycle quotient, and is an
isomorphism when the positive columns vanish. The equation is written after precomposition
with `G` of the cycles, identified with the cycles of the mapped complex by left exactness.
Source: Stacks Project, Derived Categories, Tags 015N and 015J
(blueprint: lem-pc-grothendieck-edge-cocycle).

Proof:
1. The image under G of the cycle inclusion is killed by the next differential,
   by functoriality and iCycles_d. Lift it to the cycles of GF(I) by liftCycles.
   Its inclusion equation is liftCycles_i. Apply grothendieck_cocycle_comparison
   to this lift for the quotient equation; this is the remaining CE comparison.
2. Define the filtration directly by transporting the spectral object's image
   filtration through grothendieckSpectralObjectHBotTopIso. Monotonicity of the
   image filtration makes it decreasing. The first-quadrant bounds give top at
   zero and bottom at n+1. These imply finiteness, exhaustiveness and separation.
3. Identify H^{p+q}(q,q+1) with R^p G(R^q F(X)). Under the vanishing hypothesis,
   H^m(q,q+1) is zero for q<n and m=n or n+1. Induction on the upper endpoint,
   using exact₂ and H^m(bot,0)=0, gives H^n(bot,n)=H^{n+1}(bot,n)=0.
   Thus H^n(bot,top) -> H^n(n,top) is an isomorphism by the spectral object's
   exact sequence. H^n(n,n+1) -> H^n(n,top) is already an isomorphism by the
   first-quadrant bound. Their composite is leftEdge. Transporting it through
   the canonical abutment and target isomorphisms proves the collapse clause.
-/
theorem grothendieck_left_edge_cocycle
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) :
    (∀ n : ℕ, ∃ c :
        G.obj (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n) ⟶
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n,
      c ≫ (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n =
        G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n) ∧
      c ≫ (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n ≫
          (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
          (F.grothendieckLeftEdgeMap G hFG n).app X ≫
          G.map (I.isoRightDerivedObj F n).hom =
        G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n)) ∧
    (∃ HF : ∀ n : ℕ, DecreasingFiltration (((F ⋙ G).rightDerived n).obj X),
      (∀ (n : ℕ) (p : ℤ), (HF n).step p =
        (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app X)).obj
          ((F.grothendieckSpectralObject G X).imageFiltration (n : ℤ)
            ((n : ℤ) + 1 - p))) ∧
      (∀ n : ℕ, (HF n).IsFinite ∧ (HF n).IsExhaustive ∧ (HF n).IsSeparated)) ∧
    ((∀ p q : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj X))) →
      ∀ n : ℕ, IsIso ((F.grothendieckLeftEdgeMap G hFG n).app X)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro n
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let T := ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    have hk : G.map (K.iCycles n) ≫ T.d n (n + 1) = 0 := by
      change G.map (K.iCycles n) ≫ G.map (K.d n (n + 1)) = 0
      rw [← G.map_comp, K.iCycles_d, G.map_zero]
    let c := T.liftCycles (G.map (K.iCycles n)) (n + 1) (by simp) hk
    refine ⟨c, T.liftCycles_i _ _ _ _, ?_⟩
    exact grothendieck_cocycle_comparison F G hFG X I n c
      (T.liftCycles_i _ _ _ _)
  · let Y := F.grothendieckSpectralObject G X
    let e (n : ℕ) := (F.grothendieckSpectralObjectHBotTopIso G hFG n).app X
    let HF (n : ℕ) : DecreasingFiltration (((F ⋙ G).rightDerived n).obj X) :=
      { F := fun p => (Subobject.«exists» (e n).hom).obj
          (Y.imageFiltration n ((n : ℤ) + 1 - p))
        F_succ_le p :=
          leOfHom ((Subobject.«exists» (e n).hom).map
            (homOfLE (Y.imageFiltration_mono n (by omega)))) }
    refine ⟨HF, fun n p => rfl, ?_⟩
    intro n
    have htop : (HF n).step 0 = ⊤ := by
      dsimp [HF]
      rw [Y.imageFiltration_eq_top n _ (by omega)]
      rw [Subobject.exists_iso_map, Subobject.map_top]
      exact Subobject.mk_eq_top_of_isIso _
    have hbot : (HF n).step ((n : ℤ) + 1) = ⊥ := by
      dsimp [HF]
      rw [Y.imageFiltration_eq_bot n _ (by omega)]
      rw [Subobject.exists_iso_map, Subobject.map_bot]
    refine ⟨⟨0, (n : ℤ) + 1, htop, hbot⟩, ?_, ?_⟩
    · intro S hS
      exact top_unique (htop ▸ hS 0)
    · intro S hS
      exact bot_unique (hbot ▸ hS ((n : ℤ) + 1))
  · intro h n
    have hzero (p q : ℕ) (hp : 0 < p) :
        IsZero (((F.grothendieckSpectralObject G X).H (p + q : ℕ)).obj
          (ComposableArrows.mk₁ (homOfLE
            (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp)))) := by
      exact (h p q hp).of_iso
        ((F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1)
          (by push_cast; rfl) rfl rfl).app X)
    have := spectral_left_edge_isIso (F.grothendieckSpectralObject G X) hzero n
    change IsIso ((F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
      (F.grothendieckSpectralObject G X).leftEdge n ≫
        (F.grothendieckLeftEdgeTargetIso G n).hom.app X)
    infer_instance

end CategoryTheory
