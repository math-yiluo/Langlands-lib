/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLineCounitBaseChange

/-! # Base change for the affine trace tower -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The counit equation is preserved by ordered pasting of exchange squares.
Source: adjunction counit naturality and functoriality
(blueprint: lem-amb-affine-trace-tower-counit-base-change). -/
private theorem tower_counit_baseChange {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {L' : ∀ d, C' (d + 1) ⥤ C' d}
    {R : ∀ d, C d ⥤ C (d + 1)} {R' : ∀ d, C' d ⥤ C' (d + 1)}
    (a : ∀ d, L d ⊣ R d) (a' : ∀ d, L' d ⊣ R' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K))
    (h : ∀ d K, (e d).app ((R d).obj K) ≫
      (L' d).map (r d K).hom ≫ (a' d).counit.app ((B d).obj K) =
        (B d).map ((a d).counit.app K)) (d : ℕ) (K : C 0) :
    (affineTraceExchangeTower L L' B e d).app ((affineTraceRightTower R d).obj K) ≫
      (affineTraceLeftTower L' d).map (affineTraceRightExchangeTower R R' B r d K).hom ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) =
    (B 0).map ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero =>
    rw [affineTraceExchangeTower_zero]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (B 0).map (𝟙 K)
    simp
  | succ d ih =>
    let M := (affineTraceRightTower R d).obj K
    let q := affineTraceRightExchangeTower R R' B r d K
    have hn := (a' d).counit.naturality q.hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hi : (e d).app ((R d).obj M) ≫
        (L' d).map ((r d M).hom ≫ (R' d).map q.hom) ≫
        (a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K)) =
        (B d).map ((a d).counit.app M) ≫ q.hom := by
      rw [Functor.map_comp, Category.assoc, hn]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ q.hom) (h d M)
    rw [affineTraceExchangeTower_succ, affineTraceAdjunctionTower_counit_succ,
      affineTraceAdjunctionTower_counit_succ]
    change (_ ≫ (affineTraceLeftTower L' d).map ((e d).app ((R d).obj M))) ≫
      (affineTraceLeftTower L' d).map
        ((L' d).map ((r d M).hom ≫ (R' d).map q.hom)) ≫
      (affineTraceLeftTower L' d).map
        ((a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K))) ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) = _
    have hi' := congrArg (fun z ↦ (affineTraceLeftTower L' d).map z) hi
    simp only [Functor.map_comp, Category.assoc] at hi'
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hi']
    have he := (affineTraceExchangeTower L L' B e d).naturality ((a d).counit.app M)
    simp only [Functor.comp_map] at he
    change _ ≫ (affineTraceExchangeTower L L' B e d).app M =
      (affineTraceExchangeTower L L' B e d).app
        ((L d).obj ((affineTraceRightTower R (d + 1)).obj K)) ≫ _ at he
    rw [← Category.assoc, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [ih, ← Functor.map_comp]

/-- The actual coordinate-tower counit commutes with its pasted base-change exchange.
Source: blueprint lemma-integral-linear-character--1, proof steps 8--9
(blueprint: lem-amb-affine-trace-tower-counit-base-change).

Proof: first establish the one-coordinate counit square. Expand the affine-line
exchange into the proper exchange, open-extension exchange and compactification
comparison. The inverse open exchange is the mate of the open unit, so its two
counit composites transpose to the identity. Paste with the normalized projective
counit square hD. The compactification comparisons cancel by naturality.
Now induct on d, for arbitrary K. At zero every tower comparison and counit is
identity. At a successor write the composite counit as the preceding left functor
applied to the inner counit, followed by the preceding counit. The right comparison
is the inner line comparison followed by the line right functor applied to the
preceding right comparison. Commute the latter map past the inner counit using
counit naturality, and apply the one-coordinate square. Exchange naturality moves
the resulting mapped inner counit past the preceding exchange. Finally apply the
induction hypothesis and functoriality of pullback. This gives the displayed actual
morphism equality, including all associativity identifications. Naturality of the
line exchange follows from its composite natural transformation; induction gives
naturality of the tower exchange. No stalkwise equality of derived morphisms is
used. The identity change of base, d=0, empty base and zero coefficient ring obey
the same unit and triangle equations. -/
theorem affineTraceTowerCounit_baseChange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    affineTraceExchange A g d ((affineTraceRight A N hA S d).obj K) ≫
        (affineTraceLeft A S' d).map
          (affineTraceRightBaseChange A N hA t g hS d K).hom ≫
        (affineTraceAdjunction A N hA t D S'
          (affineTracePullbackInvertible N g hS) d).counit.app
            ((ordinaryFinitePullback A g).obj K) =
      (ordinaryFinitePullback A g).map
        ((affineTraceAdjunction A N hA t D S hS d).counit.app K) := by
  unfold affineTraceExchange affineTraceRightBaseChange affineTraceAdjunction
  apply tower_counit_baseChange
  intro e M
  let := affineTraceNoetherian S e
  let := affineTraceNoetherian S' e
  simpa only [affineTraceLineExchange] using
    affineTraceLineCounit_baseChange A N hN hA t D hD
      (affineTraceMap g e) (affineTraceInvertible N S hS e) M

end AlgebraicGeometry.Etale
