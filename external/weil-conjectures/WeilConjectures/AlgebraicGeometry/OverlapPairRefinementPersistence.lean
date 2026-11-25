/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.OverlapPairSquareChartTransport
import WeilConjectures.AlgebraicGeometry.OverlapIteratedComparisonRefinement

/-! # A step of persistent pairwise overlap lifting

Source: Stacks Project, Tag 01ZR, first proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

private theorem pair_square_chart_transport_exists
    {Y Y' Z : Scheme.{u}} (V : Y.OpenCover.{u}) (V' : Y'.OpenCover.{u})
    (α : V'.I₀ → V.I₀) (r : Y' ⟶ Y) (ρ : ∀ d, V'.X d ⟶ V.X (α d))
    (hr : ∀ d, ρ d ≫ V.f (α d) = V'.f d ≫ r)
    (p : Z ⟶ Y) (p' : Z ⟶ Y')
    (A : (d : V.I₀) → (V.X d).Modules)
    (A' : (d : V'.I₀) → (V'.X d).Modules) (M : Z.Modules)
    (c : ∀ d, (Scheme.Modules.pullback (ρ d)).obj (A (α d)) ≅ A' d)
    (δ : ∀ d, (V'.pullback₁ p').X d ⟶ (V.pullback₁ p).X (α d))
    (hδf : ∀ d, δ d ≫ (V.pullback₁ p).f (α d) = (V'.pullback₁ p').f d)
    (hδv : ∀ d, δ d ≫ V.pullbackHom p (α d) = V'.pullbackHom p' d ≫ ρ d)
    (ε : ∀ d, (Scheme.Modules.pullback (V.pullbackHom p d)).obj (A d) ≅
      (Scheme.Modules.pullback ((V.pullback₁ p).f d)).obj M)
    (ε' : ∀ d, (Scheme.Modules.pullback (V'.pullbackHom p' d)).obj (A' d) ≅
      (Scheme.Modules.pullback ((V'.pullback₁ p').f d)).obj M)
    (hε : ε' =
    (fun d ↦ (Scheme.Modules.pullback (V'.pullbackHom p' d)).mapIso (c d).symm ≪≫
      pullbackCompOfEq (V'.pullbackHom p' d) (ρ d)
        (δ d ≫ V.pullbackHom p (α d)) (hδv d).symm (A (α d)) ≪≫
      (pullbackCompOfEq (δ d) (V.pullbackHom p (α d))
        (δ d ≫ V.pullbackHom p (α d)) rfl (A (α d))).symm ≪≫
      (Scheme.Modules.pullback (δ d)).mapIso (ε (α d)) ≪≫
      pullbackCompOfEq (δ d) ((V.pullback₁ p).f (α d))
        ((V'.pullback₁ p').f d) (hδf d) M))
    (a b : V'.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (V.f (α a)) (V.f (α b)))).obj
        (A (α a)) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f (α a)) (V.f (α b)))).obj
        (A (α b)))
    (hs : overlapPairSquare V A p
      ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M) ε (α a) (α b) φ) :
    ∃ φ' : (Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).obj (A' a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).obj (A' b),
      overlapPairSquare V' A' p'
        ((modulesPseudofunctor.toDescentData (V'.pullback₁ p').f).obj M) ε' a b φ' := by
  refine ⟨_, overlap_pair_square_chart_transport V V' α r ρ hr p p'
    A A' M c δ hδf hδv ε ε' hε a b φ hs⟩

/-- A compatible map on one pair stays compatible under refinement of the stage.
No finite presentation, quasi-coherence, affineness or limit hypothesis is used.
Source: Stacks Project, Tag 01ZR, first proof, successive Zariski restrictions;
Mathlib pseudofunctor pullHom composition and pullback overlapIteratedComparison coherence.
(blueprint: lem-pc-fp-overlap-pair-refinement-persistence).

Proof: For each chart use overlapRefinementHom U q q' r hr to map the later
chart to the earlier one. Pull the given pair map along the induced map of the
universal overlaps. Conjugate by pullback composition and the equality
of the composites with the original chart projections to obtain a map between
the prescribed later modules. The limit charts of the later cover map to those
of the earlier cover because p' followed by r is p. Pull back the given square
along the induced map of limit overlaps. Naturality of mapComp and the
pseudofunctor pentagon identify its left and right component comparisons with
overlapIteratedComparison U q' p' t h' N M e. PullHom composition identifies its middle map
with the pullback of the newly constructed stage map. The descent datum of M
is natural under this overlap map, so the resulting equality is the desired
square. These constructions use universal pullback maps, and still apply when
a chart or overlap is empty; no map is chosen from a mere existence statement. -/
theorem overlap_pair_map_refinement_persistence
    {X Y Y' Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (q' : Y' ⟶ X) (r : Y' ⟶ Y) (hr : r ≫ q = q')
    (p : Z ⟶ Y) (p' : Z ⟶ Y') (t : Z ⟶ X)
    (h : p ≫ q = t) (h' : p' ≫ q' = t) (hp : p' ≫ r = p)
    (N : (a : U.I₀) → (U.X a).Modules) (M : Z.Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f a)).obj M)
    (a b : U.I₀) :
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    let W := V.pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    (∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
      overlapPairSquare V A p D ε a b φ) →
    let V' := U.pullback₁ q'
    let A' := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q' d)).obj (N d)
    let W' := V'.pullback₁ p'
    let D' := (modulesPseudofunctor.toDescentData W'.f).obj M
    let ε' := overlapIteratedComparison U q' p' t h' N M e
    ∃ φ' : (Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).obj (A' a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).obj (A' b),
      overlapPairSquare V' A' p' D' ε' a b φ' := by
  dsimp only
  rintro ⟨φ, hs⟩
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let V' : Y'.OpenCover.{u} := U.pullback₁ q'
  let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
  let A' := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q' d)).obj (N d)
  let ρ := overlapRefinementHom U q q' r hr
  have hρf : ∀ d, ρ d ≫ V.f d = V'.f d ≫ r :=
    overlapRefinementHom_map U q q' r hr
  have hρ : ∀ d, ρ d ≫ U.pullbackHom q d = U.pullbackHom q' d :=
    overlapRefinementHom_comp U q q' r hr
  let c : ∀ d, (Scheme.Modules.pullback (ρ d)).obj (A d) ≅ A' d := fun d ↦
    pullbackCompOfEq (ρ d) (U.pullbackHom q d) (U.pullbackHom q' d) (hρ d) (N d)
  let δ : ∀ d, (V'.pullback₁ p').X d ⟶ (V.pullback₁ p).X d := fun d ↦
    pullback.lift ((V'.pullback₁ p').f d) (V'.pullbackHom p' d ≫ ρ d) (by
      rw [Category.assoc, hρf d, ← Category.assoc, V'.pullbackHom_map p' d,
        Category.assoc, hp])
  have hδf : ∀ d, δ d ≫ (V.pullback₁ p).f d = (V'.pullback₁ p').f d := by
    intro d
    exact pullback.lift_fst _ _ _
  have hδv : ∀ d, δ d ≫ V.pullbackHom p d = V'.pullbackHom p' d ≫ ρ d := by
    intro d
    exact pullback.lift_snd _ _ _
  have he := overlap_iterated_comparison_refinement U q q' p p' t h h' N M e
    ρ hρ δ hδf hδv
  exact pair_square_chart_transport_exists V V' (fun d ↦ d) r ρ hρf p p'
    A A' M c δ hδf hδv (overlapIteratedComparison U q p t h N M e)
    (overlapIteratedComparison U q' p' t h' N M e) he a b φ hs

end AlgebraicGeometry
