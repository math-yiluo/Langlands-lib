/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-!
# Compatibility of the étale cohomology edge map with base change

Source: Stacks Project, Etale Cohomology, Section 03SB, proof of Lemma 0A5D
(blueprint: lem-weil-pbc-edge-map-base-change).

The edge map is written as pullback on cohomology followed by the counit. In the finite
case, its bijectivity and that of the exchange followed by the base-changed edge map give
the two isomorphisms identifying the horizontal pullback maps.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The edge map commutes with cartesian base change, without any hypothesis on `f`.
Source: Stacks Project, Section 03SB, proof of Lemma 0A5D
(blueprint: lem-weil-pbc-edge-map-base-change).

Proof (steps 1--6 of the node):
1. Fix resolutions and unwind the edge maps as pullback followed by the counit. The
exchange map is the adjoint of the square isomorphism followed by pullback of the counit
(definition-underived-base-change-map--1, def-weil-pbc-inverse-image,
lem-weil-pbc-inverse-image-composition, def-weil-pbc-cohomology-pullback,
prose-03-02). Independence of resolutions follows from
proposition-cohomology-p-1-over-henselian--1, clause 1.
2. The induced maps `Sheaf.H.map` preserve composition and identities, by composition
of comparison lifts and functoriality of global sections and cohomology.
3. The adjunct-counit identity (situation-conventions) identifies pullback
of exchange followed by the counit with the square isomorphism followed by pullback
of the original counit; upstream this is `upperStar_map_baseChangeMap_app_counit`.
4. Naturality and composition of cohomological pullback
(proposition-cohomology-p-1-over-henselian--1, clauses 3 and 4) express the left side as
pullback along the diagonal followed by the inverse composition isomorphism and counit.
5. Apply the same naturality and composition clauses to the right side.
6. Substitute step 3 and cancel the composition isomorphisms. Both diagonal maps are
pullback along the same morphism, so the two sides agree. -/
theorem cohomology_edgeMap_baseChange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (cohomologyMap g' F q).comp
        ((Sheaf.H.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F) q).comp
          (cohomologyMap f ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q)) =
      (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
          ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
        ((cohomologyMap f' ((lowerStar AddCommGrpCat.{u + 1} f').obj
          ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
          ((Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) q).comp
            (cohomologyMap g ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q))) := by
  ext x
  change cohomologyMap g' F q
      (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F) q
        (cohomologyMap f ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q x)) =
    Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
      ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q
      (cohomologyMap f' ((lowerStar AddCommGrpCat.{u + 1} f').obj
        ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q
        (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) q
          (cohomologyMap g ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q x)))
  have hleft := cohomologyMap_map g' q
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F)
    (cohomologyMap f ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q x)
  have hright := cohomologyMap_map f' q
    ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)
    (cohomologyMap g ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q x)
  refine hleft.trans ?_
  refine Eq.trans ?_ (congrArg
    (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
      ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q) hright.symm)
  let A := (lowerStar AddCommGrpCat.{u + 1} f).obj F
  let c₁ := (upperStarComp AddCommGrpCat.{u + 1} f' g (g' ≫ f) sq.w).hom.app A
  let c₂ := (upperStarComp AddCommGrpCat.{u + 1} g' f).hom.app A
  let θ := (squareUpperStarIso AddCommGrpCat.{u + 1} sq.toCommSq).hom.app A
  let ε := ((upperStar AddCommGrpCat.{u + 1} g').map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F))
  let β := ((upperStar AddCommGrpCat.{u + 1} f').map
    ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F))
  let ε' := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
    ((upperStar AddCommGrpCat.{u + 1} g').obj F)
  let y := cohomologyMap f' ((upperStar AddCommGrpCat.{u + 1} g).obj A) q
    (cohomologyMap g A q x)
  let z := cohomologyMap g' ((upperStar AddCommGrpCat.{u + 1} f).obj A) q
    (cohomologyMap f A q x)
  let d := cohomologyMap (g' ≫ f) A q x
  have hy : y = Sheaf.H.map c₁ q d := by
    have hcomp (h : X' ⟶ Y) (hh : h = f' ≫ g) :
        y = Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f' g h hh).hom.app A) q
          (cohomologyMap h A q x) := by
      subst h
      exact (cohomologyPullbackFunctorial f' g A q).2.1 x
    exact hcomp (g' ≫ f) sq.w
  have hz : z = Sheaf.H.map c₂ q d := (cohomologyPullbackFunctorial g' f A q).2.1 x
  have hc : c₁ ≫ θ = c₂ := by
    dsimp only [c₁, c₂, θ, squareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hθ : Sheaf.H.map θ q y = z := calc
    _ = Sheaf.H.map θ q (Sheaf.H.map c₁ q d) := congrArg (Sheaf.H.map θ q) hy
    _ = Sheaf.H.map (c₁ ≫ θ) q d := (Sheaf.H.map_comp_apply c₁ θ d).symm
    _ = Sheaf.H.map c₂ q d := congrArg (fun t ↦ Sheaf.H.map t q d) hc
    _ = z := hz.symm
  have hm : β ≫ ε' = θ ≫ ε :=
    upperStar_map_baseChangeMap_app_counit AddCommGrpCat.{u + 1} sq.toCommSq F
  calc
    Sheaf.H.map ε q z = Sheaf.H.map ε q (Sheaf.H.map θ q y) :=
      congrArg (Sheaf.H.map ε q) hθ.symm
    _ = Sheaf.H.map (θ ≫ ε) q y := (Sheaf.H.map_comp_apply θ ε y).symm
    _ = Sheaf.H.map (β ≫ ε') q y := congrArg (fun t ↦ Sheaf.H.map t q y) hm.symm
    _ = Sheaf.H.map ε' q (Sheaf.H.map β q y) := Sheaf.H.map_comp_apply β ε' y

/-- When `f` is finite and the underived exchange is invertible, the vertical comparison
maps in `cohomology_edgeMap_baseChange` are isomorphisms (bijective additive maps).
Thus that identity identifies `g`-pullback with `g'`-pullback through these isomorphisms.
Source: Stacks Project, Section 03SB, proof of Lemma 0A5D
(blueprint: lem-weil-pbc-edge-map-base-change).

Proof (step 7 of the node): finite morphisms are stable under base change
(lem-weil-pbc-finite-morphism-permanence), so `f'` is finite. Both edge maps are bijective
by lemma-finite-morphisms-cohomology--2. The exchange is an isomorphism, hence its
map on cohomology is bijective by step 2. Their composite is bijective. Step 6 then gives
the asserted identification of pullbacks through these two canonical isomorphisms. -/
theorem bijective_edgeMap_baseChange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hEx : IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)) :
    Function.Bijective
        ((Sheaf.H.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app F) q).comp
          (cohomologyMap f ((lowerStar AddCommGrpCat.{u + 1} f).obj F) q)) ∧
      Function.Bijective
        ((Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').counit.app
            ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
          ((cohomologyMap f' ((lowerStar AddCommGrpCat.{u + 1} f').obj
            ((upperStar AddCommGrpCat.{u + 1} g').obj F)) q).comp
            (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) q))) := by
  have := hEx
  have : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  refine ⟨bijective_edgeMap_of_isFinite f F q, ?_⟩
  have hH : Function.Bijective
      (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) q) := by
    refine ⟨?_, ?_⟩
    · intro x y h
      have h' := congrArg
        (Sheaf.H.map (inv ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)) q) h
      simpa only [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id,
        Sheaf.H.map_id_apply] using h'
    · intro y
      refine ⟨Sheaf.H.map
        (inv ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F)) q y, ?_⟩
      rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]
  exact (bijective_edgeMap_of_isFinite f' _ q).comp hH

end AlgebraicGeometry.Etale
