/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangePaste
public import WeilConjectures.CategoryTheory.Adjunction.ExceptionalBaseChangePasteHoriz
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalBaseChangeIso

/-!
# Horizontal pasting of the exceptional base change and the law `H3`

The horizontal pasting law of the compactly supported base change `Ex_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_horiz`) gives, by the mate
calculus (`CategoryTheory.Adjunction.exceptionalBaseChange_paste_horiz'`), the horizontal pasting
law of the exceptional base change `Ex^! : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap_paste_horiz`).

Applied to the two decompositions of the rectangle `p₁' / f` of an isomorphism of squares, it
identifies the comparison `Le^* ω_{p₁} ≅ ω_{p₁'}` of
`AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso` with the exceptional base change of
`p₁` at the unit: this is the law `H3` of
`AlgebraicGeometry.Etale.IsoSquare.compEqId_baseChange`
(`AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso_hom_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Generic

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- The exceptional base change map is the exceptional base change of `Ex_!`. -/
lemma rightDerivedUpperShriekBaseChangeMap_app_eq_exceptionalBaseChange (sq : IsPullback g' f' f g)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
    (rightDerivedUpperShriekBaseChangeMap Λ sq).app N =
      Adjunction.exceptionalBaseChange (rightDerivedUpperShriekAdjunction Λ f)
        (rightDerivedUpperShriekAdjunction Λ f') (rightDerivedLowerShriekBaseChangeMap Λ sq) N := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  change (rightDerivedUpperShriekBaseChangeMap Λ sq).app N =
    Adjunction.exceptionalBaseChange (rightDerivedUpperShriekAdjunction Λ f)
      (rightDerivedUpperShriekAdjunction Λ f') (rightDerivedLowerShriekBaseChangeMap Λ sq) N
  rw [Adjunction.exceptionalBaseChange_eq_mateEquiv_inv_app]
  rfl

/-- `AlgebraicGeometry.Etale.upperShriekBaseChangeMap` is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`. -/
lemma upperShriekBaseChangeMap_eq (sq : IsPullback g' f' f g) :
    upperShriekBaseChangeMap Λ sq = rightDerivedUpperShriekBaseChangeMap Λ sq :=
  rfl

-- `rfl` compares the tensor unit of `constantComplex` with the one inside the definition (deep)
set_option maxRecDepth 20000 in
/-- The base change map of the dualizing complexes, in the vocabulary of `constantComplex`. -/
lemma dualizingComplexBaseChangeMap_eq (sq : IsPullback g' f' f g) :
    dualizingComplexBaseChangeMap Λ sq =
      (rightDerivedUpperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g).hom := by
  rw [leftDerivedUpperStarConstantComplexIso_hom]
  rfl

end Generic

section PasteHoriz

variable {X X' X'' Y Y' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
  {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v₀ : Y'' ⟶ Y} {v' : X' ⟶ X} {w' : X'' ⟶ X'} {v₀' : X'' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
  [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']

/-- **Horizontal pasting of the exceptional base change maps**: for cartesian squares
`sq₁ : v' ≫ f = f' ≫ v` and `sq₂ : w' ≫ f' = f'' ≫ w` side by side with outer square `sq₃`
along `v₀ = w ≫ v` and `v₀' = w' ≫ v'`, the exceptional base change of the outer square is
`Lw'^*` of that of `sq₁` followed by that of `sq₂`, through the composition isomorphisms of the
derived pullbacks. The mate of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_horiz`. -/
theorem rightDerivedUpperShriekBaseChangeMap_paste_horiz
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) (sq₃ : IsPullback v₀' f'' f v₀)
    (hv : v₀ = w ≫ v) (hv' : v₀' = w' ≫ v')
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedUpperShriekBaseChangeMap Λ sq₃).app N =
      (leftDerivedUpperStarComp _ w' v' v₀' hv').hom.app ((R(f)^![Λ]).obj N) ≫
        (L((w')^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekBaseChangeMap Λ sq₁).app N) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq₂).app ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
        (R(f'')^![Λ]).map ((leftDerivedUpperStarComp _ w v v₀ hv).inv.app N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq₁
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq₂
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq₃
  rw [rightDerivedUpperShriekBaseChangeMap_app_eq_exceptionalBaseChange sq₃,
    rightDerivedUpperShriekBaseChangeMap_app_eq_exceptionalBaseChange sq₁,
    rightDerivedUpperShriekBaseChangeMap_app_eq_exceptionalBaseChange sq₂]
  exact Adjunction.exceptionalBaseChange_paste_horiz' _ _ _
    (leftDerivedUpperStarComp _ w' v' v₀' hv') (leftDerivedUpperStarComp _ w v v₀ hv) _ _ _
    (fun K ↦ (rightDerivedLowerShriekBaseChangeMap_paste_horiz sq₁ sq₂ sq₃ hv hv' K).symm) N

end PasteHoriz

namespace IsoSquare

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) [IsIso g'] [IsIso g]

variable (Λ) in
omit [Finite Λ] [IsIso g'] [IsIso g] in
/-- The two factorizations of `L(f' ≫ g)^* Λ_Y ≅ Λ_{X'}` through `g' ≫ f = f' ≫ g`. -/
lemma unit_coherence :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' f (f' ≫ g) sq.w.symm).inv.app
        (constantComplex Λ Y) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
        (constantComplex Λ Y) ≫
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫
      (leftDerivedUpperStarConstantComplexIso Λ f').hom =
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
      (leftDerivedUpperStarConstantComplexIso Λ g').hom := by
  have e₁ :=
    congrArg Iso.hom (leftDerivedUpperStarConstantComplexIso_comp Λ g' f (f' ≫ g) sq.w.symm)
  have e₂ := congrArg Iso.hom (leftDerivedUpperStarConstantComplexIso_comp Λ f' g (f' ≫ g) rfl)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at e₁ e₂
  rw [← e₂, e₁, Iso.inv_hom_id_app_assoc]

variable (Λ) (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
  [HasCompactification f] [HasCompactification f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Y'] [QuasiCompact f]
  [QuasiCompact f']

-- the ascriptions compare `constantComplex` with the tensor unit (deep, fast)
set_option maxRecDepth 20000 in
/-- **The law `H3`** of `AlgebraicGeometry.Etale.IsoSquare.compEqId_baseChange`: the comparison
`Le^* ω_{p₁} ≅ ω_{p₁'}` of `AlgebraicGeometry.Etale.IsoSquare.dualizingComplexFstIso` induced by
the exceptional base change `Lg'^* ω_f ≅ ω_{f'}` is the exceptional base change of `p₁` at the
unit. Both are the exceptional base change of the rectangle `p₁' / f`, by horizontal pasting. -/
theorem dualizingComplexFstIso_hom_eq :
    (dualizingComplexFstIso sq Λ d (IsoSquare.dualizingComplexIso Λ sq)).hom =
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).app (constantComplex Λ X) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g').hom := by
  have S₀ : IsPullback (pullback.snd f f) (pullback.fst f f) f f :=
    (IsPullback.of_hasPullback f f).flip
  have S₀' : IsPullback (pullback.snd f' f') (pullback.fst f' f') f' f' :=
    (IsPullback.of_hasPullback f' f').flip
  have R : IsPullback (map sq ≫ pullback.snd f f) (pullback.fst f' f') f (f' ≫ g) := by
    rw [(commSq_snd sq).w]; exact S₀'.paste_horiz sq
  have h1 := rightDerivedUpperShriekBaseChangeMap_paste_horiz (Λ := Λ) S₀ (isPullback_fst sq) R
    sq.w.symm rfl (constantComplex Λ Y)
  have h2 := rightDerivedUpperShriekBaseChangeMap_paste_horiz (Λ := Λ) sq S₀' R rfl
    (commSq_snd sq).w (constantComplex Λ Y)
  -- the pasting law `h1 = h2`, solved for the second decomposition
  have hE : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd f' f') g'
          (map sq ≫ pullback.snd f f) (commSq_snd sq).w).hom.app (dualizingComplex Λ f) ≫
        (L((pullback.snd f' f')^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ S₀').app
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (map sq) (pullback.snd f f)
          (map sq ≫ pullback.snd f f) rfl).hom.app (dualizingComplex Λ f) ≫
        (L((map sq)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekBaseChangeMap Λ S₀).app (constantComplex Λ Y)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).app
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) ≫
        (R(pullback.fst f' f')^![Λ]).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' f (f' ≫ g) sq.w.symm).inv.app
              (constantComplex Λ Y) ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
              (constantComplex Λ Y)) := by
    have h := congrArg (fun t ↦ t ≫ (R(pullback.fst f' f')^![Λ]).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
        (constantComplex Λ Y))) (h1.symm.trans h2)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Functor.comp_obj] at h
    exact h.symm
  -- naturality of the exceptional base changes along the unit identifications
  have hN := (rightDerivedUpperShriekBaseChangeMap Λ S₀').naturality
    (leftDerivedUpperStarConstantComplexIso Λ g).hom
  have hN2 := (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_fst sq)).naturality
    (leftDerivedUpperStarConstantComplexIso Λ f).hom
  simp only [Functor.comp_map] at hN hN2
  -- the unit coherence, under `Rp₁'^!`
  have hU : (R(pullback.fst f' f')^![Λ]).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' f (f' ≫ g) sq.w.symm).inv.app
            (constantComplex Λ Y) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
            (constantComplex Λ Y)) ≫
        (R(pullback.fst f' f')^![Λ]).map ((L((f')^*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ g).hom) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ f').hom =
      (R(pullback.fst f' f')^![Λ]).map ((L((g')^*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ f).hom) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g').hom := by
    simp only [← Functor.map_comp, Category.assoc, unit_coherence Λ sq]
  -- unfold the comparison
  have hI := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d S₀
  have hI' : IsIso (dualizingComplexBaseChangeMap Λ S₀) :=
    (isIso_dualizingComplexBaseChangeMap_iff Λ S₀).2 inferInstance
  simp only [dualizingComplexFstIso, dualizingComplexPullbackFstIso, IsoSquare.dualizingComplexIso,
    upperShriekBaseChangeMap_eq, derivedSquareUpperStarIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, asIso_hom, asIso_inv, Functor.mapIso_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.map_inv, IsIso.inv_comp_eq, dualizingComplexBaseChangeMap_eq,
    dualizingComplexBaseChangeMap_eq, ← leftDerivedUpperStarConstantComplexIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hN, reassoc_of% hE, Iso.inv_hom_id_app_assoc, hU, ← reassoc_of% hN2]

end IsoSquare

end AlgebraicGeometry.Etale
