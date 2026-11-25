/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangePaste
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalCompIsoBaseChange

/-!
# Vertical pasting of `Ex_!` along `Δ ≫ p₁ = 𝟙` (the law `H1`)

The law `H1` of `AlgebraicGeometry.Etale.IsoSquare.compEqId_baseChange` is the compatibility of
the compactly supported base change maps of the squares of `Δ`, `p₁` and `𝟙 = Δ ≫ p₁` with the
composition isomorphisms `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`
(`CategoryTheory.Adjunction.ExchangeCompCompatible`). It is the vertical pasting law
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_vert`, once the composition
isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` (built from the chosen
compactifications) is identified with the inverse of
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`
(`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso_tower`), and the equality
`Δ ≫ p₁ = 𝟙` is transported (`AlgebraicGeometry.Etale.exchangeCompCompatible_of_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Comp

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact (f ≫ g)]

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` is the inverse of
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`. -/
theorem rightDerivedLowerShriekCompIso_eq_symm :
    rightDerivedLowerShriekCompIso Λ f g = (unboundedEtaleLowerShriekCompIso Λ f g).symm := by
  have h := unboundedEtaleLowerShriekCompIso_tower Λ f g (HasCompactification.compactification g)
    ((HasCompactification.compactification (f ≫ g)).ofComp
      (HasCompactification.compactification g))
  have hrefl : rightDerivedLowerShriekIso Λ (HasCompactification.compactification g) =
      Iso.refl _ :=
    (unboundedEtaleCompactSupport_comparison_coherence Λ g).1 _
  refine Iso.ext ?_
  rw [Iso.symm_hom, Iso.hom_eq_inv, h, hrefl]
  ext K
  simp only [rightDerivedLowerShriekCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app,
    Iso.refl_inv, NatTrans.id_app, Category.assoc]
  -- the identity is stated at `R(g)_!`, the composite at `Rg_!(c)`
  erw [Category.id_comp]

end Comp

section Paste

variable {X X' Y Y' Z Z' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
  {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}

/-- **Vertical pasting as `ExchangeCompCompatible`**: the compactly supported base change maps
of two stacked cartesian squares and of their pasting are compatible with the composition
isomorphisms `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_vert`). -/
theorem exchangeCompCompatible_of_paste_vert
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Z']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    [QuasiCompact (f ≫ g)] [QuasiCompact (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
      (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqgf)
      (rightDerivedLowerShriekCompIso Λ f g) (rightDerivedLowerShriekCompIso Λ f' g') where
  comp M := by
    rw [rightDerivedLowerShriekCompIso_eq_symm, rightDerivedLowerShriekCompIso_eq_symm]
    simp only [Iso.symm_hom]
    have h := rightDerivedLowerShriekBaseChangeMap_paste_vert (Λ := Λ) sqf sqg sqgf M
    rw [← cancel_mono ((unboundedEtaleLowerShriekCompIso Λ f' g').hom.app
      ((L((vX)^*[ModuleCat.{u + 1} Λ])).obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
    -- the identity is stated at `R.obj (LvX^* M)`, the map at `(LvX^* ⋙ R).obj M`
    erw [Category.comp_id]

/-- Transport of `ExchangeCompCompatible` along equalities `f ≫ g = h`, `f' ≫ g' = h'`: the
composition isomorphisms become `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`. -/
theorem exchangeCompCompatible_of_eq {h : X ⟶ Z} {h' : X' ⟶ Z'}
    (w : f ≫ g = h) (w' : f' ≫ g' = h')
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification h']
    [QuasiCompact h] [QuasiCompact h'] [QuasiCompact f'] [QuasiCompact g']
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqh : IsPullback vX h' h vZ) (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ)
    (H : letI : HasCompactification (f ≫ g) := HasCompactification.of_eq w.symm
      letI : HasCompactification (f' ≫ g') := HasCompactification.of_eq w'.symm
      letI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
      letI : QuasiCompact (f' ≫ g') := by rw [w']; infer_instance
      Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
        (rightDerivedLowerShriekBaseChangeMap Λ sqg)
        (rightDerivedLowerShriekBaseChangeMap Λ sqgf)
        (rightDerivedLowerShriekCompIso Λ f g) (rightDerivedLowerShriekCompIso Λ f' g')) :
    Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
      (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqh)
      (rightDerivedLowerShriekCompIsoOfEq Λ f g h w)
      (rightDerivedLowerShriekCompIsoOfEq Λ f' g' h' w') := by
  subst w w'
  refine ⟨fun M ↦ ?_⟩
  have hM := H.comp M
  simp only [rightDerivedLowerShriekCompIsoOfEq, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact hM

end Paste

namespace IsoSquare

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) [IsIso g'] [IsIso g]

/-- The square of `Δ ≫ p₁` for an isomorphism of squares. -/
lemma isPullback_diagonal_fst :
    IsPullback g' (pullback.diagonal f' ≫ pullback.fst f' f')
      (pullback.diagonal f ≫ pullback.fst f f) g' :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

variable (Λ) [IsSeparated f] [IsSeparated f'] [HasCompactification f] [HasCompactification f']
  [IsNoetherian X] [IsNoetherian X'] [IsNoetherian (pullback f f)] [IsNoetherian (pullback f' f')]
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] [QuasiCompact f] [QuasiCompact f']

/-- **The law `H1`** of `AlgebraicGeometry.Etale.IsoSquare.compEqId_baseChange`: for an
isomorphism of squares, the compactly supported base change maps of the squares of `Δ`, `p₁` and
`𝟙 = Δ ≫ p₁` are compatible with the composition isomorphisms. -/
theorem exchangeCompCompatible_diagonal :
    Adjunction.ExchangeCompCompatible
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fst sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_id g'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
        (pullback.diagonal_fst f))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f') (𝟙 X')
        (pullback.diagonal_fst f')) := by
  refine exchangeCompCompatible_of_eq (pullback.diagonal_fst f) (pullback.diagonal_fst f') _ _
    (isPullback_id g') isPullback_diagonal_fst ?_
  let _ : HasCompactification (pullback.diagonal f ≫ pullback.fst f f) :=
    HasCompactification.of_eq (pullback.diagonal_fst f).symm
  let _ : HasCompactification (pullback.diagonal f' ≫ pullback.fst f' f') :=
    HasCompactification.of_eq (pullback.diagonal_fst f').symm
  have : QuasiCompact (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  have : QuasiCompact (pullback.diagonal f' ≫ pullback.fst f' f') := by
    rw [pullback.diagonal_fst]; infer_instance
  exact exchangeCompCompatible_of_paste_vert _ _ _

end IsoSquare

end AlgebraicGeometry.Etale
