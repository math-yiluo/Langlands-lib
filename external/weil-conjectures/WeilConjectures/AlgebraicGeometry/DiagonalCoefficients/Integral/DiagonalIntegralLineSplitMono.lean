/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
public import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalRankOneIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteIntegralEndpoint

/-! # Split endomorphisms of the shifted integral Tate line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem integral_epi_end_isIso (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (q : End (spIntegralTwist X l E)) [Epi q.asHom] : IsIso q.asHom := by
  let B := condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) X
  let J := Scheme.ProEt.topology X
  let O := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let S := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J B
  let f := S.functor.map q.asHom
  have : Epi f := inferInstance
  obtain ⟨I, U, v, _, _, hc, _, _, _, hIR, _⟩ := spTwists_commonCover X l
  have hU : J.CoversTop U := by
    let hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U v]
    exact Precoverage.generate_mem_toGrothendieck hc
  have he (i : I) : Nonempty ((S.functor.obj (spIntegralTwist X l E)).over (U i) ≅
      (SheafOfModules.unit R).over (U i)) := by
    simpa only [B, S, R, O, J, spSignedTwist, WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower] using
      (hIR E i).1
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    obtain ⟨e⟩ := he i
    have := diagonalLocalRankOne_isIso X O (U i) f e e
    change IsIso ((SheafOfModules.toSheaf (R.over (U i))).map (f.over (U i)))
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact isIso_of_reflects_iso q.asHom S.functor

private theorem zlLine_epi_end_isIso (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (q : End (zlLine l X)) [Epi q.asHom] : IsIso q.asHom := by
  let a := coefficientMap (integralMap.{u} l (bottomField l)) X
  have : IsIso (integralMap.{u} l (bottomField l)) := bottomMap_isIso l
  have : IsIso a := (upperStarFromPoint X).map_isIso _
  let F : Modules (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X ⥤
      Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X := Mod.comap a
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso a).isEquivalence_functor
  let r : End (spIntegralTwist X l (bottomField l)) := .of (F.preimage q.asHom)
  have hr : F.map r.asHom = q.asHom := F.map_preimage q.asHom
  have : Epi (F.map r.asHom) := hr.symm ▸ inferInstance
  have : Epi r.asHom := F.epi_of_epi_map inferInstance
  have : IsIso r.asHom := integral_epi_end_isIso l X (bottomField l) r
  exact hr ▸ F.map_isIso r.asHom

/-- Every split monomorphism from the shifted integral Tate line to itself is invertible.

Source: the local rank-one Tate-line calculation and the fully faithful single functor
(blueprint: lem-diagonal-integral-line-split-mono).

Proof: an epic endomorphism of the integral line is invertible. On a common root cover,
its section-module morphism is an epic map between free rank-one modules; the local
rank-one criterion proves it invertible, and invertibility descends. The bottom-field
coefficient inclusion is an isomorphism, so restriction of scalars transfers this fact
to the specified Z_l line. Fully faithfulness of the shifted single functor lifts a
retraction of the given map to a retraction of an endomorphism of this line. That
retraction is epic, hence invertible; its section is therefore invertible too. -/
theorem diagonalIntegralLine_splitMono_isIso (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (q : End (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X))⟦(2 : ℤ)⟧)) [IsSplitMono q.asHom] : IsIso q.asHom := by
  let G := DerivedCategory.singleFunctor
    (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0 ⋙ shiftFunctor _ (2 : ℤ)
  let r := G.preimage (retraction q.asHom)
  have hr : G.map r = retraction q.asHom := G.map_preimage _
  have : Epi (G.map r) := hr.symm ▸ inferInstance
  have : Epi r := G.epi_of_epi_map inferInstance
  have : IsIso r := zlLine_epi_end_isIso l X (.of r)
  have : IsIso (retraction q.asHom) := hr ▸ G.map_isIso r
  exact IsIso.of_mono_retraction q.asHom

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
