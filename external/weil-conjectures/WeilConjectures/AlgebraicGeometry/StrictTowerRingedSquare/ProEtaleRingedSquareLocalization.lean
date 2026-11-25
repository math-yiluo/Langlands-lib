/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization

/-! The canonical ringed inverse-image square is exact localization of its ordinary square.
Source: Stacks Project, Tag 0D6D.
(blueprint: lem-weil-pbc-ringed-square-localization) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingModulePullback proEtaleRingModuleAdjunction proEtaleRingCompositeCoefficients
  proEtaleCanonicalDerivedPullbackComparison

private theorem composition_localization {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ) :
    proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch =
      Functor.mapDerivedCategoryNatIso (exchangeModuleComposition h k RV RW RZ ck ch) ≪≫
        (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback k RV RW ck)
          (proEtaleRingModulePullback h RW RZ ch)).symm := by
  let a := exchangeModuleComposition h k RV RW RZ ck ch
  let ak := proEtaleRingModuleAdjunction k RV RW ck
  let ah := proEtaleRingModuleAdjunction h RW RZ ch
  let ac := proEtaleRingModuleAdjunction (h ≫ k) RV RZ
    (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
  let e := conjugateIsoEquiv (ak.comp ah) ac a
  have he : (Adjunction.leftAdjointCompIso ak ah ac e).symm = a := by
    apply Iso.ext
    apply (conjugateEquiv (ak.comp ah) ac).injective
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv ak ah ac e
  have hn : ExchangeModuleCompositionNormalized h k RV RW RZ ck ch a :=
    (exchangeModuleComposition_existsUnique h k RV RW RZ ck ch).choose_spec.1
  have H := proEtaleCanonicalDerivedPullback_normalization h k RV RW RZ ck ch
    (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl e hn
  simp only [eqToIso_refl, Iso.refl_trans] at H
  change proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch =
    Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointCompIso ak ah ac e).symm ≪≫
      (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback k RV RW ck)
        (proEtaleRingModulePullback h RW RZ ch)).symm at H
  rw [he] at H
  exact H

private theorem localization_transport
    {U V : Scheme.{t}} (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    {a b : Σ q : U ⟶ V,
      (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj R ≅ S} (h : a = b) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg
        (fun z ↦ proEtaleRingModulePullback z.1 R S z.2) h)) =
      eqToIso (congrArg (fun z ↦ proEtaleRingDerivedPullback z.1 R S z.2) h) := by
  cases h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

/-- The published ambient pullback square is the exact descent of the ordinary square.
Source: Stacks Project, Tag 0D6D
(blueprint: lem-weil-pbc-ringed-square-localization).
Proof: the normalization theorem identifies each canonical derived compositor with
exact localization of the ordinary compositor. Its right-adjoint conjugate has the
same sectionwise fibre-product formula as exchangeModuleComposition, so uniqueness
identifies the ordinary isomorphisms. Exact localization preserves inverse,
composition and equality transport. Substitute these identities into the two
compositors defining the square. -/
theorem StrictTowerRingedSquare.ambientSquare_localization
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) :
    proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
        r.cf r.cg r.cg' r.cf' r.coherent =
      Functor.mapDerivedCategorySquareIso r.exchangeModuleSquare := by
  unfold proEtaleAmbientRingedPullbackComparison
  dsimp only
  rw [composition_localization, composition_localization]
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, StrictTowerRingedSquare.exchangeModuleSquare,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  have ht := localization_transport r.RY r.RX' r.exchangeCoefficients_eq
  rw [ht]

end AlgebraicGeometry.Scheme
