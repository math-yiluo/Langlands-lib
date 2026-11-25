/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedLocallyClosedScalarExtension
import all WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal

/-! # Ordinary scalar extension of the supported regular module

Source: closed/open localization and its tensor projection formula, as used in
paragraph (1) of the diagonal tower coefficient changes.
(blueprint: lem-sfb-diagonal-supported-ordinary-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem scalar_push_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (e : H ⋙ R' ≅ R ⋙ G) (M : A) (N : B) (f : L.obj M ⟶ N) :
    adj'.homEquiv _ _
        ((Adjunction.pushHomOfComapIso adj adj' e).app M ≫ H.map f) =
      G.map (adj.homEquiv _ _ f) ≫ e.inv.app N := by
  have h := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ e.inv) M
  change G.map (adj.unit.app M) ≫ e.inv.app (L.obj M) =
    adj'.unit.app (G.obj M) ≫
      R'.map ((Adjunction.pushHomOfComapIso adj adj' e).app M) at h
  have hn := e.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [adj'.homEquiv_unit, R'.map_comp, ← Category.assoc, ← h,
    Category.assoc, ← hn, adj.homEquiv_unit, G.map_comp, Category.assoc]

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.upperStarLowerStarAdjunction

/-- The specified supported coefficient map is an ordinary extension-of-scalars unit.

Source: literature/stacks-project/proetale.tex, lemma-closed-immersion and
lemma-closed-immersion-complement-retrocompact-exact; closed projection formula;
blueprint latest, diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-sfb-diagonal-supported-ordinary-scalars).

Proof: Let i be the diagonal and j its open complement. The Noetherian hypothesis
makes j quasi-compact. The closed counit identifies i^*i_*Lambda with Lambda;
j^*i_*Lambda is zero. These exact tensor restriction functors jointly detect
isomorphisms, by the closed/open localization sequence.
For the ordinary scalar adjoint q, closed restriction of q is the usual
multiplication Lambda' tensor_Lambda Lambda -> Lambda', which is invertible.
Open restriction has zero source and target and is invertible. Restriction commutes
with extension of scalars, by associativity of the ordinary relative tensor product.
Joint reflection gives that q is invertible. The formula for supportMap is the
pushed coefficient unit followed by the restriction/direct-image comparison, so
adjunction identifies this q with the displayed transpose. The equality imposed
on the underlying regular map fixes that unit, rather than an arbitrary scalar
multiple. There is no flatness assumption on the coefficient map; empty schemes
and zero rings give the same calculation, with zero restrictions allowed. -/
theorem diagonal_supported_ordinary_scalars
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    [IsNoetherian (diagonalSurface Y)]
    (v : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ⟶
      (Mod.comap (coefficientMap a (ProjectiveLine Y))).obj
        (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y))))
    (_hv : v.hom = coefficientMap a (ProjectiveLine Y)) :
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap a (diagonalSurface Y))).homEquiv
        _ _).symm (supportMap a Y v)) := by
  let i := diagonalImmersion Y
  let j := i.openComplement.ι
  have hj : Set.range j = (Set.range i)ᶜ := by
    classical
    ext x
    have hx := Set.ext_iff.mp i.range_eq_compl_range_openComplement_ι x
    change x ∈ Set.range i ↔ x ∉ Set.range i.openComplement.ι at hx
    change x ∈ Set.range i.openComplement.ι ↔ x ∉ Set.range i
    tauto
  let e := Mod.unitComparisonIso (coefficientMap a (ProjectiveLine Y))
  have he : (Mod.extendRestrictAdjunction (coefficientMap a (ProjectiveLine Y))).homEquiv
      _ _ e.hom = v := by
    apply Mod.hom_ext
    change Mod.extendUnitHom (coefficientMap a (ProjectiveLine Y)) _ ≫ e.hom.hom = v.hom
    rw [_hv]
    exact Mod.unitComparison_unit _
  have hp := closed_scalar_iso a j i hj
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
  have hq := scalar_push_transpose
    (Mod.extendRestrictAdjunction (coefficientMap a (ProjectiveLine Y)))
    (Mod.extendRestrictAdjunction (coefficientMap a (diagonalSurface Y)))
    (CondensedRing.comapLowerStarIso a i) _ _ e.hom
  rw [he] at hq
  have hfactor : ((Mod.extendRestrictAdjunction
      (coefficientMap a (diagonalSurface Y))).homEquiv _ _).symm (supportMap a Y v) =
      (CondensedRing.pushHom a i).app _ ≫ (CondensedRing.lowerStar Λ' i).map e.hom := by
    apply ((Mod.extendRestrictAdjunction
      (coefficientMap a (diagonalSurface Y))).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact hq.symm
  rw [hfactor]
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
