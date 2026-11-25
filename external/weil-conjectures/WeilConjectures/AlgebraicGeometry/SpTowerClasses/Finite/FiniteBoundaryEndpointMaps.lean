/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
/-! # The source and root maps after finite scalar evaluation -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u c₀ v₀ r₀
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem scalarUnitSection
    {C : Type c₀} [Category.{v₀} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{max c₀ v₀ r₀} C]
    {R R' : Sheaf J CommRingCat.{max c₀ v₀ r₀}} (φ : R ⟶ R')
    (S : SemilinearSections.ScalarData.{c₀, v₀, max c₀ v₀ r₀} φ)
    (M : SemilinearSections.Mod.{c₀, v₀, max c₀ v₀ r₀} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    (S.ordinaryAdjunction.unit.app M).val.app U x =
      SemilinearSections.scalarExtensionSection.{c₀, v₀, r₀} φ S M U x := by
  change _ = (eqToHom (S.model.obj_eq M).symm).val.app U
    (SemilinearSections.extensionUnit.{c₀, v₀, max c₀ v₀ r₀} φ M U x)
  rw [← S.unit_section M U x]
  exact (congrArg (fun a ↦ a.val.app U ((S.ordinaryAdjunction.unit.app M).val.app U x))
    (eqToIso (S.model.obj_eq M)).hom_inv_id).symm

attribute [local irreducible] SemilinearSections.scalarExtensionSection

/-- The integer generator followed by scalar restriction and evaluation is the
canonical finite quotient. Source: classes proof (2), evaluation on constants.
(blueprint: lem-sfb-finite-source-map).
Proof: the morphism and section equations of Forget identify the composite on
constant k with its image under the coefficient ring map. This image is k, since
ring maps preserve integer casts. The uniqueness of finiteQuotient concludes. -/
theorem finiteBoundary_sourceMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :
    (abEvaluation T n).map (integerGenerator T (Rrings l T) c.reduction.forget) ≫
      (c.reduction.forget.F ⋙ abEvaluation T n).map (scalarGenerator l E T) ≫
      (finiteScalarForgetIso l E c n).hom.app (coefficient T (Arings l E T)) =
      finiteQuotient l E T n := by
  apply (finiteQuotient_existsUnique l E T n).unique ?_
    (finiteQuotient_existsUnique l E T n).exists.choose_spec
  intro U k
  let x : (coefficient T (Rrings l T)).val.obj (op (n, U.unop)) :=
    (k.down : ((Rrings l T).obj (op n)).obj.obj U)
  have hx := (integerGenerator_existsUnique T (Rrings l T)
    c.reduction.forget).exists.choose_spec n U k
  have hf := finiteBoundary_forgetMapSection T _ c.reduction.forget
    (scalarGenerator l E T) n U x _ hx
  have hs := (scalarGenerator_existsUnique l E T).exists.choose_spec (op (n, U.unop)) x
  have hy := hf.trans (hs.trans (heq_of_eq (map_intCast
    ((coefficientSystemMap l E T).hom.app (op (n, U.unop))).hom k.down)))
  exact (finiteScalarForgetIso_section l E c n (coefficient T (Arings l E T)) U _ _ hy).heq

/-- The ordinary scalar unit on roots evaluates to the canonical map z to 1 tensor z.
Source: classes proof (2), the pure-tensor equation of lineEvaluation.
(blueprint: lem-sfb-finite-root-map).
Proof: transport z back along rootForget and then to its actual module section x.
The section equation of the ordinary scalar unit sends x to its scalarExtensionSection.
The evaluation comparison forgets only the action. Apply the defining equation of
lineEvaluation with scalar 1 and cancel rootForget and its inverse. The uniqueness
of finiteRootMap concludes. No flatness or generation hypothesis on roots is used. -/
theorem finiteBoundary_rootMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :
    (abEvaluation T n).map c.rootForget.inv ≫
      (c.reduction.forget.F ⋙ abEvaluation T n).map
        (c.scalar.ordinaryAdjunction.unit.app c.rootModule) ≫
      (finiteScalarForgetIso l E c n).hom.app (lineModule l E c) ≫
      (finiteForget l E T n).map (lineEvaluation l E c n).hom =
      finiteRootMap l E T n := by
  apply (finiteRootMap_existsUnique l E T n).unique ?_
    (finiteRootMap_existsUnique l E T n).exists.choose_spec
  intro U z
  let x' := (c.rootForget.inv.app (op n)).hom.app U z
  let x : c.rootModule.val.obj (op (n, U.unop)) :=
    (eqToHom (c.reduction.forget.sections c.rootModule n U)) x'
  have hx : HEq x' x := (finiteBoundary_cast_heq
    (c.reduction.forget.sections c.rootModule n U) x').symm
  let η := c.scalar.ordinaryAdjunction.unit.app c.rootModule
  have hf := finiteBoundary_forgetMapSection T _ c.reduction.forget η n U x x' hx
  have he := finiteScalarForgetIso_section l E c n (lineModule l E c) U _ _ hf
  have hu : η.val.app (op (n, U.unop)) x =
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l E T)
        c.scalar c.rootModule (op (n, U.unop)) x :=
    scalarUnitSection.{u + 1, u, u + 1} (coefficientSystemMap l E T)
      c.scalar c.rootModule (op (n, U.unop)) x
  have hv₀ : HEq (η.val.app (op (n, U.unop)) x)
      ((1 : (SpTowerShriek.B l E T n).obj.obj U) •
        SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
          (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) := by
    rw [one_smul, hu]
  let v : ((SpTowerShriek.ev l E T n).obj (lineModule l E c)).val.obj U :=
    ((finiteScalarForgetIso l E c n).hom.app (lineModule l E c)).hom.app U
      (((c.reduction.forget.F.map η).app (op n)).hom.app U x')
  have hv : HEq v ((1 : (SpTowerShriek.B l E T n).obj.obj U) •
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) :=
    (heq_of_eq he).trans hv₀
  have hl := (lineEvaluation_existsUnique l E c n).exists.choose_spec U 1 x x' v hx.symm hv
  change (lineEvaluation l E c n).hom.val.app U v = _
  erw [hl]
  have hi := congrArg (fun a ↦ a.hom.app U z) (c.rootForget.app (op n)).inv_hom_id
  change (c.rootForget.hom.app (op n)).hom.app U x' = z at hi
  erw [hi]
end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
