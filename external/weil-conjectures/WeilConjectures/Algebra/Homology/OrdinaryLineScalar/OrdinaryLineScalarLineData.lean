/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor

/-! # Ordinary signed-line tensor and derived scalar extension

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint main-20261015,
Tate-twist local freeness, proof (3).
(blueprint: lem-pur-ordinary-line-scalar-line-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  KFlatFixedTensor.representativeIso compute signedLinePower scalarTensorPower
  LineUnbounded.localizedCancellation LineUnbounded.cancellation
  LineUnbounded.pureTensor ScalarHomOrdinary.pure

set_option backward.isDefEq.respectTransparency.types false

section LineConstruction

set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] monoidalCategory
  tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction

private theorem tensor_kflat_generic
    {A : Type ua} [Category.{va} A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
    [HasColimitsOfSize.{0, 0} A]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (M : A) [PreservesFiniteLimits (tensorRight M)]
    [PreservesFiniteColimits (tensorRight M)] (P : CochainComplex A ℤ)
    (hP : ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F P (curriedTensor A)).Acyclic) :
    ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F
        (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) (curriedTensor A)).Acyclic := by
  intro F hF i
  have : ∀ (K K' : CochainComplex A ℤ), HomologicalComplex.HasTensor K K' :=
    fun K K' ↦ inferInstance
  have h : (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor F P (curriedTensor A))).ExactAt i :=
    (hP F hF i).map (tensorRight M)
  have c := CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor A) M
  have e := HomologicalComplex.associator F P ((CochainComplex.singleFunctor A 0).obj M) ≪≫
    (((curriedTensor A).map₂CochainComplex).obj F).mapIso (c.app P)
  exact HomologicalComplex.ExactAt.of_iso h
    ((c.app (CochainComplex.mapBifunctor F P (curriedTensor A))).symm ≪≫ e)

section PureTensorFormula

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

private theorem pure_formula (R : Sheaf J CommRingCat.{r})
    (M N : scalarModules J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y)) =
      ScalarHomOrdinary.pure R M N U x y := by
  unfold ScalarHomOrdinary.pure
  rfl

end PureTensorFormula

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem pure_eq_ordinary_private
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    LineUnbounded.pureTensor.{t, a} X R M N U x y =
      ScalarHomOrdinary.pure.{t + 1, t, max a (t + 1)} R M N U x y := by
  unfold LineUnbounded.pureTensor
  have hcomputed := pure_formula R M N U x y
  -- Reuse the inferred proof; the kernel checks the displayed target.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hcomputed
      | Lean.throwError "missing comparison proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

/-- Public export of the private `pure_eq_ordinary_private`
(used by `import all` importers; linter.privateModule). -/
alias pure_eq_ordinary := pure_eq_ordinary_private

private def tensor_site
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) :=
  ScalarHomOrdinary.tensorIsoSite.{t + 1, t, max a (t + 1)} R M N

attribute [local irreducible] tensor_site

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem tensor_site_pure
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (tensor_site.{t, a} M N).hom.val.app U (LineUnbounded.pureTensor.{t, a} X R M N U x y) =
      siteSheafTensorTmul (J := Scheme.ProEt.topology X) (A := R) M N U x y := by
  unfold tensor_site
  have hcomputed := (congrArg ((ScalarHomOrdinary.tensorIsoSite R M N).hom.val.app U)
    (pure_eq_ordinary_private M N U x y)).trans
      (ScalarHomOrdinary.tensorIsoSite_pure.{t + 1, t, max a (t + 1)} R M N U x y)
  -- Reuse the inferred proof; the kernel checks the displayed target.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hcomputed
      | Lean.throwError "missing comparison proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem signed_power_rank
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) [L.IsFiniteLocallyFreeOfRank 1] :
    ∀ m : ℤ, (power.{t, a} L m).IsFiniteLocallyFreeOfRank 1 := by
  obtain ⟨I, V, hV, h⟩ :=
    (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{max a (t + 1), t, t + 1}
      (M := L) (r := 1)).mp
      inferInstance
  intro m
  apply (isInvertible_iff_isFiniteLocallyFreeOfRank_one.{max a (t + 1), t, t + 1} _).mp
  apply isInvertible_of_forall_over_unit.{max a (t + 1), t, t + 1} V hV
  intro i
  let q := (h i).some ≪≫ freeUniqueIso (ULift (Fin 1))
  obtain ⟨E, hE⟩ := signedBasis_on_chart.{t + 1, t, a} L (V i) q
  exact ⟨(basisChart.{t + 1, t, max a (t + 1)} (power.{t, a} L m)
    (op (V i)) (E m) (hE.1 m)).symm⟩

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem tensor_flat_model
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M : Modules.{t, a} X R)
    (hM : PreservesFiniteLimits (LineUnbounded.tensor.{t, a} X R M) ∧
      PreservesFiniteColimits (LineUnbounded.tensor.{t, a} X R M))
    (P : CochainComplex (Modules.{t, a} X R) ℤ) (hP : FlatModel.{t, a} P) :
    FlatModel.{t, a}
      (((LineUnbounded.tensor.{t, a} X R M).mapHomologicalComplex (.up ℤ)).obj P) := by
  change PreservesFiniteLimits (tensorRight M) ∧
    PreservesFiniteColimits (tensorRight M) at hM
  have := hM.1
  have := hM.2
  constructor
  · exact tensor_kflat_generic M P hP.1
  · intro i
    have ht : exactFunctor _ _ (tensorRight (P.X i)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)) (hP.2 i)
    have : PreservesFiniteLimits (tensorRight (P.X i)) := ht.1
    have : PreservesFiniteColimits (tensorRight (P.X i)) := ht.2
    have : PreservesFiniteLimits (tensorRight (P.X i) ⋙ tensorRight M) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (tensorRight (P.X i) ⋙ tensorRight M) :=
      comp_preservesFiniteColimits _ _
    have : PreservesFiniteLimits (tensorRight (P.X i ⊗ M)) :=
      preservesFiniteLimits_of_natIso (tensorRightTensor (P.X i) M).symm
    have : PreservesFiniteColimits (tensorRight (P.X i ⊗ M)) :=
      preservesFiniteColimits_of_natIso (tensorRightTensor (P.X i) M).symm
    change IsFlatOnSite (J := Scheme.ProEt.topology X) (R := R) (P.X i ⊗ M)
    exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R _).symm,
      preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R _).symm⟩

section
attribute [local semireducible] monoidalCategory signedLinePower scalarTensorPower
omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem power_zero
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) : power.{t, a} L 0 = 𝟙_ (Modules.{t, a} X R) := rfl
omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem power_zero_one
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) :
    (eqToHom (power_zero L)).val.app U (1 : R.obj.obj U) = (1 : R.obj.obj U) := rfl
end

attribute [local semireducible] monoidalCategory

/-- All signed powers are lines and their unbounded derived tensors are the exact
termwise tensors with inverse the opposite signed power and actual evaluation.
Source: blueprint proof (3), Stacks 0B8N, 06YN and 06YU
(blueprint: lem-pur-ordinary-line-scalar-line-data).
Proof: on a trivializing slice tensor the chosen basis to get positive powers, and
use the dual basis for negative powers. The normalized signed contraction is actual
evaluation. Apply line_unbounded_derived_tensor to each power. Its degree-zero total
collapse and representative normalization give factors and epsilon_computed on all
complexes. Exact tensor commutes with total sums; reassociation then proves K-flatness
of P tensor the line. Composites of exact tensor functors prove flatness of its terms.
The opposite evaluation gives the other inverse, including exponent zero. -/
theorem exists_lineData
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) [L.IsFiniteLocallyFreeOfRank 1] : Nonempty (LineData L) := by
  classical
  have hr := signed_power_rank L
  have hs (m : ℤ) : ∃ h : FlatModel.{t, a} (LineUnbounded.single.{t, a} X R (power.{t, a} L m)),
      ∃ c : 𝒬[R] ⋙ twist.{t, a, w} L m ≅
        (tensor.{t, a} L m).mapHomologicalComplex (.up ℤ) ⋙ 𝒬[R],
      (PreservesFiniteLimits (tensor.{t, a} L m) ∧ PreservesFiniteColimits (tensor.{t, a} L m)) ∧
      ∀ P : CochainComplex (Modules.{t, a} X R) ℤ,
        LineUnbounded.normalization.{t, a, w} X R (power.{t, a} L m) h.1 h.2 (twist.{t, a, w} L m)
          rfl P (c.app P) := by
    have := hr m
    obtain ⟨_, _, hP, _, hPf, _, hl, hc, _, _, _, _, _, F, G, hF, hG, h⟩ :=
      LineUnbounded.line_unbounded_derived_tensor.{t, a, w} X R (power.{t, a} L m)
    have hh : ∃ cP : 𝒬[R] ⋙ F ≅
        (tensor.{t, a} L m).mapHomologicalComplex (.up ℤ) ⋙ 𝒬[R],
        ∀ P : CochainComplex (Modules.{t, a} X R) ℤ,
          LineUnbounded.normalization.{t, a, w} X R (power.{t, a} L m) hP hPf F hF
            P (cP.app P) := by
      obtain ⟨sP, sD, _, _, cP, _, _, _, hnP, _⟩ := h
      exact ⟨cP, hnP⟩
    clear h hG G
    obtain ⟨cP, hnP⟩ := hh
    subst F
    exact ⟨⟨hP, hPf⟩, cP, ⟨hl, hc⟩, hnP⟩
  choose h c hc hn using hs
  obtain ⟨I, V, hV, hL⟩ :=
    (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{max a (t + 1), t, t + 1}
      (M := L) (r := 1)).mp
      inferInstance
  have hcover : ∃ (I : Type (t + 1)) (V : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (L.over (V i) ≅ unit
        (((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat RingCat)).obj R).over (V i))) :=
    ⟨I, V, hV, fun i ↦ ⟨(hL i).some ≪≫ freeUniqueIso (ULift (Fin 1))⟩⟩
  obtain ⟨μ, hμ, _⟩ := existsUnique_signedLineProduct.{t + 1, t, a} L hcover
  let ev (m : ℤ) : power.{t, a} L m ⊗ power.{t, a} L (-m) ≅ 𝟙_ (Modules.{t, a} X R) :=
    tensor_site.{t, a} _ _ ≪≫ μ m (-m) ≪≫
      eqToIso ((congrArg (power.{t, a} L) (add_neg_cancel m)).trans (power_zero L))
  have hev (m : ℤ) (U : X.ProEtᵒᵖ) (E : ∀ n : ℤ, (power.{t, a} L n).val.obj U)
      (hE : SignedLineBasisPowers.{t + 1, t, a} L U E) :
      (ev m).hom.val.app U
        (LineUnbounded.pureTensor.{t, a} X R
          (power.{t, a} L m) (power.{t, a} L (-m)) U (E m) (E (-m))) =
          (1 : R.obj.obj U) := by
    change (eqToHom ((congrArg (power.{t, a} L) (add_neg_cancel m)).trans
      (power_zero L))).val.app U
      ((μ m (-m)).hom.val.app U ((tensor_site.{t, a} _ _).hom.val.app U _)) = _
    rw [tensor_site_pure, hμ U E hE m (-m)]
    have cast (n : ℤ) (hn : n = 0) :
        (eqToHom ((congrArg (power.{t, a} L) hn).trans
          (power_zero L))).val.app U (E n) =
        (eqToHom (power_zero L)).val.app U (E 0) := by
      subst n
      rfl
    rw [cast _ (add_neg_cancel m), hE.2.1]
    exact power_zero_one L U
  let epsilon (m : ℤ) : twist.{t, a, w} L m ⋙ twist.{t, a, w} L (-m) ≅ 𝟭 _ :=
    LineUnbounded.localizedCancellation 𝒬[R]
      (HomologicalComplex.quasiIso (Modules.{t, a} X R) (.up ℤ))
      _ _ _ _ (c m) (c (-m))
      (Functor.mapHomologicalComplexCompIso
        (LineUnbounded.cancellation.{t, a} X R (power.{t, a} L m)
          (power.{t, a} L (-m)) (ev m)) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso (Modules.{t, a} X R) (.up ℤ))
  refine ⟨{ rank := hr
            exact := hc
            single_flat := h
            factors := c
            factors_normalized := hn
            evaluation := ev
            evaluation_basis := hev
            epsilon := epsilon
            epsilon_computed := ?_
            flat := ?_ }⟩
  · intro m P
    exact LineUnbounded.localizedCancellation_app 𝒬[R]
      (HomologicalComplex.quasiIso (Modules.{t, a} X R) (.up ℤ)) _ _ _ _ (c m) (c (-m)) _ P
  · intro m P hP
    exact tensor_flat_model (power.{t, a} L m) (hc m) P hP

end LineConstruction

end SheafOfModules.OrdinaryLineScalar
