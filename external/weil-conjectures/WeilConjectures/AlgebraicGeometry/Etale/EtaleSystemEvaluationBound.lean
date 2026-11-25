/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownEvaluationMate
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownSupportTransition

/-! # Evaluation mates and a uniform lower bound for the system right adjoint

Source: Zheng, Lemma 5.22, (5.16.2), and Construction 5.15, printed pp. 35--36
(blueprint: lem-pur-etale-system-evaluation-bound).

All categories are ordinary unbounded derived categories of strict systems. Level `n`
denotes the positive exponent `n+1`. The Brown package supplies only the already recorded
canonical comparisons: the right adjoints below are arbitrary fixed choices. The bound
is conditional and does not restrict the inputs of the evaluation or transition clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry
attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

section Maps
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O t c}
  (B : StrictEtaleBrownConstruction O t c S)
  {G : DerivedCategory (strictEtaleCoefficientSystem Y O t) ⥤
    DerivedCategory (strictEtaleCoefficientSystem X O t)}
  (adj : S.functor ⊣ G)
  {g : ∀ n : ℕ, DerivedCategory (strictEtaleLevel Y O t n) ⥤
    DerivedCategory (strictEtaleLevel X O t n)}
  (adjN : ∀ n : ℕ, S.levelFunctor n ⊣ g n)

/-- The six Hom bijections in the node, in their specified order. The middle bijection
precomposes with the inverse of the canonical left-extension comparison.
Source: Zheng, (5.16.2) and Lemma 5.22
(blueprint: lem-pur-etale-system-evaluation-bound). -/
def strictEtaleEvaluationHomChain (n : ℕ)
    (P : DerivedCategory (strictEtaleLevel X O t n))
    (M : DerivedCategory (strictEtaleCoefficientSystem Y O t)) :
    (P ⟶ (S.PX.evaluation n).obj (G.obj M)) ≃
      (P ⟶ (g n).obj ((S.PY.evaluation n).obj M)) :=
  ((S.PX.derivedAdj n).homEquiv P (G.obj M)).symm |>.trans
    ((adj.homEquiv ((S.PX.derivedExtension n).obj P) M).symm) |>.trans
    (Iso.homCongr ((B.leftExtension n).app P) (Iso.refl M)) |>.trans
    ((S.PY.derivedAdj n).homEquiv ((S.levelFunctor n).obj P) M) |>.trans
    ((adjN n).homEquiv P ((S.PY.evaluation n).obj M))

/-- The coefficient projection's right mate. `B.projection.hom` is `q⁻¹`, as fixed by
`projection_recorded_q`; the mate uses the chosen finite-level units and counits.
Source: Zheng, Lemma 5.22 and Construction 5.15
(blueprint: lem-pur-etale-system-evaluation-bound). -/
def strictEtaleBrownQuotientMate {m n : ℕ} (h : n ≤ m) :
    g m ⋙ (S.PX.scalar h).derived ⟶ (S.PY.scalar h).derived ⋙ g n :=
  (mateEquiv (adjN m) (adjN n) (.mk _ _ _ _ (B.projection h).hom))

/-- The prescribed finite-level transition word `g_n(t_M) b`, using the scalar-adjoint
of the actual derived strict transition of `M`, including nonflat quotient maps.
Source: Zheng, Lemma 5.22 and Construction 4.1
(blueprint: lem-pur-etale-system-evaluation-bound). -/
def strictEtaleBrownRightSystemTransition {m n : ℕ} (h : n ≤ m)
    (M : DerivedCategory (strictEtaleCoefficientSystem Y O t)) :
    (S.PX.scalar h).derived.obj ((g m).obj ((S.PY.evaluation m).obj M)) ⟶
      (g n).obj ((S.PY.evaluation n).obj M) :=
  (strictEtaleBrownQuotientMate B adjN h).app ((S.PY.evaluation m).obj M) ≫
    (g n).map (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm ((S.PY.transition h).app M))

private def evaluationIso (n : ℕ) :
    G ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ g n :=
  conjugateIsoEquiv ((S.PX.derivedAdj n).comp adj)
    ((adjN n).comp (S.PY.derivedAdj n)) (B.leftExtension n).symm

private theorem evaluationIso_hom_chain (n : ℕ)
    (P : DerivedCategory (strictEtaleLevel X O t n))
    (M : DerivedCategory (strictEtaleCoefficientSystem Y O t))
    (h : P ⟶ (S.PX.evaluation n).obj (G.obj M)) :
    h ≫ (evaluationIso B adj adjN n).hom.app M =
      strictEtaleEvaluationHomChain B adj adjN n P M h := by
  let a := (S.PX.derivedAdj n).comp adj
  let b := (adjN n).comp (S.PY.derivedAdj n)
  let e := B.leftExtension n
  let f := (a.homEquiv P M).symm h
  have hc : a.homEquiv P M f ≫ (conjugateIsoEquiv a b e.symm).hom.app M =
      b.homEquiv P M (e.inv.app P ≫ f) := by
    rw [a.homEquiv_unit, b.homEquiv_unit]
    rw [Category.assoc, (conjugateIsoEquiv a b e.symm).hom.naturality f,
      ← Category.assoc]
    rw [conjugateIsoEquiv_apply_hom, unit_conjugateEquiv]
    rw [Category.assoc, ← Functor.map_comp]
    rfl
  rw [show a.homEquiv P M f = h from (a.homEquiv P M).apply_symm_apply h] at hc
  simpa [f, a, b, e, evaluationIso, Adjunction.comp_homEquiv,
    strictEtaleEvaluationHomChain] using hc

private theorem evaluationIso_unique
    (theta' : ∀ n : ℕ, G ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ g n)
    (hh : ∀ (n : ℕ) P M (h : P ⟶ (S.PX.evaluation n).obj (G.obj M)),
      h ≫ (theta' n).hom.app M = strictEtaleEvaluationHomChain B adj adjN n P M h) :
    theta' = evaluationIso B adj adjN := by
  funext n
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have h := (hh n _ M (𝟙 _)).trans
    (evaluationIso_hom_chain B adj adjN n _ M (𝟙 _)).symm
  simpa only [Category.id_comp] using h

private theorem coefficient_counit {m n : ℕ} (h : n ≤ m)
    (M : DerivedCategory (strictEtaleLevel Y O t m)) :
    (S.levelFunctor n).map ((strictEtaleBrownQuotientMate B adjN h).app M) ≫
      (adjN n).counit.app ((S.PY.scalar h).derived.obj M) =
    (B.projection h).hom.app ((g m).obj M) ≫
      (S.PY.scalar h).derived.map ((adjN m).counit.app M) := by
  exact mateEquiv_counit (adjN m) (adjN n) (.mk _ _ _ _ (B.projection h).hom) M

private theorem coefficient_transpose {m n : ℕ} (h : n ≤ m)
    (M : DerivedCategory (strictEtaleLevel Y O t m)) :
    (adjN n).homEquiv _ _
      ((B.projection h).hom.app ((g m).obj M) ≫
        (S.PY.scalar h).derived.map ((adjN m).counit.app M)) =
      (strictEtaleBrownQuotientMate B adjN h).app M := by
  apply ((adjN n).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact (coefficient_counit B adjN h M).symm

include B adjN in
private theorem right_lower_bound
    (theta : ∀ n : ℕ, G ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ g n)
    (N : ℕ)
    (hN : ∀ (n : ℕ) (b : ℤ) (P : DerivedCategory (strictEtaleLevel X O t n)),
      P.IsLE b → ((S.levelFunctor n).obj P).IsLE (b + (N : ℤ)))
    (a : ℤ) (M : DerivedCategory (strictEtaleCoefficientSystem Y O t))
    (hM : M.IsGE a) : (G.obj M).IsGE (a - (N : ℤ)) := by
  apply ((B.componentsX.bounds (G.obj M) (a - (N : ℤ))).1).2
  intro n
  have hMn := ((B.componentsY.bounds M a).1).1 hM n
  have hg : ((g n).obj ((S.PY.evaluation n).obj M)).IsGE (a - (N : ℤ)) := by
    apply (DerivedCategory.TStructure.t.isGE_iff_orthogonal
      (a - (N : ℤ) - 1) (a - (N : ℤ)) (by omega) _).2
    intro P h hP
    have hFP := hN n (a - (N : ℤ) - 1) P hP
    have hz (k : (S.levelFunctor n).obj P ⟶ (S.PY.evaluation n).obj M) : k = 0 :=
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE k
        (a - (N : ℤ) - 1 + (N : ℤ)) a (by omega) hFP hMn
    exact ((adjN n).homEquiv _ _).symm.injective ((hz _).trans (hz _).symm)
  have := hg
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (show (g n).obj ((S.PY.evaluation n).obj M) ≅
      (S.PX.evaluation n).obj (G.obj M) from ((theta n).app M).symm) _

private theorem evaluationIso_mate (n : ℕ) :
    (evaluationIso B adj adjN n).hom =
      (mateEquiv adj (adjN n) (.mk _ _ _ _ (S.evaluation n).inv)) := by
  change conjugateEquiv ((S.PX.derivedAdj n).comp adj)
    ((adjN n).comp (S.PY.derivedAdj n)) (B.leftExtension n).inv = _
  rw [← iterated_mateEquiv_conjugateEquiv (S.PX.derivedAdj n)
    (S.PY.derivedAdj n) (adjN n) adj]
  apply congrArg (fun z ↦ (mateEquiv adj (adjN n) z))
  refine NatTrans.ext (funext fun K ↦ ?_)
  exact congrArg (fun z ↦ z.app K) (etaleBrownEvaluationMate B n).2

private theorem evaluationIso_counit (n : ℕ) M :
    (S.levelFunctor n).map ((evaluationIso B adj adjN n).hom.app M) ≫
      (adjN n).counit.app ((S.PY.evaluation n).obj M) =
    (S.evaluation n).inv.app (G.obj M) ≫ (S.PY.evaluation n).map (adj.counit.app M) := by
  rw [evaluationIso_mate]
  exact mateEquiv_counit adj (adjN n) (.mk _ _ _ _ (S.evaluation n).inv) M

private theorem evaluationIso_unit (n : ℕ) K :
    (S.PX.evaluation n).map (adj.unit.app K) ≫
      (evaluationIso B adj adjN n).hom.app (S.functor.obj K) ≫
      (g n).map ((S.evaluation n).hom.app K) =
    (adjN n).unit.app ((S.PX.evaluation n).obj K) := by
  rw [← Category.assoc, evaluationIso_mate,
    unit_mateEquiv adj (adjN n) (.mk _ _ _ _ (S.evaluation n).inv) K]
  change ((adjN n).unit.app ((S.PX.evaluation n).obj K) ≫
    (g n).map ((S.evaluation n).inv.app K)) ≫ (g n).map ((S.evaluation n).hom.app K) = _
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(g n).map_id, Category.comp_id]

private theorem coefficient_identity (n : ℕ) M :
    (strictEtaleBrownQuotientMate B adjN (Nat.le_refl n)).app M ≫
      (g n).map ((S.PY.derivedUnit n).hom.app M) =
    (S.PX.derivedUnit n).hom.app ((g n).obj M) := by
  apply ((adjN n).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
    coefficient_counit]
  rw [Category.assoc]
  have hn := (S.PY.derivedUnit n).hom.naturality ((adjN n).counit.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [hn]
  change _ = (S.levelFunctor n).map ((S.PX.derivedUnit n).hom.app ((g n).obj M)) ≫
    (adjN n).counit.app M
  rw [← Category.assoc]
  erw [(etaleBrownCoefficientCoherence B).1]

private theorem coefficient_composition {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) M :
    (S.PX.derivedAssoc h₁ h₂).hom.app ((g r).obj M) ≫
      (strictEtaleBrownQuotientMate B adjN (h₂.trans h₁)).app M =
    (S.PX.scalar h₂).derived.map ((strictEtaleBrownQuotientMate B adjN h₁).app M) ≫
      (strictEtaleBrownQuotientMate B adjN h₂).app ((S.PY.scalar h₁).derived.obj M) ≫
      (g n).map ((S.PY.derivedAssoc h₁ h₂).hom.app M) := by
  apply ((adjN n).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [coefficient_counit]
  rw [(adjN n).counit_naturality]
  rw [← Category.assoc ((S.levelFunctor n).map
    ((strictEtaleBrownQuotientMate B adjN h₂).app _)), coefficient_counit]
  simp only [Category.assoc]
  have hn := (B.projection h₂).hom.naturality
    ((strictEtaleBrownQuotientMate B adjN h₁).app M)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rw [← (S.PY.scalar h₂).derived.map_comp_assoc, coefficient_counit]
  simp only [Functor.map_comp, Category.assoc]
  have ha := (S.PY.derivedAssoc h₁ h₂).hom.naturality ((adjN r).counit.app M)
  dsimp only [Functor.comp_map] at ha
  erw [ha]
  simp only [← Category.assoc]
  rw [(etaleBrownCoefficientCoherence B).2 h₁ h₂]
  simp only [Functor.comp_obj, Category.assoc]

private theorem evaluationIso_transition {m n : ℕ} (h : n ≤ m) M :
    ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm ((S.PX.transition h).app (G.obj M)) ≫
      (evaluationIso B adj adjN n).hom.app M =
    (S.PX.scalar h).derived.map ((evaluationIso B adj adjN m).hom.app M) ≫
      strictEtaleBrownRightSystemTransition B adjN h M := by
  let tx := ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
    ((S.PX.transition h).app (G.obj M))
  let ty := ((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
    ((S.PY.transition h).app M)
  change tx ≫ _ = _ ≫ _
  apply ((adjN n).homEquiv _ _).symm.injective
  change (S.levelFunctor n).map (tx ≫ _) ≫ _ =
    (S.levelFunctor n).map (_ ≫ _) ≫ _
  rw [Functor.map_comp, Category.assoc, evaluationIso_counit,
    ← Category.assoc, etaleBrownSupportTransition B h]
  simp only [strictEtaleBrownRightSystemTransition, Functor.map_comp, Category.assoc]
  rw [(adjN n).counit_naturality]
  rw [← Category.assoc ((S.levelFunctor n).map
    ((strictEtaleBrownQuotientMate B adjN h).app _)), coefficient_counit]
  simp only [Category.assoc]
  have hn := (B.projection h).hom.naturality ((evaluationIso B adj adjN m).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rw [← (S.PY.scalar h).derived.map_comp_assoc, evaluationIso_counit]
  simp only [Functor.map_comp, Category.assoc]
  congr 2
  have hn := (S.PY.transition h).naturality (adj.counit.app M)
  dsimp only [Functor.comp_map] at hn
  have hh := congrArg (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm) hn
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm] at hh
  symm
  exact hh

private theorem actual_transition_identity
    {W : Scheme.{u}} (P : StrictEtaleEvaluation W O t) (n : ℕ)
    (M : DerivedCategory (strictEtaleCoefficientSystem W O t)) :
    ((P.scalar (Nat.le_refl n)).derivedAdj.homEquiv _ _).symm
      ((P.transition (Nat.le_refl n)).app M) =
    (P.derivedUnit n).hom.app ((P.evaluation n).obj M) := by
  have hh := P.mate (Nat.le_refl n) ((P.evaluation n).obj M) M
    ((P.derivedAdj n).counit.app M)
  rw [P.sigma_id, Adjunction.homEquiv_naturality_left] at hh
  rw [← (P.derivedAdj n).homEquiv_symm_id] at hh
  simpa [Functor.comp_obj] using hh.symm

private theorem actual_transition_composition
    {W : Scheme.{u}} (P : StrictEtaleEvaluation W O t)
    {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m)
    (M : DerivedCategory (strictEtaleCoefficientSystem W O t)) :
    (P.scalar h₂).derived.map
        (((P.scalar h₁).derivedAdj.homEquiv _ _).symm ((P.transition h₁).app M)) ≫
      (((P.scalar h₂).derivedAdj.homEquiv _ _).symm ((P.transition h₂).app M)) =
    (P.derivedAssoc h₁ h₂).hom.app ((P.evaluation r).obj M) ≫
      (((P.scalar (h₂.trans h₁)).derivedAdj.homEquiv _ _).symm
        ((P.transition (h₂.trans h₁)).app M)) := by
  let F := (P.derivedAdj r).counit.app M
  have hh := P.mate h₂ ((P.scalar h₁).derived.obj ((P.evaluation r).obj M)) M
    ((P.sigma h₁).app ((P.evaluation r).obj M) ≫ F)
  have hh' := P.mate h₁ ((P.evaluation r).obj M) M F
  rw [hh'] at hh
  have hd := P.mate (h₂.trans h₁) ((P.evaluation r).obj M) M F
  have hs := P.sigma_comp h₁ h₂ ((P.evaluation r).obj M)
  have he := congrArg (fun k ↦ (P.derivedAdj n).homEquiv _ M (k ≫ F)) hs
  rw [Category.assoc, hh] at he
  rw [Category.assoc, Adjunction.homEquiv_naturality_left, hd] at he
  dsimp only [F] at he
  rw [← (P.derivedAdj r).homEquiv_symm_id] at he
  simpa [Functor.comp_obj] using he

private theorem right_transition_identity (n : ℕ) M :
    strictEtaleBrownRightSystemTransition B adjN (Nat.le_refl n) M =
      (S.PX.derivedUnit n).hom.app ((g n).obj ((S.PY.evaluation n).obj M)) := by
  unfold strictEtaleBrownRightSystemTransition
  rw [actual_transition_identity, coefficient_identity]

private theorem right_transition_composition {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) M :
    (S.PX.scalar h₂).derived.map (strictEtaleBrownRightSystemTransition B adjN h₁ M) ≫
      strictEtaleBrownRightSystemTransition B adjN h₂ M =
    (S.PX.derivedAssoc h₁ h₂).hom.app ((g r).obj ((S.PY.evaluation r).obj M)) ≫
      strictEtaleBrownRightSystemTransition B adjN (h₂.trans h₁) M := by
  let ty := ((S.PY.scalar h₁).derivedAdj.homEquiv _ _).symm ((S.PY.transition h₁).app M)
  have hn := (strictEtaleBrownQuotientMate B adjN h₂).naturality ty
  dsimp only [Functor.comp_map] at hn
  simp only [strictEtaleBrownRightSystemTransition, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((S.PX.scalar h₂).derived.map ((g m).map _)), hn]
  simp only [Category.assoc]
  rw [← (g n).map_comp, actual_transition_composition]
  simp only [Functor.map_comp]
  erw [reassoc_of% (coefficient_composition B adjN h₁ h₂
    ((S.PY.evaluation r).obj M)).symm]

/-- Conclusion data, rather than assumptions, for evaluation, its unique Hom-chain
normalization, the evaluated unit/counit, actual transitions, and the unchanged bound.
Source: Zheng, Lemma 5.22 and Construction 5.15
(blueprint: lem-pur-etale-system-evaluation-bound). -/
structure StrictEtaleEvaluationBound where
  theta : ∀ n : ℕ, G ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ g n
  hom_chain : ∀ (n : ℕ) P M (h : P ⟶ (S.PX.evaluation n).obj (G.obj M)),
    h ≫ (theta n).hom.app M = strictEtaleEvaluationHomChain B adj adjN n P M h
  unique : ∀ (theta' : ∀ n : ℕ, G ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ g n),
    (∀ (n : ℕ) P M (h : P ⟶ (S.PX.evaluation n).obj (G.obj M)),
      h ≫ (theta' n).hom.app M = strictEtaleEvaluationHomChain B adj adjN n P M h) →
    theta' = theta
  counit : ∀ (n : ℕ) M,
    (S.levelFunctor n).map ((theta n).hom.app M) ≫
      (adjN n).counit.app ((S.PY.evaluation n).obj M) =
    (S.evaluation n).inv.app (G.obj M) ≫ (S.PY.evaluation n).map (adj.counit.app M)
  unit : ∀ (n : ℕ) K,
    (S.PX.evaluation n).map (adj.unit.app K) ≫ (theta n).hom.app (S.functor.obj K) ≫
      (g n).map ((S.evaluation n).hom.app K) =
    (adjN n).unit.app ((S.PX.evaluation n).obj K)
  coefficient_transpose : ∀ {m n : ℕ} (h : n ≤ m) M,
    (adjN n).homEquiv _ _
      ((B.projection h).hom.app ((g m).obj M) ≫
        (S.PY.scalar h).derived.map ((adjN m).counit.app M)) =
    (strictEtaleBrownQuotientMate B adjN h).app M
  transition : ∀ {m n : ℕ} (h : n ≤ m) M,
    ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm ((S.PX.transition h).app (G.obj M)) ≫
      (theta n).hom.app M =
    (S.PX.scalar h).derived.map ((theta m).hom.app M) ≫
      strictEtaleBrownRightSystemTransition B adjN h M
  coefficient_identity : ∀ (n : ℕ) M,
    (strictEtaleBrownQuotientMate B adjN (Nat.le_refl n)).app M ≫
      (g n).map ((S.PY.derivedUnit n).hom.app M) =
    (S.PX.derivedUnit n).hom.app ((g n).obj M)
  coefficient_composition : ∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) M,
    (S.PX.derivedAssoc h₁ h₂).hom.app ((g r).obj M) ≫
      (strictEtaleBrownQuotientMate B adjN (h₂.trans h₁)).app M =
    (S.PX.scalar h₂).derived.map ((strictEtaleBrownQuotientMate B adjN h₁).app M) ≫
      (strictEtaleBrownQuotientMate B adjN h₂).app ((S.PY.scalar h₁).derived.obj M) ≫
      (g n).map ((S.PY.derivedAssoc h₁ h₂).hom.app M)
  transition_identity : ∀ (n : ℕ) M,
    strictEtaleBrownRightSystemTransition B adjN (Nat.le_refl n) M =
      (S.PX.derivedUnit n).hom.app ((g n).obj ((S.PY.evaluation n).obj M))
  transition_composition : ∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) M,
    (S.PX.scalar h₂).derived.map (strictEtaleBrownRightSystemTransition B adjN h₁ M) ≫
      strictEtaleBrownRightSystemTransition B adjN h₂ M =
    (S.PX.derivedAssoc h₁ h₂).hom.app ((g r).obj ((S.PY.evaluation r).obj M)) ≫
      strictEtaleBrownRightSystemTransition B adjN (h₂.trans h₁) M
  lower_bound : ∀ N : ℕ,
    (∀ (n : ℕ) (b : ℤ) (P : DerivedCategory (strictEtaleLevel X O t n)),
      P.IsLE b → ((S.levelFunctor n).obj P).IsLE (b + (N : ℤ))) →
    ∀ (a : ℤ) (M : DerivedCategory (strictEtaleCoefficientSystem Y O t)),
      M.IsGE a → (G.obj M).IsGE (a - (N : ℤ))
end Maps

end AlgebraicGeometry
