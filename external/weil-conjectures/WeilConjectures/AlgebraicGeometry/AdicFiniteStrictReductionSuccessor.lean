/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.AdicNormalizedScalarComposition
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore

/-! # Normalization of the strict finite reduction tower

Source: Stacks Project, Tags 06YY and 099M
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

open Opposite

attribute [local irreducible] derivedExtension DerivedCategory.Q HasDerivedCategory.standard
  dres change

/-- Termwise evaluation commutes with the two ordinary scalar functors.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
def adicFiniteStrictReductionEvaluationIso
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A)) (n : ℕ) :
    let T := coefficientProEtaleModelTopology.{u, v} X
    let f := quotient T A J n
    ((res f).mapHomologicalComplex (.up ℤ)).obj
        (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≅
      (reductionComplex T A J false P).asFunctor.obj (op n) :=
  eqToIso (by rfl)

/-- The levelwise scalar comparison, constructed from universal K-flat computation
and exact restriction; its direction is from the derived reduction to the strict model.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
def adicFiniteStrictReductionLevel
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (hP : P.IsKFlatTensor) (N : adicFiniteAmbient.{u, v} X A)
    (e : (Q (constant (coefficientProEtaleModelTopology.{u, v} X) A)).obj P ≅ N)
    (n : ℕ) :
    let T := coefficientProEtaleModelTopology.{u, v} X
    adicFiniteUnderlying X J N n ≅
      (Q (constant T A)).obj ((reductionComplex T A J false P).asFunctor.obj (op n)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let f := quotient T A J n
  let : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
  exact (dres f).mapIso ((extend f).mapIso e.symm ≪≫ asIso ((extendComparison f).app P)) ≪≫
    (resFactors f).symm.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    (Q (constant T A)).mapIso (adicFiniteStrictReductionEvaluationIso X A J P n)

attribute [local irreducible] adicFiniteStrictReductionLevel
  adicFiniteStrictReductionEvaluationIso extend adicFiniteTransition

section Proofs

attribute [local instance] HasDerivedCategory.standard
attribute [local semireducible] change extend
attribute [local implicit_reducible] SheafOfModules.restrictScalars change
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  extend extendComparison
  SheafOfModules.unit PresheafOfModules.unit CategoryTheory.sheafCompose

private theorem strict_scalar_step
    {C : Type v} [SmallCategory C] {T : GrothendieckTopology C}
    {R S V : Sheaf T CommRingCat.{v}}
    (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V) (eh : h = f ≫ g)
    (P : Cx R) (hP : P.IsKFlatTensor) (M : D R) (eP : (Q R).obj P ≅ M) :
    let F := (change f).mapHomologicalComplex (.up ℤ)
    let H := (change h).mapHomologicalComplex (.up ℤ)
    let e := adicFiniteExtendComp f g h eh
    letI : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
    letI : IsIso ((extendComparison h).app P) := (derivedExtension h).computation P hP
    (Q R).map ((NatTrans.mapHomologicalComplex (scalarTransition f g h eh.symm)
      (.up ℤ)).app P) ≫ (resFactors h).hom.app (H.obj P) ≫
        (dres h).map (inv ((extendComparison h).app P)) ≫
        (dres h).map ((extend h).map eP.hom) =
      (resFactors f).hom.app (F.obj P) ≫
        (dres f).map (inv ((extendComparison f).app P)) ≫
        (dres f).map ((extend f).map eP.hom) ≫
        (dres f).map ((adicFiniteUnit g).app ((extend f).obj M) ≫
          (dres g).map (e.hom.app M)) ≫
        (adicFiniteDresComp f g).hom.app ((extend h).obj M) ≫
        (eqToIso (congrArg (fun k ↦ (dres k).obj ((extend h).obj M)) eh.symm)).hom := by
  subst h
  dsimp only
  simp only [adicFiniteExtendComp, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id]
  have hpf : IsIso ((extendComparison f).app P) := (derivedExtension f).computation P hP
  have hph : IsIso ((extendComparison (f ≫ g)).app P) :=
    (derivedExtension (f ≫ g)).computation P hP
  rw [reassoc_of% (scalar_transition_comparison f g P hP)]
  rw [← canonical_step_naturality f g eP.hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (adicFiniteDresComp f g).hom.naturality
    ((adicFiniteExtendComp_existsUnique f g).exists.choose.hom.app M)
  change (dres f).map ((dres g).map _) ≫ _ =
    (adicFiniteDresComp f g).hom.app _ ≫ (dres (f ≫ g)).map _ at hn
  rw [hn]
  rfl

private theorem strict_ordinary_step
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A)) (n : ℕ) :
    let T := coefficientProEtaleModelTopology.{u, v} X
    let f := quotient T A J (n + 1)
    let g := adicFiniteConstantMap (adicFiniteFactor J (Nat.le_succ n)) T
    let h := quotient T A J n
    let eh := adicFiniteConstantComp T (adicFiniteQuotient J (n + 1))
      (adicFiniteFactor J (Nat.le_succ n)) (adicFiniteQuotient J n)
      (adicFiniteQuotientComp J (Nat.le_succ n))
    (reductionComplex T A J false P).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      (NatTrans.mapHomologicalComplex (scalarTransition f g h eh.symm) (.up ℤ)).app P := by
  dsimp only
  let T := coefficientProEtaleModelTopology.{u, v} X
  let eh := adicFiniteConstantComp T (adicFiniteQuotient J (n + 1))
    (adicFiniteFactor J (Nat.le_succ n)) (adicFiniteQuotient J n)
    (adicFiniteQuotientComp J (Nat.le_succ n))
  have hs : reductionStep T A J false n =
      scalarTransition (quotient T A J (n + 1))
        (adicFiniteConstantMap (adicFiniteFactor J (Nat.le_succ n)) T)
        (quotient T A J n) eh.symm := by
    apply (reductionStep_existsUnique T A J false n).unique
    · exact (reductionStep_existsUnique T A J false n).exists.choose_spec
    · exact scalarTransition_tmul _ _ _ _
  apply HomologicalComplex.hom_ext
  intro q
  change ((reductionTower T A J false).obj (P.X q)).map
      (homOfLE (Nat.le_succ n)).op = _
  change ((Functor.ofOpSequence (reductionStep T A J false)).map
      (homOfLE (Nat.le_succ n)).op).app (P.X q) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ, hs]
  rfl

end Proofs

attribute [local semireducible] extend

/-- The normalized derived tensor unit and balancing give the actual quotient successor.
Source: Stacks Tags 06YY and 099M
(auxiliary; not a blueprint node).

Proof: compute the scalar unit on the K-flat complex obtained by extending P to the
larger quotient; this is K-flat by flat scalar base change. Use adicFiniteUnitFormula
and adicFiniteExtendCompFormula. The exact restriction composition comparison commutes
with localization by its definition using mapDerivedCategoryCompIso. After composing
with the invertible level comparisons, the resulting equality is the localization
of an equality of ordinary chain maps. In each degree use the faithful underlying
module functor and the scalar tensor adjunction, or check pure tensors: the unit sends
s tensor p to 1 tensor (s tensor p), balancing sends this to the quotient of s tensor p,
and restriction composition acts by identity. The unique normalization of reductionStep
is precisely this formula, so the chain maps agree in each degree. Naturality of all
three scalar comparisons transports the equality along e. The calculation remains
valid for zero ideals, unit ideals, zero complexes, and empty schemes. -/
theorem adicFiniteStrictReduction_successor
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (hP : P.IsKFlatTensor)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q))
    (N : adicFiniteAmbient.{u, v} X A)
    (e : (Q (constant (coefficientProEtaleModelTopology.{u, v} X) A)).obj P ≅ N)
    (n : ℕ) :
    ((reductionComplex (coefficientProEtaleModelTopology.{u, v} X) A J false P).asFunctor ⋙
        Q (constant (coefficientProEtaleModelTopology.{u, v} X) A)).map
          (homOfLE (Nat.le_succ n)).op ≫
        (adicFiniteStrictReductionLevel X A J P hP N e n).inv =
      (adicFiniteStrictReductionLevel X A J P hP N e (n + 1)).inv ≫
        adicFiniteTransition X J N n := by
  have _ := hflat
  let T := coefficientProEtaleModelTopology.{u, v} X
  let f := quotient T A J (n + 1)
  let g := adicFiniteConstantMap (adicFiniteFactor J (Nat.le_succ n)) T
  let h := quotient T A J n
  let eh := adicFiniteConstantComp T (adicFiniteQuotient J (n + 1))
    (adicFiniteFactor J (Nat.le_succ n)) (adicFiniteQuotient J n)
    (adicFiniteQuotientComp J (Nat.le_succ n))
  have hpf : IsIso ((extendComparison f).app P) := by
    simpa only [extendComparison, extend] using (derivedExtension f).computation P hP
  have hph : IsIso ((extendComparison h).app P) := by
    simpa only [extendComparison, extend] using (derivedExtension h).computation P hP
  have ht := strict_scalar_step f g h eh P hP N e
  have ho := congrArg (fun a ↦ (Q (constant T A)).map a) (strict_ordinary_step X A J P n)
  dsimp only at ht ho
  unfold adicFiniteStrictReductionLevel adicFiniteStrictReductionEvaluationIso
  simp only [Iso.trans_inv, CategoryTheory.Functor.mapIso_inv, Iso.app_inv,
    Iso.symm_inv, asIso_inv, CategoryTheory.Functor.map_comp, Category.assoc]
  change (Q (constant T A)).map
      ((reductionComplex T A J false P).asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
      ((Q (constant T A)).map (𝟙 _) ≫
        (resFactors h).hom.app (((change h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (dres h).map (inv ((extendComparison h).app P)) ≫
        (dres h).map ((extend h).map e.hom)) =
    ((Q (constant T A)).map (𝟙 _) ≫
      (resFactors f).hom.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (dres f).map (inv ((extendComparison f).app P)) ≫
      (dres f).map ((extend f).map e.hom) ≫ adicFiniteTransition X J N n)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ho]
  unfold adicFiniteTransition
  dsimp only [adicFiniteReduction, adicFiniteExtension,
    adicFiniteRho, adicFiniteExtensionComp, Iso.app_hom, adicFiniteConstantMap,
    adicFiniteQuotient, quotient, f, g, h, T] at ht ⊢
  simpa only [Category.assoc] using ht

end AlgebraicGeometry.Scheme
