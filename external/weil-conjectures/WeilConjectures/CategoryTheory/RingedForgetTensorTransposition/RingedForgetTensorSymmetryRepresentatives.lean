/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorChainSymmetry

/-! # Representative constraints for exact ringed tensor comparison

Source: Stacks Project, Tags 0FPT, 06YU and 0G7D
(blueprint: lem-sf-ringed-forget-tensor-symmetry-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep the chosen internal-Hom and localization constructions behind their APIs.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

-- Prove the diagram chase with abstract morphisms, before instantiating the models.
private theorem symmetry_localization_square {E : Type*} [Category E]
    {X X' Y Y' Z Z' W W' V V' : E}
    (i : X ⟶ Y) [Epi i] (a' : Z' ⟶ V') [Mono a']
    {i' : X' ⟶ Y'} {b : Y ⟶ Y'} {e : Z ⟶ Z'}
    {c : Y ⟶ Z} {c' : Y' ⟶ Z'} {a : Z ⟶ V}
    {j : W ⟶ V} {j' : W' ⟶ V'} {d : V ⟶ V'}
    {k : X ⟶ W} {k' : X' ⟶ W'} {t : W ⟶ W'} {s : X ⟶ X'}
    (hs : i ≫ b = s ≫ i')
    (hr : i ≫ c ≫ a = k ≫ j) (hr' : i' ≫ c' ≫ a' = k' ≫ j')
    (hk : s ≫ k' = k ≫ t) (hj : j ≫ d = t ≫ j')
    (hn : a ≫ d = e ≫ a') : b ≫ c' = c ≫ e := by
  apply (cancel_epi i).mp
  apply (cancel_mono a').mp
  calc
    _ = s ≫ (i' ≫ c' ≫ a') := by simp only [← Category.assoc, hs]
    _ = s ≫ k' ≫ j' := by rw [hr']
    _ = k ≫ t ≫ j' := by rw [← Category.assoc, hk, Category.assoc]
    _ = k ≫ j ≫ d := by rw [← hj]
    _ = _ := by
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc, hn]

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem zsmul_apply {M N : RingedTensorModules.{c, v, r} J R}
    (f : M ⟶ N) (a : ℤ) (V : Cᵒᵖ) (x : M.val.obj V) :
    (a • f).val.app V x = a • f.val.app V x := by
  have h := (SheafOfModules.forget ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)).map_zsmul
      (f := f) (r := a)
  change (a • f).val = a • f.val at h
  rw [h, PresheafOfModules.zsmul_app]
  rfl

private theorem pure_ext (M N L : RingedTensorModules.{c, v, r} J R)
    {f g : (SheafOfModules.monoidalCategory R).tensorObj M N ⟶ L}
    (h : ∀ V x y,
      f.val.app V (sheafTensorGenerator.{c, v, r} J R M N V x y) =
        g.val.app V (sheafTensorGenerator.{c, v, r} J R M N V x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
  apply (adj.homEquiv (M.val ⊗ N.val) L).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

private theorem swap_summand
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (s : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj (Q, P))
    (hs : ∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      (s.hom.f n).val.app V
        (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y) =
      (p * q).negOnePow •
        coefficientTensorGenerator.{r, c, v} J R Q P q p n h' V y x)
    (p q n : ℤ) (h : p + q = n) (h' : q + p = n) :
    tensorSummand.{c, v, r} J R P Q p q n h ≫ s.hom.f n =
      ((p * q).negOnePow : ℤ) •
        ((SheafOfModules.symmetricCategory R).toBraidedCategory.braiding
          (P.X p) (Q.X q)).hom ≫ tensorSummand.{c, v, r} J R Q P q p n h' := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  apply pure_ext.{c, v, r} J R (P.X p) (Q.X q) _
  intro V x y
  rw [zsmul_apply.{c, v, r}]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (s.hom.f n).val.app V
      (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y) = _
  rw [hs p q n h h' V x y]
  congr 1
  exact congrArg ((tensorSummand.{c, v, r} J R Q P q p n h').val.app V)
    (CochainPullback.moduleTmul_braiding (P.X p) (Q.X q) V x y).symm

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

attribute [local irreducible] coefficientTotalTensor tensorSummand

omit [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
include cB cA

-- The localization square compares two independently presented derived tensor models.
/-- Symmetry on a pair of flat-term K-flat representatives.
There are no unit or associativity assertions, and the arguments are fixed
complexes rather than arbitrary derived objects.

Source: Stacks Project, sites-cohomology.tex, Tags 0FPT and 06YU;
the symmetry part of step 3 of lem-sf-ringed-forget-tensor-coherence
(blueprint: lem-sf-ringed-forget-tensor-symmetry-representatives).

Proof: take the chain swaps supplied by cB.symmetry_model and cA.symmetry_model.
Use the representative equations for (P,Q) and (Q,P), naturality of the
localization factor, and the two symmetry-model equations to cancel the tensor
model isomorphisms. The remaining chain equality is checked after the inverse
comparison, on the target coproduct summands. On bidegree (p,q), the summand
law identifies it with the underived symmetry equation times (-1)^(p*q).
The additive functor preserves this integer scalar. Equality on local pure
tensors identifies the stated chain swaps by the universal property of the
sheafified tensor; equality on coproduct summands then gives equality of chain
maps. Localize and cancel to obtain the displayed square. -/
theorem ringed_forget_tensor_symmetry_representatives
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (hQ : Q.IsKFlatIndependentCoefficients)
    (fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p)) :
    U.mapDerivedCategory.map
        (βB.toBraidedCategory.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (βA.toBraidedCategory.braiding (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
          (U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q))).hom := by
  obtain ⟨sB, hsB, heB⟩ := cB.symmetry_model P Q hP hQ
  have hUP := (hU P hP fP).1
  have hUQ := (hU Q hQ fQ).1
  obtain ⟨sA, hsA, heA⟩ := cA.symmetry_model
    ((U.mapHomologicalComplex (.up ℤ)).obj P)
    ((U.mapHomologicalComplex (.up ℤ)).obj Q) hUP hUQ
  have hc := ringed_forget_tensor_chain_symmetry.{c, v, r, d, vd, s}
    J R J' R' U u chain summand P Q sB sA
    (swap_summand.{c, v, r} J R P Q sB hsB)
    (swap_summand.{d, vd, s} J' R' _ _ sA hsA)
  have hm := hμ P Q hP hQ hUP hUQ fP fQ
  have hm' := hμ Q P hQ hP hUQ hUP fQ fP
  let aP := U.mapDerivedCategoryFactors.hom.app P
  let aQ := U.mapDerivedCategoryFactors.hom.app Q
  have : IsIso (Prod.mkHom aQ aP) := (isIso_prod_iff _ _).2
    ⟨inferInstance, inferInstance⟩
  let := SA.monoidal
  let : SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R')) := βA
  have hn := BraidedCategory.braiding_naturality aP aQ
  have hf := U.mapDerivedCategoryFactors.hom.naturality sB.hom
  change U.mapDerivedCategory.map (DerivedCategory.Q.map sB.hom) ≫
    U.mapDerivedCategoryFactors.hom.app _ =
      U.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map sB.hom) at hf
  apply symmetry_localization_square
    (U.mapDerivedCategory.map (TB.iso J R SB P Q hP hQ).hom)
    (SA.tensor.map
      (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q),
        U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
      (Y := (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj Q),
        DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P)))
      (aQ, aP))
    (s := U.mapDerivedCategory.map (DerivedCategory.Q.map sB.hom))
    (t := DerivedCategory.Q.map sA.hom)
    (k := U.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (chain.hom.app (P, Q)))
    (k' := U.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (chain.hom.app (Q, P)))
    (j := (TA.iso J' R' SA _ _ hUP hUQ).hom)
    (j' := (TA.iso J' R' SA _ _ hUQ hUP).hom)
    (d := (β_ (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P))
      (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj Q))).hom)
    (a := SA.tensor.map
      (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
        U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)))
      (Y := (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P),
        DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj Q)))
      (aP, aQ))
    (i' := U.mapDerivedCategory.map (TB.iso J R SB Q P hQ hP).hom)
  · exact (U.mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg U.mapDerivedCategory.map heB).trans (U.mapDerivedCategory.map_comp _ _))
  · exact hm.trans (Category.assoc _ _ _).symm
  · exact hm'.trans (Category.assoc _ _ _).symm
  · rw [← Category.assoc, hf, Category.assoc, ← DerivedCategory.Q.map_comp, hc,
      DerivedCategory.Q.map_comp, Category.assoc]
  · exact heA
  · simpa only [CoefficientClosedStructure.tensor, tensor_map, Functor.comp_obj] using hn

end CategoryTheory.RingedForgetTensorTransposition
