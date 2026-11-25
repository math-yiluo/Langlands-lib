/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientRealization
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulUnitTensorRealization
import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement

/-! # Finite exact realization of completed Koszul coefficient cones

Source: Stacks Project, Tags 099M, 0921 and 093M.
(blueprint: lem-weil-pbc-completed-koszul-coefficient-cone-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

/-- The existing total tensor structure, with the completed coefficient sheaf explicit.
Source: Stacks 06YN (blueprint: lem-weil-pbc-completed-koszul-coefficient-cone-realization). -/
instance completedKoszulCochainMonoidal
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategory (CochainComplex (CompletedAdicModules T d) ℤ) :=
  CategoryTheory.flatConstantCochainMonoidal
    (J := ProEt.topology T) (O := completedAdicCommRing T d)

attribute [-instance] completedKoszulCochainMonoidal
attribute [local instance] completedKoszulCochainMonoidal

/-- Use precisely the tensor data of completedKoszulCochainMonoidal.
Source: Stacks 06YN (blueprint: lem-weil-pbc-completed-koszul-coefficient-cone-realization). -/
instance completedKoszulCochainMonoidalStruct
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategoryStruct (CochainComplex (CompletedAdicModules T d) ℤ) :=
  (completedKoszulCochainMonoidal T d).toMonoidalCategoryStruct

attribute [-instance] completedKoszulCochainMonoidalStruct
attribute [local instance] completedKoszulCochainMonoidalStruct

attribute [local instance] koszulConstantFunctor_preservesZero

private theorem mapToExtendedSingle_ext
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive] {K : CochainComplex D ℤ} (M : C)
    (g h : K ⟶ (E.mapHomologicalComplex (.up ℤ)).obj
      (((ChainComplex.single₀ C).obj M).extend ComplexShape.embeddingDownNat))
    (hzero : g.f 0 = h.f 0) : g = h := by
  let e := (E.mapHomologicalComplex (.up ℤ)).mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 rfl) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app M
  apply (cancel_mono e.hom).1
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, hzero]

set_option linter.unusedVariables false in
/-- Finite exact realization identifies the algebraic augmentation cones with the
completed coefficient cones, including their actual strict transition maps. There
is no arbitrary complex P, K-flatness, eventual vanishing, or inverse limit here.

Source: Stacks Project, proetale.tex, proof of lemma-naive-completion (099M),
more-algebra.tex, lemma-sequence-Koszul-complexes (0921), and Modules on Sites (093M).
(blueprint: lem-weil-pbc-completed-koszul-coefficient-cone-realization).

Proof: work over the universe lift of A. Use constant module sheafification,
followed by extension along completedAdicScalar, as E. The constant functor is
exact; the completed ring is flat over the constant ring by completed constant
sheaf reduction. Hence E is additive and preserves finite limits and colimits.
The lifted quotient of A by I^(n+1) is the quotient of the lifted ring, through
the quotient map induced by ULift.ringEquiv. Finite coefficient identification
identifies its constant sheaf with completedAdicFiniteModule. The identification
sends a quotient representative x to its recorded constant section and therefore
commutes with every quotient transition. The exterior complexes are exactly the
ones in completedAdicKoszul: their degree-zero maps use exteriorPower.zeroEquiv,
and their successors are exterior powers of the diagonal a_i. Tensoring with
the cochain unit and its left unitor identifies these with the source of gamma.
In degree zero the Koszul unit is invertible: exterior degree zero is the rank-one
coefficient module, and extension of scalars preserves the scalar-unit isomorphism.
The unit equation therefore determines gamma on exterior degree zero. The second
equation determines it to be zero on all other exterior degrees. The total
summand inclusions jointly detect morphisms, so gamma equals the realized
algebraic augmentation under the two identifications. The given formulas for
sA and qA determine their components; for qA cancel the surjective quotient map.
They therefore identify all strict squares, for every n <= m. The additive
mapping-cone comparison gives e, and its naturality at those strict squares is
the displayed equation. For r=0 only exterior degree zero remains; the empty
scheme, zero ring and unit ideal use the same quotient and unitor formulas. -/
theorem completedKoszulCoefficientConeRealization
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (εA : ∀ n : ℕ,
      ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1)) ⟶
        (ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (n + 1))))
    (sA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (m + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (n + 1)))))
    (hεA : ∀ n, (εA n).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
          (n + 1)).mkQ.comp
        (exteriorPower.zeroEquiv (ULift.{t + 1} A) (Fin r →₀ ULift.{t + 1} A)).toLinearMap))
    (hsA : ∀ n m h k, (sA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k (Finsupp.linearCombination (ULift.{t + 1} A)
        (fun i ↦ Finsupp.single i ((ULift.up (a i) : ULift.{t + 1} A) ^ (m - n))))))
    (hqA : ∀ n m h,
      ModuleCat.ofHom ((Ideal.span (Set.range
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^ (m + 1)).mkQ ≫
        (qA n m h).f 0 = ModuleCat.ofHom ((Ideal.span (Set.range
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^ (n + 1)).mkQ)
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (sA n m h) ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat =
        HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
    (γ : (completedKoszulTensorTower T d r a).obj
        (𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)) ⟶
      ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
        (𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)))
    (hu : ∀ n : ℕ,
      completedAdicKoszulTensorUnit T d r a _ n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map γ).app (op n) =
        completedQuotientTensorUnit T d _ n)
    (hz : ∀ (n : ℕ) (p q : ℤ) (_hq : q ≠ 0),
      completedKoszulTensorSummand T d r a _ n p q ≫
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map γ).app (op n)).f
            (p + q) = 0) :
    ∃ (E : ModuleCat.{t + 1} (ULift.{t + 1} A) ⥤ CompletedAdicModules T d)
      (_hadd : E.Additive) (_hlim : PreservesFiniteLimits E)
      (_hcolim : PreservesFiniteColimits E)
      (e : ∀ n : ℕ, (E.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.homotopyCofiber
          (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)) ≅
            (CochainComplex.mappingCone γ).asFunctor.obj (op n)),
      ∀ (n m : ℕ) (h : n ≤ m),
        (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (sA n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
          (e m).hom ≫ (CochainComplex.mappingCone γ).asFunctor.map (homOfLE h).op := by
  let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let H := E.mapHomologicalComplex (.up ℤ)
  let B (n : ℕ) := ModuleCat.of (ULift.{t + 1} A)
    ((ULift.{t + 1} A) ⧸
      (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^ (n + 1))
  let K (n : ℕ) := (ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
    (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))).extend
      ComplexShape.embeddingDownNat
  let L (n : ℕ) := ((ChainComplex.single₀ (ModuleCat (ULift.{t + 1} A))).obj
    (B n)).extend ComplexShape.embeddingDownNat
  let f (n : ℕ) : K n ⟶ L n :=
    HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat
  obtain ⟨hadd, hlim, hcolim, c, eQ, hQ⟩ :=
    completedKoszulFiniteQuotientRealization T d r a ha
  let : E.Additive := hadd
  let : PreservesFiniteLimits E := hlim
  let : PreservesFiniteColimits E := hcolim
  obtain ⟨eK, ht, hK⟩ := completedKoszulUnitTensorRealization T d r a sA hsA c
  let ε := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map γ
  let vK (n : ℕ) : ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A) ⟶ (K n).X 0 :=
    ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
      (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv
  have hvK (n : ℕ) : IsIso (vK n) := by
    change IsIso ((exteriorPower.zeroEquiv (ULift.{t + 1} A)
      (Fin r →₀ ULift.{t + 1} A)).toModuleIso.inv ≫ _)
    infer_instance
  have haug (n : ℕ) : H.map (f n) ≫ (eQ n).hom = (eK n).hom ≫ ε.app (op n) := by
    have hf0 : vK n ≫ (f n).f 0 =
        ModuleCat.ofHom ((Ideal.span (Set.range
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^ (n + 1)).mkQ ≫
        (((ChainComplex.single₀ (ModuleCat (ULift.{t + 1} A))).obj (B n)).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv := by
      dsimp only [vK, f]
      rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl, hεA n]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc]
      apply (cancel_mono
        (((ChainComplex.single₀ (ModuleCat (ULift.{t + 1} A))).obj (B n)).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv).2
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp
    have hzero : (H.map (f n) ≫ (eQ n).hom).f 0 =
        ((eK n).hom ≫ ε.app (op n)).f 0 := by
      have := hvK n
      apply (cancel_epi (c.hom ≫ E.map (vK n))).1
      simp only [HomologicalComplex.comp_f, Category.assoc]
      change c.hom ≫ E.map (vK n) ≫ E.map ((f n).f 0) ≫ (eQ n).hom.f 0 =
        c.hom ≫ E.map (vK n) ≫ (eK n).hom.f 0 ≫ (ε.app (op n)).f 0
      rw [← E.map_comp_assoc, hf0, E.map_comp]
      simp only [Category.assoc]
      erw [hQ n]
      calc
        _ = (completedAdicKoszulTensorUnit T d r a U n).f 0 ≫
            (ε.app (op n)).f 0 := (congrArg (fun z ↦ z.f 0) (hu n)).symm
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ z ≫ (ε.app (op n)).f 0) (hK n).symm
    apply (cancel_mono (eQ n).inv).1
    apply mapToExtendedSingle_ext E (B n)
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun z ↦ z ≫ (eQ n).inv.f 0) hzero
  have hfepi (n : ℕ) : Epi (H.map (f n)) := by
    have hepi (k : ℕ) : Epi ((εA n).f k) := by
      cases k with
      | zero =>
        rw [hεA n]
        apply (ModuleCat.epi_iff_surjective _).2
        exact (Submodule.mkQ_surjective _).comp
          (exteriorPower.zeroEquiv (ULift.{t + 1} A)
            (Fin r →₀ ULift.{t + 1} A)).surjective
      | succ k =>
        exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 (B n) (k + 1)
          (by omega)).epi _
    have : Epi (f n) := by
      apply HomologicalComplex.epi_of_epi_f
      intro i
      by_cases hi : ∃ k, ComplexShape.embeddingDownNat.f k = i
      · obtain ⟨k, hk⟩ := hi
        dsimp only [f]
        rw [HomologicalComplex.extendMap_f _ _ hk]
        infer_instance
      · exact (HomologicalComplex.isZero_extend_X _ _ i (by simpa using hi)).epi _
    infer_instance
  obtain ⟨e, he⟩ := additiveConeFamilyComparison E K L f
    (fun n m h ↦ HomologicalComplex.extendMap (sA n m h) ComplexShape.embeddingDownNat)
    (fun n m h ↦ HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
    hc ε eK eQ haug ht hfepi
  exact ⟨E, hadd, hlim, hcolim, e, he⟩

end AlgebraicGeometry.Scheme
