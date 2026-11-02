import Langlands.CommutativeAlgebra.FiniteFreeReversedDualExactness
import Langlands.Cohomology.PerfectModuleComplexBaseChange
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Scalar extension of reversed dual complexes -/

universe u

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology.ModuleComplex
open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R S : Type u} [CommRing R] [CommRing S]

set_option backward.isDefEq.respectTransparency.types false in
/-- Finite free duals commute with ordinary scalar extension, as actual complexes. -/
def reversedDualBaseChangeIso (φ : R →+* S) (g : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ∀ i, Module.Finite R (C.X i) ∧ Module.Free R (C.X i)) :
    (baseChange φ).obj (reversedDual g C) ≅
      reversedDual g ((baseChange φ).obj C) := by
  letI := φ.toAlgebra
  have (i : ℤ) : Module.Finite R (C.X i) := (h i).1
  have (i : ℤ) : Module.Free R (C.X i) := (h i).2
  let e (i : ℤ) : ((baseChange φ).obj (reversedDual g C)).X i ≅
      (reversedDual g ((baseChange φ).obj C)).X i :=
    (TensorProduct.isBaseChange R (C.X (g - i)) S).toDualBaseChange.toModuleIso
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  apply ModuleCat.ExtendScalars.hom_ext
  intro f
  change Module.Dual R (C.X (g - i)) at f
  change @Eq (Module.Dual S (S ⊗[R] C.X (g - j))) _ _
  apply (TensorProduct.isBaseChange R (C.X (g - j)) S).algHom_ext
  intro x
  change ((TensorProduct.isBaseChange R (C.X (g - i)) S).toDualBaseChange
      (1 ⊗ₜ[R] f)) (1 ⊗ₜ[R] (C.d (g - j) (g - i)).hom x) =
    ((TensorProduct.isBaseChange R (C.X (g - j)) S).toDualBaseChange
      (1 ⊗ₜ[R] (C.d (g - j) (g - i)).hom.dualMap f)) (1 ⊗ₜ[R] x)
  exact ((TensorProduct.isBaseChange R (C.X (g - i)) S).toDualBaseChange_tmul
    (1 : S) f ((C.d (g - j) (g - i)).hom x)).trans
    ((TensorProduct.isBaseChange R (C.X (g - j)) S).toDualBaseChange_tmul
      (1 : S) ((C.d (g - j) (g - i)).hom.dualMap f) x).symm

/-- A scalar extension that makes a bounded finite free complex acyclic also
makes its reversed dual acyclic. -/
theorem isZero_homology_baseChange_reversedDual_of_acyclic (φ : R →+* S) (g : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : IsFiniteFree C)
    (hacyclic : ((baseChange φ).obj C).Acyclic) (i : ℤ) :
    IsZero (((baseChange φ).obj (reversedDual g C)).homology i) := by
  have hP := isStrictlyPerfect_baseChange φ (isStrictlyPerfect_of_isFiniteFree hC)
  obtain ⟨a, b, ha, hb⟩ := hP.1
  have hz := isZero_homology_reversedDual_of_acyclic g b ((baseChange φ).obj C)
    hb (fun j ↦ (hP.2 j).2) hacyclic i
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (reversedDualBaseChangeIso φ g C hC.2))

end Langlands.CommutativeAlgebra
