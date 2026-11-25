/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseRationalScalarFiberMaps
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientFiberEndomorphisms
import WeilConjectures.CategoryTheory.Pseudofunctor.LisseFiberCoherenceNormalization

/-!
# Coherent scalar comparisons for geometric fibres

## References

* Deligne, Weil II (1.1.1) b)-d), pp. 146-147
* Weil II (1.1.1) d)
-/

@[expose] public section

universe d
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- Transport a rational coefficient comparison to the recorded pseudofunctor categories. -/
noncomputable def lisseCoefficientFiberRawComparison
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (E₀ L₀ : Padic.FiniteCoefficientFields l K) (f : E₀ ⟶ L₀)
    (e : S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K) ≅
      lisseRationalScalarExtension l E₀.val Y L₀.val
          (IntermediateField.inclusion (leOfHom f)) ⋙ S L₀ ⋙
        ModuleCat.extendScalars (algebraMap L₀.val K)) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let J := fun E₀ : Padic.FiniteCoefficientFields l K ↦
      (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
        S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    J E₀ ≅ (P.map f.toLoc).toFunctor ⋙ J L₀ := by
  let D := lisseCoefficientDiagramData l Y K
  let P := D.diagram
  let T := (eqToHom (D.obj_eq E₀)).toFunctor
  let U := (eqToHom (D.obj_eq E₀).symm).toFunctor
  let V := (eqToHom (D.obj_eq L₀)).toFunctor
  let Q := lisseRationalScalarExtension l E₀.val Y L₀.val
    (IntermediateField.inclusion (leOfHom f))
  let R := (P.map f.toLoc).toFunctor
  let H := S L₀ ⋙ ModuleCat.extendScalars (algebraMap L₀.val K)
  have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have he := D.map_eq E₀ L₀ (leOfHom f)
  rw [hf] at he
  have h : U ⋙ R ⋙ V = Q := congrArg Cat.Hom.toFunctor he
  let cancel (C D : Cat.{d + 1, d + 2}) (h : C = D) :
      (eqToHom h).toFunctor ⋙ (eqToHom h.symm).toFunctor ≅ 𝟭 C := by
    cases h
    exact Functor.leftUnitor _
  let a : T ⋙ Q ≅ R ⋙ V :=
    Functor.isoWhiskerLeft T (eqToIso h.symm) ≪≫
      (Functor.associator T U (R ⋙ V)).symm ≪≫
        Functor.isoWhiskerRight (cancel _ _ (D.obj_eq E₀)) (R ⋙ V) ≪≫
          Functor.leftUnitor _
  exact Functor.isoWhiskerLeft T e ≪≫
    (Functor.associator T Q H).symm ≪≫ Functor.isoWhiskerRight a H ≪≫
      Functor.associator R V H

end AlgebraicGeometry.Scheme
