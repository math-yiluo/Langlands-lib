/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

/-!
# Flatness in the intrinsic finite-coefficient presentation

## References

* Stacks Project, Modules on Sites, Tags 03EL, 03ER and 08FC
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

private theorem finite_scalar_lift
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (U : T.ProEt) (n : ℕ)
    (a : Fin n → (Scheme.proEtaleConstantRing T B).obj.obj (op U)) :
    ∃ S : Sieve U, S ∈ Scheme.ProEt.topology T U ∧
      ∀ (V : T.ProEt) (f : V ⟶ U), S f →
        ∀ i, ∃ c : ULift.{u + 1, u} B,
          (finiteCoefficientIntrinsicScalarMap T B).app (op V) c =
            (Scheme.proEtaleConstantRing T B).obj.map f.op (a i) := by
  induction n with
  | zero => exact ⟨⊤, (Scheme.ProEt.topology T).top_mem U, fun _ _ _ i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
    let Z := Presheaf.imageSieve (finiteCoefficientIntrinsicScalarMap T B) (a 0)
    refine ⟨Z ⊓ S, (Scheme.ProEt.topology T).intersection_covering
      (Presheaf.imageSieve_mem _ _ _) hS, ?_⟩
    intro V f hf
    refine Fin.cases ?_ (fun i ↦ hs V f hf.2 i)
    exact hf.1

private def relationSieve
    (T : Scheme.{u}) (B : Type u) [CommRing B]
    (N : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B))
    {U : T.ProEt} {n : ℕ}
    (a : Fin n → (Scheme.proEtaleConstantRing T B).obj.obj (op U))
    (s : Fin n → N.val.obj (op U)) : Sieve U where
  arrows V f := ∃ (l : ℕ)
    (b : Fin n → Fin l → (Scheme.proEtaleConstantRing T B).obj.obj (op V))
    (t : Fin l → N.val.obj (op V)),
    (∀ i, N.val.map f.op (s i) = ∑ j, b i j • t j) ∧
    (∀ j, ∑ i, (Scheme.proEtaleConstantRing T B).obj.map f.op (a i) * b i j = 0)
  downward_closed := by
    rintro V W f ⟨l, b, t, hs, ha⟩ g
    refine ⟨l, (fun i j ↦ (Scheme.proEtaleConstantRing T B).obj.map g.op (b i j)),
      (fun j ↦ N.val.map g.op (t j)), ?_, ?_⟩
    · intro i
      simp only [op_comp, N.val.map_comp_apply, hs, map_sum, N.val.map_smul]
      rfl
    · intro j
      simp only [op_comp, Functor.map_comp_apply, ← map_mul, ← map_sum, ha, map_zero]

/-- The associated-module-sheaf realization preserves flat fixed-coefficient sheaves. -/
theorem intrinsicRealization_flat
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (hM : ObjectProperty.flat M) :
    SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := Scheme.proEtaleConstantRing T B)
      ((finiteCoefficientIntrinsicRealization T B).obj M) := by
  classical
  let A := ULift.{u + 1, u} B
  have : Finite A := Finite.of_equiv B Equiv.ulift.symm
  let J := Scheme.ProEt.topology T
  let R := Scheme.proEtaleConstantRing T B
  let N := (finiteCoefficientIntrinsicRealization T B).obj M
  obtain ⟨e⟩ := intrinsicRealization_restriction T B
  have hN : ObjectProperty.flat ((Scheme.proEtaleModuleRestriction T B).obj N) :=
    ObjectProperty.prop_of_iso _ (e.app M).symm hM
  let N' := (Scheme.proEtaleModuleRestriction T B).obj N
  have hrel := Sheaf.hasLocallyTrivialRelations_of_flat hN
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1} R N).mpr
  intro U n a s hs
  let Z := relationSieve T B N a s
  refine ⟨Z, ?_, fun V f hf ↦ hf⟩
  obtain ⟨S, hS, hfac⟩ := finite_scalar_lift T B U n a
  apply J.transitive hS
  intro V f hf
  choose c hc using hfac V f hf
  let d : Matrix (Fin 1) (Fin n) A := fun _ i ↦ c i
  let y : Fin n → N'.obj.obj (op V) := fun i ↦ N.val.map f.op (s i)
  have he : ∀ k, ∑ i, d k i • y i = 0 := by
    intro k
    change ∑ i, (finiteCoefficientIntrinsicScalarMap T B).app (op V) (c i) •
      N.val.map f.op (s i) = 0
    simp only [hc]
    have h := congrArg (N.val.map f.op) hs
    simp only [map_sum, map_zero, N.val.map_smul] at h
    exact h
  obtain ⟨S', hS', hfac'⟩ := hrel y d he
  apply J.superset_covering _ hS'
  intro W g hg
  obtain ⟨l, b, t, hb, ht⟩ := hfac' g hg
  let β (W : T.ProEtᵒᵖ) : A →+* R.obj.obj W :=
    ((finiteCoefficientIntrinsicScalarMap T B).app W).hom
  let t' : Fin l → N.val.obj (op W) := t
  refine ⟨l, (fun i j ↦ β (op W) (b i j)), t', ?_, ?_⟩
  · intro i
    have hi := ht i
    change N.val.map g.op (N.val.map f.op (s i)) =
      ∑ j, β (op W) (b i j) • t' j at hi
    simpa only [op_comp, N.val.map_comp_apply] using hi
  · intro j
    have hb' := congrFun (congrFun hb 0) j
    have hz := congrArg (β (op W)) hb'
    simp only [Matrix.mul_apply, Matrix.zero_apply, map_sum, map_mul, map_zero] at hz
    change ∑ i, R.obj.map (g ≫ f).op (a i) * β (op W) (b i j) = 0
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change R.obj.map (g ≫ f).op (a i) =
      (finiteCoefficientIntrinsicScalarMap T B).app (op W) (c i)
    rw [op_comp, Functor.map_comp_apply, ← hc i]
    exact (NatTrans.naturality_apply (finiteCoefficientIntrinsicScalarMap T B) g.op
      (c i)).symm

end AlgebraicGeometry.ProEtale
