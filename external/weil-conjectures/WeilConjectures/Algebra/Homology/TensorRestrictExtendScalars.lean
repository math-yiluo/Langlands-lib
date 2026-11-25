/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-!
# Tensor total complexes and restriction of scalars

Source: Stacks Project, More on Algebra, Tag 06Y1, proof.
(blueprint: lem-pc-tensor-restrict-extend-scalars)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CochainComplex

/-- Restricting a tensor total complex after extension of the second factor agrees
with tensoring its restriction with the original second factor.
Source: Stacks Project, More on Algebra, Tag 06Y1, proof.
(blueprint: lem-pc-tensor-restrict-extend-scalars)

Proof: in bidegree (p,q), define the A-linear map on balanced pure tensors by
`l ⊗ (b ⊗ k) ↦ (b • l) ⊗ k`. The inverse is `l ⊗ k ↦ l ⊗ (1 ⊗ k)`.
The A-balancing relations follow from the restricted action through the ring homomorphism;
the B-balancing relation follows from associativity of the B-action on L. Tensor induction
shows both composites are identities. These maps are natural in both module factors:
B-linearity of each differential of L handles the first factor, and A-linearity of the
differentials of K handles the second. Hence they commute with both bicomplex differentials.
Restriction of scalars preserves coproducts. Apply the bidegree maps on every summand
p+q=n and the coproduct universal property to obtain inverse degreewise maps. Their
compatibility with both differentials also implies compatibility with the total differential,
including its sign (-1)^p. Thus they define inverse cochain maps. The construction uses no
flatness or boundedness: coproduct maps have finite support on each input, even for an
unbounded complex, and the same tensor formulas hold for zero rings. -/
theorem nonempty_tensorRestrictExtendScalarsIso
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (L : CochainComplex (ModuleCat.{u} B) ℤ)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    Nonempty
      ((((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj
          (mapBifunctor L
            (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj K)
            (curriedTensor _))) ≅
        mapBifunctor
          (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj L)
          K (curriedTensor _)) := by
  classical
  obtain ⟨e, he⟩ := ModuleCat.exists_tensorRestrictExtend_module_natural ρ
  let T := (((curriedTensor (ModuleCat B)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj L).obj
      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj K)
  let : (ModuleCat.restrictScalars ρ).PreservesTotalComplex T (.up ℤ) :=
    fun n ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso (ModuleCat.restrictScalars ρ) T (.up ℤ)).symm
  let f :
      ((((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℤ)).obj T) ≅
      (((curriedTensor (ModuleCat A)).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj
          (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj L)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents (fun j ↦ e (L.X i) (K.X j))
        (by
          intro j j' hj
          change (e (L.X i) (K.X j)).hom ≫ (ModuleCat.restrictScalars ρ).obj (L.X i) ◁ K.d j j' =
            (ModuleCat.restrictScalars ρ).map (L.X i ◁ (ModuleCat.extendScalars ρ).map (K.d j j')) ≫
              (e (L.X i) (K.X j')).hom
          exact (he (L.X i) (L.X i) (K.X j) (K.X j') (𝟙 _) (K.d j j')).symm))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e (L.X i) (K.X j)).hom ≫ (ModuleCat.restrictScalars ρ).map (L.d i i') ▷ K.X j =
          (ModuleCat.restrictScalars ρ).map (L.d i i' ▷ (ModuleCat.extendScalars ρ).obj (K.X j)) ≫
            (e (L.X i') (K.X j)).hom
        simpa [MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight] using
          (he (L.X i) (L.X i') (K.X j) (K.X j) (L.d i i') (𝟙 _)).symm)
  exact ⟨t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)⟩

end CochainComplex
