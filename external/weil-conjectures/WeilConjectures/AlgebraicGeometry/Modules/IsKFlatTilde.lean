/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.Modules.TildeStalkTensorComparison
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-!
# Associated sheaves of K-flat complexes on affine schemes

## References

* Stacks Project, Derived Categories of Schemes, Lemma 36.3.6 (Tag 08DV)
* Stacks Project, Lemma 36.3.6 (Tag 08DV)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

private theorem acyclic_restrictScalars_iff
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (F : CochainComplex (ModuleCat.{u} B) ℤ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F).Acyclic ↔ F.Acyclic := by
  simp only [HomologicalComplex.acyclic_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The total tensor's coproduct instance unfolds the composed tilde and stalk functors.
private theorem nonempty_restrictScalars_tensor_tildeStalkIso
    (A : Type u) [CommRing A] (x : Spec (.of A))
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} ((Spec (.of A)).presheaf.stalk x)) ℤ) :
    Nonempty
      (((ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor F
          (((RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A) (Spec (.of A)).Modules
              _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ => tilde.map_zero⟩
              (ComplexShape.up ℤ)).obj K)) (curriedTensor _)) ≅
        CochainComplex.mapBifunctor
          (((ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F) K (curriedTensor _)) := by
  let : (tilde.functor (.of A)).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let S := tilde.functor (.of A) ⋙
    RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x
  have : S.PreservesZeroMorphisms := by
    constructor
    intro M M'
    change (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace x).map
      (tilde.map (0 : M ⟶ M')) = 0
    rw [tilde.map_zero, Functor.map_zero]
  let U := ModuleCat.restrictScalars (StructureSheaf.toStalk A x).hom
  let T := (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj S).obj (curriedTensor _)
  let : T.PreservesZeroMorphisms := by
    constructor
    intro N N'
    apply NatTrans.ext
    funext M
    change (0 : N ⟶ N') ▷ S.obj M = 0
    exact MonoidalPreadditive.zero_whiskerRight
  have hT : ∀ N, (T.obj N).PreservesZeroMorphisms := by
    intro N
    constructor
    intro M M'
    change N ◁ S.map (0 : M ⟶ M') = 0
    rw [Functor.map_zero, MonoidalPreadditive.whiskerLeft_zero]
  obtain ⟨e⟩ := nonempty_restrictScalars_tensor_tildeStalkNatIso A x
  exact ⟨asIso (HomologicalComplex.mapBifunctorComparison (F := T) (G₁ := U)
    (G₂ := 𝟭 _) (G := U) e.hom
    (ComplexShape.up ℤ) F K)⟩

/-- The termwise associated sheaf of a K-flat
complex of modules over a commutative ring `A` is K-flat on `Spec A`. -/
theorem isKFlat_tilde (A : Type u) [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ,
      F.Acyclic → (CochainComplex.mapBifunctor F K (curriedTensor (ModuleCat A))).Acyclic) :
    CochainComplex.IsKFlatTensor (R := (Spec (.of A)).sheaf)
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A) (Spec (.of A)).Modules
        _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ => tilde.map_zero⟩
        (ComplexShape.up ℤ)).obj K) :=
  by
    apply (RingedSpace.isKFlat_iff_stalk_isKFlat
      (Spec (.of A)).toRingedSpace _).2
    intro x F hF
    obtain ⟨e⟩ := nonempty_restrictScalars_tensor_tildeStalkIso A x K F
    have hF' := (acyclic_restrictScalars_iff (StructureSheaf.toStalk A x).hom F).2 hF
    have h := hK _ hF'
    apply (acyclic_restrictScalars_iff (StructureSheaf.toStalk A x).hom _).1
    intro i
    exact (h i).of_iso e.symm

end AlgebraicGeometry

