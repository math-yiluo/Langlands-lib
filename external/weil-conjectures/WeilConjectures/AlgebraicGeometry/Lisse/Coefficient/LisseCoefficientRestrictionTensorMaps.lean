/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionIntegralModel

/-! Maps of integral adic systems induced by a central coefficient tensor.

## References

* Deligne, Weil II (1.1.1) b)-d), pp. 146-147, restriction and extension of coefficients
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe d u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
section
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {V W : Type v} [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module S V] [IsScalarTower R S V]
  [Module R W] [Module S W] [IsScalarTower R S W]
private def avgBilinear (f : V →ₗ[R] W) : S →ₗ[R] S →ₗ[R] (V →ₗ[R] W) where
  toFun x :=
    { toFun := fun y ↦
        { toFun := fun z ↦ x • f (y • z)
          map_add' := by intros; simp only [smul_add, map_add]
          map_smul' := by
            intro r z
            change x • f (y • (r • z)) = r • (x • f (y • z))
            rw [smul_comm y r, map_smul, smul_comm x r] }
      map_add' := by
        intro a b
        ext z
        change x • f ((a + b) • z) = x • f (a • z) + x • f (b • z)
        simp only [add_smul, map_add, smul_add]
      map_smul' := by
        intro r y
        ext z
        change x • f ((r • y) • z) = r • (x • f (y • z))
        rw [smul_assoc, map_smul, smul_comm x r] }
  map_add' := by
    intro a b
    ext y z
    change (a + b) • f (y • z) = a • f (y • z) + b • f (y • z)
    exact add_smul _ _ _
  map_smul' := by
    intro r x
    ext y z
    exact smul_assoc r x (f (y • z))

private def avgRaw (f : V →ₗ[R] W) (t : TensorProduct R S S) : V →ₗ[R] W :=
  TensorProduct.lift (avgBilinear (S := S) f) t
@[simp] private theorem avgRaw_zero (f : V →ₗ[R] W) : avgRaw (S := S) f 0 = 0 :=
  map_zero _
@[simp] private theorem avgRaw_add (f : V →ₗ[R] W) (t z : TensorProduct R S S) :
    avgRaw (S := S) f (t + z) = avgRaw (S := S) f t + avgRaw (S := S) f z :=
  (TensorProduct.lift (avgBilinear (S := S) f)).map_add _ _
@[simp] private theorem avgRaw_tmul (f : V →ₗ[R] W) (x y : S) (z : V) :
    avgRaw (S := S) f (x ⊗ₜ[R] y) z = x • f (y • z) := rfl

private def avg (f : V →ₗ[R] W) (t : TensorProduct R S S)
    (ht : ∀ s : S, (s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s) * t = 0) : V →ₗ[S] W where
  __ := avgRaw (S := S) f t
  map_smul' s z := by
    have h₁ : avgRaw (S := S) f t (s • z) = avgRaw (S := S) f (((1 : S) ⊗ₜ[R] s) * t) z := by
      clear ht
      induction t using TensorProduct.inductionOn with
      | tmul x y => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          avgRaw_tmul, mul_smul, smul_comm y s]
      | add t w ht hw => simp only [mul_add, avgRaw_add, LinearMap.add_apply, ht, hw]
    have h₂ : avgRaw (S := S) f ((s ⊗ₜ[R] (1 : S)) * t) z = s • avgRaw (S := S) f t z := by
      clear ht h₁
      induction t using TensorProduct.inductionOn with
      | tmul x y => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          avgRaw_tmul, mul_smul]
      | add t w ht hw => simp only [mul_add, avgRaw_add, LinearMap.add_apply, smul_add, ht, hw]
    have hc := ht s
    rw [sub_mul, sub_eq_zero] at hc
    exact h₁.trans (hc.symm ▸ h₂)
variable {V' W' : Type v} [AddCommGroup V'] [AddCommGroup W']
  [Module R V'] [Module S V'] [IsScalarTower R S V']
  [Module R W'] [Module S W'] [IsScalarTower R S W']
private theorem avgRaw_naturality (f : V →ₗ[R] W) (f' : V' →ₗ[R] W')
    (a : V →ₗ[S] V') (b : W →ₗ[S] W') (h : ∀ z, b (f z) = f' (a z))
    (t : TensorProduct R S S) (z : V) :
    b (avgRaw (S := S) f t z) = avgRaw (S := S) f' t (a z) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp only [avgRaw_tmul, map_smul, h]
  | add t u ht hu => simp only [avgRaw_add, LinearMap.add_apply, map_add, ht, hu]

omit [Module R V'] [IsScalarTower R S V'] in
private theorem avgRaw_comp (f : V →ₗ[R] W) (b : W →ₗ[S] V') (a : V →ₗ[S] V')
    (h : ∀ z, b (f z) = a z) (t : TensorProduct R S S) (z : V) :
    b (avgRaw (S := S) f t z) = Algebra.TensorProduct.lmul' R t • a z := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp only [avgRaw_tmul, map_smul, h,
      Algebra.TensorProduct.lmul'_apply_tmul, mul_smul]
  | add t u ht hu => simp only [avgRaw_add, LinearMap.add_apply, map_add, ht, hu, add_smul]
end

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
section AveragedSheaves
variable (Y : Scheme.{d})
variable {R S : Type (d + 1)} [CommRing R] [CommRing S] (f : R →+* S)
variable [Algebra R S]
variable (hf : algebraMap R S = f)
private def sheafAverage
    (M H : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S))
    (η : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj H)
    (t : TensorProduct R S S)
    (ht : ∀ s : S, (s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s) * t = 0) : M ⟶ H := by
  letI (U : Y.Etaleᵒᵖ) : Module R (M.obj.obj U) := Module.compHom _ f
  letI (U : Y.Etaleᵒᵖ) : Module R (H.obj.obj U) := Module.compHom _ f
  letI (U : Y.Etaleᵒᵖ) : IsScalarTower R S (M.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  letI (U : Y.Etaleᵒᵖ) : IsScalarTower R S (H.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  refine ⟨{ app := fun U ↦ ModuleCat.ofHom (avg (V := M.obj.obj U)
    (W := H.obj.obj U) (η.hom.app U).hom t ht), naturality := ?_ }⟩
  intro U V w
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (avgRaw (V := M.obj.obj V) (W := H.obj.obj V) (S := S)
    (η.hom.app V).hom t).toFun (M.obj.map w z) =
    H.obj.map w ((avgRaw (V := M.obj.obj U) (W := H.obj.obj U) (S := S)
      (η.hom.app U).hom t).toFun z)
  symm
  apply avgRaw_naturality (a := (M.obj.map w).hom) (b := (H.obj.map w).hom)
  intro z
  exact (congrArg (fun k ↦ k z) (congrArg ModuleCat.Hom.hom
    (η.hom.naturality w))).symm
private theorem sheafAverage_square
    (M H M' H' : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S))
    (η : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj H)
    (η' : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M' ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj H')
    (a : M ⟶ M') (b : H ⟶ H')
    (h : (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} f)).map a ≫ η' =
      η ≫ (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).map b)
    (t : TensorProduct R S S)
    (ht : ∀ s : S, (s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s) * t = 0) :
    a ≫ sheafAverage Y f hf M' H' η' t ht = sheafAverage Y f hf M H η t ht ≫ b := by
  let (U : Y.Etaleᵒᵖ) : Module R (M.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (M.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  let (U : Y.Etaleᵒᵖ) : Module R (H.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (H.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  let (U : Y.Etaleᵒᵖ) : Module R (M'.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (M'.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  let (U : Y.Etaleᵒᵖ) : Module R (H'.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (H'.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (avgRaw (V := M'.obj.obj U) (W := H'.obj.obj U) (S := S)
    (η'.hom.app U).hom t).toFun (a.hom.app U z) =
    b.hom.app U ((avgRaw (V := M.obj.obj U) (W := H.obj.obj U) (S := S)
      (η.hom.app U).hom t).toFun z)
  symm
  apply avgRaw_naturality
  intro z
  exact (congrArg (fun k ↦ k.hom.app U z) h).symm

private theorem sheafAverage_comp
    (M H N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S))
    (η : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj H)
    (b : H ⟶ N) (a : M ⟶ N)
    (h : η ≫ (sheafCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{d + 1} f)).map b =
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).map a)
    (t : TensorProduct R S S)
    (ht : ∀ s : S, (s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s) * t = 0) :
    sheafAverage Y f hf M H η t ht ≫ b = Algebra.TensorProduct.lmul' R t • a := by
  let (U : Y.Etaleᵒᵖ) : Module R (M.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (M.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  let (U : Y.Etaleᵒᵖ) : Module R (H.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (H.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  let (U : Y.Etaleᵒᵖ) : Module R (N.obj.obj U) := Module.compHom _ f
  let (U : Y.Etaleᵒᵖ) : IsScalarTower R S (N.obj.obj U) :=
    IsScalarTower.of_algebraMap_smul fun r z ↦ by
      change algebraMap R S r • z = f r • z
      rw [hf]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change b.hom.app U ((avgRaw (V := M.obj.obj U) (W := H.obj.obj U) (S := S)
    (η.hom.app U).hom t).toFun z) =
    Algebra.TensorProduct.lmul' R t • a.hom.app U z
  apply avgRaw_comp
  intro z
  exact congrArg (fun k ↦ k.hom.app U z) h

end AveragedSheaves
end AlgebraicGeometry.Scheme

private def naturalEpiDesc {C D : Type*} [Category C] [Category D] [Abelian D]
    {A F H : C ⥤ D} (δ : A ⟶ F) [∀ x, Epi (δ.app x)] (σ : A ⟶ H)
    (hk : ∀ x, kernel.ι (δ.app x) ≫ σ.app x = 0) : F ⟶ H where
  app x := Abelian.epiDesc (δ.app x) (σ.app x) (hk x)
  naturality X Y f := by
    apply (cancel_epi (δ.app X)).mp
    calc
      δ.app X ≫ (F.map f ≫ Abelian.epiDesc (δ.app Y) (σ.app Y) (hk Y)) =
          A.map f ≫ (δ.app Y ≫ Abelian.epiDesc (δ.app Y) (σ.app Y) (hk Y)) := by
        rw [← Category.assoc, ← δ.naturality, Category.assoc]
      _ = A.map f ≫ σ.app Y := by rw [Abelian.comp_epiDesc]
      _ = σ.app X ≫ H.map f := σ.naturality f
      _ = δ.app X ≫ (Abelian.epiDesc (δ.app X) (σ.app X) (hk X) ≫ H.map f) := by
        rw [← Category.assoc, Abelian.comp_epiDesc]

namespace AlgebraicGeometry.Scheme
section StalkDescent
variable (Y : Scheme.{d})
variable {S : Type (d + 1)} [CommRing S]
private lemma point_annihilated (p : GrothendieckTopology.Point.{d + 1} Y.smallEtaleTopology)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S)) (I : Ideal S)
    (hN : ∀ U : Y.Etale, I • (⊤ : Submodule S (N.obj.obj (op U))) = ⊥) :
    I • (⊤ : Submodule S ((p.sheafFiber (A := ModuleCat.{d + 1} S)).obj N)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro r hr z _
  obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := N.obj) z
  have hz : r • s = 0 := by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := s))
    rw [hN U] at h
    exact h
  change r • p.toPresheafFiber U x N.obj s = 0
  rw [← map_smul, hz, map_zero]

private theorem kernel_comp_zero_of_stalk_ideal
    {M N H : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S)}
    (v : M ⟶ N) (σ : M ⟶ H) (I : Ideal S)
    (hH : ∀ U : Y.Etale, I • (⊤ : Submodule S (H.obj.obj (op U))) = ⊥)
    (hv : ∀ x : Y,
      let p := (pointSmallEtale (Y.algClosurePoint x)).ulift.{d + 1}
      let T := p.sheafFiber (A := ModuleCat.{d + 1} S)
      LinearMap.ker (T.map v).hom = I • (⊤ : Submodule S (T.obj M))) :
    kernel.ι v ≫ σ = 0 := by
  have : LocallySmall.{d + 1} Y.Etale := locallySmall_max.{d + 1} (C := Y.Etale)
  refine ((isConservativeFamilyOfPoints_ulift_pointSmallEtale Y).jointlyFaithful
    (ModuleCat.{d + 1} S)).map_injective ?_
  rintro ⟨-, ⟨x⟩⟩
  let p := (pointSmallEtale (Y.algClosurePoint x)).ulift.{d + 1}
  let T := p.sheafFiber (A := ModuleCat.{d + 1} S)
  change T.map (kernel.ι v ≫ σ) = T.map 0
  rw [T.map_comp, T.map_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz : (T.map (kernel.ι v)).hom z ∈ LinearMap.ker (T.map v).hom := by
    change (T.map v).hom ((T.map (kernel.ι v)).hom z) = 0
    have h := congrArg (fun k ↦ k z) (congrArg ModuleCat.Hom.hom
      (show T.map (kernel.ι v) ≫ T.map v = 0 by
        rw [← T.map_comp, kernel.condition, T.map_zero]))
    exact h
  rw [hv x] at hz
  have hi : (I • (⊤ : Submodule S (T.obj M))).map (T.map σ).hom ≤
      (⊥ : Submodule S (T.obj H)) := by
    rw [Submodule.map_smul'']
    refine (Submodule.smul_le.mpr ?_).trans
      (le_of_eq (point_annihilated Y p H I hH))
    intro r hr z _
    exact Submodule.smul_mem_smul hr (Submodule.mem_top (x := z))
  exact hi (Submodule.mem_map_of_mem hz)
section Lisse
variable (l : ℕ) [Fact l.Prime]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (L : Type (d + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
private theorem integralTransition_epi (F : LisseIntegralSheaf l L Y)
    (m n : ℕ) (h : m ≤ n) : Epi (F.obj.map (homOfLE h).op) := by
  have : LocallySmall.{d + 1} Y.Etale := locallySmall_max.{d + 1} (C := Y.Etale)
  apply ((isConservativeFamilyOfPoints_ulift_pointSmallEtale Y).jointlyReflectEpimorphisms
    (ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l L))).epi_iff _ |>.mpr
  rintro ⟨-, ⟨x⟩⟩
  exact (ModuleCat.epi_iff_surjective _).mpr
    (lisseIntegralStalk_transition (l := l) (Y := Y) (E := L)
      (y := Y.algClosurePoint x) F m n h).1
end Lisse
end StalkDescent
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section Multiplication
variable (Y : Scheme.{d})
variable {R S : Type (d + 1)} [CommRing R] [CommRing S]
private def multiplicationUnit (f : R →+* S) (I : Ideal S)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S)) (v : M ⟶ N)
    (hN : ∀ U : Y.Etale, I • (⊤ : Submodule S (N.obj.obj (op U))) = ⊥) :
    (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{d + 1} ((Ideal.Quotient.mk I).comp f))).obj
          (lisseCoherence_quotientSheafLift Y I N hN) :=
  ⟨{ app U := ModuleCat.ofHom
       (X := ((sheafCompose Y.smallEtaleTopology
         (ModuleCat.restrictScalars.{d + 1} f)).obj M).obj.obj U)
       (Y := ((sheafCompose Y.smallEtaleTopology
         (ModuleCat.restrictScalars.{d + 1} ((Ideal.Quotient.mk I).comp f))).obj
           (lisseCoherence_quotientSheafLift Y I N hN)).obj.obj U)
       { toFun := v.hom.app U
         map_add' := (v.hom.app U).hom.map_add
         map_smul' := fun r x ↦ (v.hom.app U).hom.map_smul (f r) x }
     naturality U V w := by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro x
       exact congrArg (fun k ↦ k x) (congrArg ModuleCat.Hom.hom (v.hom.naturality w)) }⟩

private def quotientMultiplication (f : R →+* S) (I : Ideal S)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S)) (v : M ⟶ N)
    (hN : ∀ U : Y.Etale, I • (⊤ : Submodule S (N.obj.obj (op U))) = ⊥) :
    lisseCoherence_quotientScalarLevel Y f I
      ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M) ⟶ N :=
  (sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{d + 1} (Ideal.Quotient.mk I))).map
      (((lisseCoherence_scalarSheafAdj Y ((Ideal.Quotient.mk I).comp f)).homEquiv _ _).symm
        (multiplicationUnit Y f I M N v hN)) ≫
    (lisseCoherence_quotientSheafLiftIso Y I N hN).inv

private theorem quotientMultiplication_unit (f : R →+* S) (I : Ideal S)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} S)) (v : M ⟶ N)
    (hN : ∀ U : Y.Etale, I • (⊤ : Submodule S (N.obj.obj (op U))) = ⊥)
    (U : Y.Etale) (x : M.obj.obj (op U)) :
    (quotientMultiplication Y f I M N v hN).hom.app (op U)
      (lisseCoherence_quotientScalarGenerator Y f I
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M)
          U 1 x) = v.hom.app (op U) x := by
  let A := lisseCoherence_scalarSheafAdj Y ((Ideal.Quotient.mk I).comp f)
  have h := (A.homEquiv _ _).apply_symm_apply (multiplicationUnit Y f I M N v hN)
  rw [Adjunction.homEquiv_apply] at h
  have hx := congrArg (fun k ↦ k.hom.app (op U) x) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply] at hx
  change (((A.homEquiv _ _).symm (multiplicationUnit Y f I M N v hN)).hom.app (op U))
      ((lisseCoherence_scalarSheafUnit Y ((Ideal.Quotient.mk I).comp f)
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj M)).hom.app
          (op U) x) = v.hom.app (op U) x at hx
  rw [lisseCoherence_scalarSheafUnit_apply] at hx
  exact hx
section Lisse
variable (l : ℕ) [Fact l.Prime]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (E L : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
private lemma restrictionSource_le (m : ℕ) :
    m ≤ lisseRamificationIndex l E L ι * (lisseScalarSourceIndex l E L ι m + 1) - 1 := by
  rw [lisseCoherence_scalarIndex_eq]
  have he := (lisseRamificationIndex_exists l E L ι).choose_spec.1
  exact Nat.le_sub_one_of_lt (Nat.lt_mul_div_succ m he)

private def restrictionMultiplicationLevel
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F)) (m : ℕ) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    ((lisseIntegralScalarExtension l E Y L ι).obj G).obj.obj (op m) ⟶ F.obj.obj (op m) := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  exact (lisseScalarLevelIso l E Y L ι G m).hom ≫
    quotientMultiplication Y (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionIdeal l L (m + 1))
      (F.obj.obj (op (lisseRamificationIndex l E L ι *
        (lisseScalarSourceIndex l E L ι m + 1) - 1))) (F.obj.obj (op m))
      (F.obj.map (homOfLE (restrictionSource_le l E L ι m)).op)
      (lisseCoherence_integralLevel_annihilated l L Y F m)

private theorem restrictionMultiplicationLevel_unit
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseRamificationIndex l E L ι *
        (lisseScalarSourceIndex l E L ι m + 1) - 1))).obj.obj (op U)) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    (restrictionMultiplicationLevel Y l E L ι F hF m).hom.app (op U)
      (lisseScalarGenerator l E Y L ι G m U 1 x) =
      (F.obj.map (homOfLE (restrictionSource_le l E L ι m)).op).hom.app (op U) x := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  let z := lisseIntegralScalarGenerator l E Y L ι G m U 1 x
  have he := congrArg (fun v ↦ v.hom.app (op U) z)
    (lisseScalarLevelIso l E Y L ι G m).inv_hom_id
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] at he
  dsimp only [restrictionMultiplicationLevel, lisseScalarGenerator]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply]
  rw [he]
  exact quotientMultiplication_unit Y _ _ _ _ _ _ U x
private theorem restrictionMultiplicationLevel_naturality
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (m : ℕ) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    ((lisseIntegralScalarExtension l E Y L ι).obj G).obj.map
      (homOfLE (Nat.le_succ m)).op ≫ restrictionMultiplicationLevel Y l E L ι F hF m =
    restrictionMultiplicationLevel Y l E L ι F hF (m + 1) ≫
      F.obj.map (homOfLE (Nat.le_succ m)).op := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  apply lisseCoherence_chosenScalarLevel_ext l E Y L ι G (m + 1)
    (F.obj.obj (op m))
    (lisseCoherence_integralLevel_annihilated_le l L Y F m (m + 1) (Nat.le_succ m))
  intro U x
  change (restrictionMultiplicationLevel Y l E L ι F hF m).hom.app (op U)
    ((((lisseIntegralScalarExtension l E Y L ι).obj G).obj.map
      (homOfLE (Nat.le_succ m)).op).hom.app (op U)
        (lisseScalarGenerator l E Y L ι G (m + 1) U 1 x)) =
    (F.obj.map (homOfLE (Nat.le_succ m)).op).hom.app (op U)
      ((restrictionMultiplicationLevel Y l E L ι F hF (m + 1)).hom.app (op U)
        (lisseScalarGenerator l E Y L ι G (m + 1) U 1 x))
  rw [lisseCoherence_extendedGenerator_transition, map_one,
    restrictionMultiplicationLevel_unit, restrictionMultiplicationLevel_unit]
  dsimp only [G, lisseIntegralRestrictionRaw, Functor.comp_map, Functor.op_map]
  change (F.obj.map _).hom.app (op U) ((F.obj.map _).hom.app (op U) x) =
    (F.obj.map _).hom.app (op U) ((F.obj.map _).hom.app (op U) x)
  simp only [← ModuleCat.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp]
  rfl
end Lisse
end Multiplication
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section Units
variable (Y : Scheme.{d})
section Lisse
variable (l : ℕ) [Fact l.Prime]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (E L : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
private def restrictionReindex : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show Monotone (fun m : ℕ ↦ lisseRamificationIndex l E L ι *
      (lisseScalarSourceIndex l E L ι m + 1) - 1) from
    fun _ _ h ↦ Nat.sub_le_sub_right
      (Nat.mul_le_mul_left (lisseRamificationIndex l E L ι)
        (Nat.succ_le_succ (lisseCoherence_scalarIndex_mono l E L ι h))) 1).functor.op
private def restrictionTransition (F : LisseIntegralSheaf l L Y) :
    restrictionReindex l E L ι ⋙ F.obj ⟶ F.obj where
  app m := F.obj.map (homOfLE (restrictionSource_le l E L ι m.unop)).op
  naturality m n w := by
    change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    congr 1

private def restrictionUnitLevel
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F)) (m : ℕ) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    let res := sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))
    res.obj (F.obj.obj (op (lisseRamificationIndex l E L ι *
      (lisseScalarSourceIndex l E L ι m + 1) - 1))) ⟶
      res.obj (((lisseIntegralScalarExtension l E Y L ι).obj G).obj.obj (op m)) := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  let res := sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))
  exact lisseCoherence_scalarSheafUnit Y
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))).comp
      (lisseIntegerInclusion l E L ι))
    (G.obj.obj (op (lisseScalarSourceIndex l E L ι m))) ≫
      res.map (lisseScalarLevelIso l E Y L ι G m).inv

private theorem restrictionUnitLevel_apply
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseRamificationIndex l E L ι *
      (lisseScalarSourceIndex l E L ι m + 1) - 1))).obj.obj (op U)) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    (restrictionUnitLevel Y l E L ι F hF m).hom.app (op U) x =
      lisseScalarGenerator l E Y L ι G m U 1 x := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  change (lisseScalarLevelIso l E Y L ι G m).inv.hom.app (op U)
    ((lisseCoherence_scalarSheafUnit Y
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))).comp
        (lisseIntegerInclusion l E L ι))
      (G.obj.obj (op (lisseScalarSourceIndex l E L ι m)))).hom.app (op U) x) = _
  rw [lisseCoherence_scalarSheafUnit_apply]
  rfl
private theorem restrictionUnitLevel_naturality
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F)) (m : ℕ) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    let res := sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))
    res.map (F.obj.map (homOfLE (Nat.sub_le_sub_right
      (Nat.mul_le_mul_left (lisseRamificationIndex l E L ι)
        (Nat.succ_le_succ (lisseScalarSourceIndex_le l E L ι m))) 1)).op) ≫
      restrictionUnitLevel Y l E L ι F hF m =
    restrictionUnitLevel Y l E L ι F hF (m + 1) ≫
      res.map (((lisseIntegralScalarExtension l E Y L ι).obj G).obj.map
        (homOfLE (Nat.le_succ m)).op) := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply]
  rw [restrictionUnitLevel_apply, restrictionUnitLevel_apply]
  change lisseScalarGenerator l E Y L ι G m U.unop 1
    ((F.obj.map (homOfLE (Nat.sub_le_sub_right
      (Nat.mul_le_mul_left (lisseRamificationIndex l E L ι)
        (Nat.succ_le_succ (lisseScalarSourceIndex_le l E L ι m))) 1)).op).hom.app U z) =
    ((((lisseIntegralScalarExtension l E Y L ι).obj G).obj.map
      (homOfLE (Nat.le_succ m)).op).hom.app U)
        (lisseScalarGenerator l E Y L ι G (m + 1) U.unop 1 z)
  rw [lisseCoherence_extendedGenerator_transition, map_one]
  rfl
end Lisse
end Units
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (E L : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section AveragedRestriction
variable [Algebra (Padic.coefficientExtensionIntegers l E)
  (Padic.coefficientExtensionIntegers l L)]

private def restrictionAverageLevel
    (hι : algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) = lisseIntegerInclusion l E L ι)
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (t : TensorProduct (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) (Padic.coefficientExtensionIntegers l L))
    (ht : ∀ s : Padic.coefficientExtensionIntegers l L,
      (s ⊗ₜ[Padic.coefficientExtensionIntegers l E] (1 : Padic.coefficientExtensionIntegers l L) -
        (1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[Padic.coefficientExtensionIntegers l E] s) *
          t = 0) (m : ℕ) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    F.obj.obj ((restrictionReindex l E L ι).obj (op m)) ⟶
      ((lisseIntegralScalarExtension l E Y L ι).obj G).obj.obj (op m) :=
  sheafAverage Y (lisseIntegerInclusion l E L ι) hι _ _
    (restrictionUnitLevel Y l E L ι F hF m) t ht

private theorem restrictionAverageLevel_naturality
    (hι : algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) = lisseIntegerInclusion l E L ι)
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (t : TensorProduct (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) (Padic.coefficientExtensionIntegers l L))
    (ht : ∀ s : Padic.coefficientExtensionIntegers l L,
      (s ⊗ₜ[Padic.coefficientExtensionIntegers l E] (1 : Padic.coefficientExtensionIntegers l L) -
        (1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[Padic.coefficientExtensionIntegers l E] s) *
          t = 0) (m : ℕ) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    (restrictionReindex l E L ι ⋙ F.obj).map (homOfLE (Nat.le_succ m)).op ≫
      restrictionAverageLevel l Y E L ι hι F hF t ht m =
    restrictionAverageLevel l Y E L ι hι F hF t ht (m + 1) ≫
      ((lisseIntegralScalarExtension l E Y L ι).obj G).obj.map
        (homOfLE (Nat.le_succ m)).op :=
  sheafAverage_square Y (lisseIntegerInclusion l E L ι) hι _ _ _ _
    (restrictionUnitLevel Y l E L ι F hF (m + 1))
    (restrictionUnitLevel Y l E L ι F hF m) _ _
    (restrictionUnitLevel_naturality Y l E L ι F hF m) t ht

private def restrictionAverage
    (hι : algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) = lisseIntegerInclusion l E L ι)
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (t : TensorProduct (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) (Padic.coefficientExtensionIntegers l L))
    (ht : ∀ s : Padic.coefficientExtensionIntegers l L,
      (s ⊗ₜ[Padic.coefficientExtensionIntegers l E] (1 : Padic.coefficientExtensionIntegers l L) -
        (1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[Padic.coefficientExtensionIntegers l E] s) *
          t = 0) :
    let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    restrictionReindex l E L ι ⋙ F.obj ⟶
      ((lisseIntegralScalarExtension l E Y L ι).obj G).obj :=
  NatTrans.ofOpSequence (restrictionAverageLevel l Y E L ι hι F hF t ht)
    (restrictionAverageLevel_naturality l Y E L ι hι F hF t ht)

private theorem restrictionAverage_kernel
    (hι : algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) = lisseIntegerInclusion l E L ι)
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (t : TensorProduct (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) (Padic.coefficientExtensionIntegers l L))
    (ht : ∀ s : Padic.coefficientExtensionIntegers l L,
      (s ⊗ₜ[Padic.coefficientExtensionIntegers l E] (1 : Padic.coefficientExtensionIntegers l L) -
        (1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[Padic.coefficientExtensionIntegers l E] s) *
          t = 0)
    (m : ℕᵒᵖ) :
    kernel.ι ((restrictionTransition Y l E L ι F).app m) ≫
      (restrictionAverage l Y E L ι hι F hF t ht).app m = 0 := by
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  let H := (lisseIntegralScalarExtension l E Y L ι).obj G
  apply kernel_comp_zero_of_stalk_ideal Y _ _
    (Padic.coefficientExtensionIdeal l L (m.unop + 1))
    (lisseCoherence_integralLevel_annihilated l L Y H m.unop)
  intro x
  exact (lisseIntegralStalk_transition (l := l) (E := L) (Y := Y)
    (y := Y.algClosurePoint x) F m.unop _ (restrictionSource_le l E L ι m.unop)).2

omit [Algebra (Padic.coefficientExtensionIntegers l E)
  (Padic.coefficientExtensionIntegers l L)] in
private theorem restrictionUnitLevel_comp
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F)) (m : ℕ) :
    restrictionUnitLevel Y l E L ι F hF m ≫
      (sheafCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
          (restrictionMultiplicationLevel Y l E L ι F hF m) =
      (sheafCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
          ((restrictionTransition Y l E L ι F).app (op m)) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (restrictionMultiplicationLevel Y l E L ι F hF m).hom.app U
    ((restrictionUnitLevel Y l E L ι F hF m).hom.app U z) = _
  rw [restrictionUnitLevel_apply, restrictionMultiplicationLevel_unit]
  rfl

private theorem restrictionAverageLevel_comp
    (hι : algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) = lisseIntegerInclusion l E L ι)
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y (lisseIntegralRestrictionRaw l Y E L ι F))
    (t : TensorProduct (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) (Padic.coefficientExtensionIntegers l L))
    (ht : ∀ s : Padic.coefficientExtensionIntegers l L,
      (s ⊗ₜ[Padic.coefficientExtensionIntegers l E] (1 : Padic.coefficientExtensionIntegers l L) -
        (1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[Padic.coefficientExtensionIntegers l E] s) *
          t = 0) (m : ℕ) :
    restrictionAverageLevel l Y E L ι hι F hF t ht m ≫
      restrictionMultiplicationLevel Y l E L ι F hF m =
        Algebra.TensorProduct.lmul' (Padic.coefficientExtensionIntegers l E) t •
          (restrictionTransition Y l E L ι F).app (op m) :=
  sheafAverage_comp Y (lisseIntegerInclusion l E L ι) hι _ _ _
    (restrictionUnitLevel Y l E L ι F hF m) _ _
    (restrictionUnitLevel_comp l Y E L ι F hF m) t ht

end AveragedRestriction

/-- A central integral tensor induces opposite maps with scalar composite. -/
theorem lisseIntegralRestriction_tensor_maps
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y
      (lisseIntegralRestrictionRaw l Y E L ι F)) :
    let R := Padic.coefficientExtensionIntegers l E
    let S := Padic.coefficientExtensionIntegers l L
    letI : Algebra R S := (lisseIntegerInclusion l E L ι).toAlgebra
    ∀ t : TensorProduct R S S,
      (∀ s : S, (TensorProduct.tmul R s 1 - TensorProduct.tmul R 1 s) * t = 0) →
      let G : LisseIntegralSheaf l E Y :=
        ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
      let H := (lisseIntegralScalarExtension l E Y L ι).obj G
      ∃ (i : F ⟶ H) (r : H ⟶ F),
        i ≫ r = Algebra.TensorProduct.lmul' R t • 𝟙 F := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let : Algebra R S := (lisseIntegerInclusion l E L ι).toAlgebra
  let G : LisseIntegralSheaf l E Y := ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
  let H := (lisseIntegralScalarExtension l E Y L ι).obj G
  change ∀ t : TensorProduct R S S,
    (∀ s : S, (s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s) * t = 0) →
    ∃ (i : F ⟶ H) (r : H ⟶ F), i ≫ r = Algebra.TensorProduct.lmul' R t • 𝟙 F
  intro t ht
  let δ := restrictionTransition Y l E L ι F
  let σ := restrictionAverage l Y E L ι rfl F hF t ht
  have (m : ℕᵒᵖ) : Epi (δ.app m) := integralTransition_epi Y l L F m.unop _
    (restrictionSource_le l E L ι m.unop)
  let τ := naturalEpiDesc δ σ (restrictionAverage_kernel l Y E L ι rfl F hF t ht)
  let i : F ⟶ H := ObjectProperty.homMk τ
  let r : H ⟶ F := ObjectProperty.homMk (NatTrans.ofOpSequence
    (restrictionMultiplicationLevel Y l E L ι F hF)
    (restrictionMultiplicationLevel_naturality Y l E L ι F hF))
  refine ⟨i, r, ?_⟩
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_epi (δ.app m)).mp
  change δ.app m ≫ (Abelian.epiDesc (δ.app m) (σ.app m)
    (restrictionAverage_kernel l Y E L ι rfl F hF t ht m) ≫
      restrictionMultiplicationLevel Y l E L ι F hF m.unop) =
    δ.app m ≫ (Algebra.TensorProduct.lmul' R t • 𝟙 (F.obj.obj m))
  rw [← Category.assoc, Abelian.comp_epiDesc]
  change restrictionAverageLevel l Y E L ι rfl F hF t ht m.unop ≫ _ = _
  rw [restrictionAverageLevel_comp]
  simp only [Linear.comp_smul, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme
