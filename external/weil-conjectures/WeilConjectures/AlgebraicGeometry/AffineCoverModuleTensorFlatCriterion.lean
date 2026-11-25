/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.AffinePullbackChartTensorFlatStalks
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks

/-! # Tensor flatness on a specified affine cover

Source: Stacks Project, Morphisms, Tag 01U4; Algebra, Tag 00HT;
Limits, Tag 05LY, affine-local reduction.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Cancel the redundant right unit before comparing the affine chart with its stalks. -/
private theorem flat_tensor_right_unit_iff
    (A T : Type u) [CommRing A] [CommRing T] [Algebra A T]
    (N : Type u) [AddCommGroup N] [Module A N] :
    letI : Algebra A (T ⊗[A] A) := Algebra.TensorProduct.rightAlgebra
    letI : Module A (T ⊗[A] A) := Algebra.toModule
    Module.Flat (T ⊗[A] A) ((T ⊗[A] A) ⊗[A] N) ↔
      Module.Flat T (T ⊗[A] N) := by
  let D := T ⊗[A] A
  let : Algebra A D := Algebra.TensorProduct.rightAlgebra
  let : Module A D := Algebra.toModule
  let : SMul A D := (inferInstance : Module A D).toSMul
  have : IsScalarTower A T D := by
    apply IsScalarTower.of_algebraMap_smul
    intro a d
    induction d using TensorProduct.inductionOn with
    | tmul t r =>
      rw [TensorProduct.smul_tmul']
      change (algebraMap A T a * t) ⊗ₜ[A] r =
        ((1 : T) ⊗ₜ[A] a) * (t ⊗ₜ[A] r)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simpa [Algebra.smul_def] using TensorProduct.smul_tmul a t r
    | add d d' hd hd' =>
      rw [smul_add, hd, hd']
      change algebraMap A D a * d + algebraMap A D a * d' =
        algebraMap A D a * (d + d')
      exact (mul_add _ _ _).symm
  let e := Algebra.TensorProduct.rid A T T
  have : IsLocalization (⊥ : Submonoid T) D := by
    apply IsLocalization.of_le_isUnit_of_bijective
    · intro t ht
      obtain ⟨r, hr, rfl⟩ := ht
      have hr : r = 1 := by simpa using hr
      simp [hr]
    · exact e.symm.bijective
  have : IsScalarTower T D (D ⊗[A] N) := inferInstance
  let E : (D ⊗[A] N) ≃ₗ[T] (T ⊗[A] N) :=
    TensorProduct.AlgebraTensorModule.congr e.toLinearEquiv (LinearEquiv.refl A N)
  exact (Module.flat_iff_of_isLocalization D (⊥ : Submonoid T) (D ⊗[A] N)).trans
    (Module.Flat.equiv_iff E)

/-- Flatness after an affine base change is equivalent to tensor flatness of the actual
section modules on a specified affine covering. No finiteness or descent is asserted.
Source: Stacks Project, Morphisms, Tag 01U4; Algebra, Tag 00HT; Limits, Tag 05LY.
(blueprint: lem-pc-affine-cover-module-tensor-flat-criterion).

Proof: Each inverse image of U_b in the fibre product is affine: identify U_b with
Spec of its section ring and use the spectrum tensor-product pullback formula. The
quasi-coherent pullback has sections T tensor_A Gamma(M,U_b), compatibly with the
map to Spec T. The multiplication map T tensor_A A -> T and t -> t tensor 1 are
inverse ring maps. Their induced module isomorphism identifies the tensor module
in the statement with those sections, respecting the base action. The isomorphism
e identifies the arbitrary affine base Y with Spec T over Spec A, so the same
comparisons apply to the chosen pullback along p. Flatness over Y implies flatness
of these sections by the affine-section criterion (01U4). Conversely, tensor
flatness gives flatness of each chart's sections over T, hence flatness of every
module stalk over the corresponding base local ring, by localization. The inverse
images of the U_b cover the fibre product, so all its relative stalks are flat.
Quasi-coherence and the prime-local flatness criterion (00HT) then imply flatness
of sections on any affine source open over any affine base open, which is exactly
IsFlatOver. An empty covering forces X empty; all pulled-back sections are zero.
The zero ring and zero modules satisfy the same tensor and localization formulas. -/
theorem affine_cover_module_tensor_flat_criterion
    (A T : CommRingCat.{u}) {X Y : Scheme.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) [M.IsQuasicoherent]
    {n : ℕ} (U : Fin n → X.affineOpens) (hcover : ∀ x : X, ∃ b, x ∈ (U b).1)
    (q : A ⟶ T) (p : Y ⟶ Spec A) (e : Y ≅ Spec T)
    (he : e.hom ≫ Spec.map q = p) :
    let a := fun b ↦ ((Scheme.ΓSpecIso A).inv ≫
      f.appLE ⊤ (U b).1 (by simp)).hom
    Scheme.Modules.IsFlatOver
      ((Scheme.Modules.tensorPullback (pullback.fst f p)).obj M) (pullback.snd f p) ↔
    (∀ b, letI : Module (A : Type u) Γ(M, (U b).1) := Module.compHom _ (a b)
      letI : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
      letI : Algebra (A : Type u) ((T : Type u) ⊗[(A : Type u)] (A : Type u)) :=
        Algebra.TensorProduct.rightAlgebra
      letI : Module (A : Type u) ((T : Type u) ⊗[(A : Type u)] (A : Type u)) :=
        Algebra.toModule
      Module.Flat ((T : Type u) ⊗[(A : Type u)] (A : Type u))
        (((T : Type u) ⊗[(A : Type u)] (A : Type u)) ⊗[(A : Type u)] Γ(M, (U b).1))) := by
  classical
  dsimp only
  let a := pullback.fst f p
  let b := pullback.snd f p
  let G := (Scheme.Modules.tensorPullback a).obj M
  let E := (Scheme.Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction a)
  have : G.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f p).ringCatSheaf).prop_of_iso
      (E.app M).symm (Scheme.Modules.isQuasicoherent_pullback a M)
  constructor
  · intro hflat i
    let : Module (A : Type u) Γ(M, (U i).1) := Module.compHom _
      (((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ (U i).1 (by simp)).hom)
    let : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
    apply (flat_tensor_right_unit_iff (A : Type u) (T : Type u) Γ(M, (U i).1)).mpr
    apply (affine_pullback_chart_tensor_flat_iff_stalks A T f M (U i) q p e he).mpr
    intro z _
    let := (b.stalkMap z).hom.toAlgebra
    exact relative_flat_module_stalk b G hflat z rfl
  · intro hflat
    apply relative_flat_of_stalks b G
    intro z
    obtain ⟨i, hi⟩ := hcover (a z)
    let : Module (A : Type u) Γ(M, (U i).1) := Module.compHom _
      (((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ (U i).1 (by simp)).hom)
    let : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
    have ht : Module.Flat (T : Type u) ((T : Type u) ⊗[(A : Type u)] Γ(M, (U i).1)) :=
      (flat_tensor_right_unit_iff (A : Type u) (T : Type u) Γ(M, (U i).1)).mp (hflat i)
    exact (affine_pullback_chart_tensor_flat_iff_stalks A T f M (U i) q p e he).mp ht z hi

end AlgebraicGeometry
