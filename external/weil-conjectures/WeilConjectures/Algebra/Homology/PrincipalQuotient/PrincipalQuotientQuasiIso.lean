/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Principal quotient preserves quasi-isomorphisms on regular complexes

Source: Stacks Project, Derived Categories, Tag 05RT; steps 4--7 of the original plan.
(blueprint: lem-pod-principal-quotient-quasi-iso) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace CochainComplex.PrincipalQuotient
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) (t : R)
  (hf : Function.Surjective f) (hk : ∀ x : R, f x = 0 ↔ ∃ y : R, t * y = x)

private def unit (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    C ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj C) where
  f i := (ModuleCat.extendRestrictScalarsAdj f).unit.app (C.X i)
  comm' i j _ := (ModuleCat.extendRestrictScalarsAdj f).unit.naturality (C.d i j)

include hf

private theorem unit_surjective (M : ModuleCat.{u} R) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) := by
  let := f.toAlgebra
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, TensorProduct.tmul_add _ _ _⟩
  | tmul a x =>
    obtain ⟨b, rfl⟩ := hf a
    refine ⟨b • x, ?_⟩
    rw [show ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) (b • x) =
      (1 : A) ⊗ₜ[R] (b • x) from rfl, TensorProduct.tmul_smul]
    change (f b * 1) ⊗ₜ[R] x = _
    rw [mul_one]

include hk

private theorem unit_kernel (M : ModuleCat.{u} R) (x : M) :
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) x = 0 ↔
      ∃ y : M, t • y = x := by
  let := f.toAlgebra
  let μ : R →ₗ[R] R := LinearMap.lsmul R R t
  let π : R →ₗ[R] A := Algebra.linearMap R A
  have hπ : Function.Exact μ π := by
    intro a
    exact hk a
  have hT := rTensor_exact M hπ hf
  have hμ (z : R ⊗[R] M) :
      TensorProduct.lid R M (LinearMap.rTensor M μ z) = t • TensorProduct.lid R M z := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp [hz, hw, smul_add]
    | tmul a m => simp [μ, smul_smul]
  constructor
  · intro hx
    change (1 : A) ⊗ₜ[R] x = 0 at hx
    have hzero : LinearMap.rTensor M π ((1 : R) ⊗ₜ[R] x) = 0 := by
      simpa [π] using hx
    obtain ⟨z, hz⟩ := (hT ((1 : R) ⊗ₜ[R] x)).1 hzero
    refine ⟨TensorProduct.lid R M z, (hμ z).symm.trans ?_⟩
    rw [hz]
    simp
  · rintro ⟨y, rfl⟩
    change (1 : A) ⊗ₜ[R] (t • y) = 0
    rw [TensorProduct.tmul_smul]
    change (f t * 1) ⊗ₜ[R] y = 0
    rw [(hk t).2 ⟨1, mul_one _⟩, zero_mul, TensorProduct.zero_tmul]

private def sequence (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (t • 𝟙 C) (unit f C) (by
    ext i x
    change ((ModuleCat.extendRestrictScalarsAdj f).unit.app (C.X i)) (t • x) = 0
    exact (unit_kernel f t hf hk (C.X i) (t • x)).2 ⟨x, rfl⟩)

private theorem sequence_shortExact (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ∀ i : ℤ, Function.Injective (fun x : C.X i ↦ t • x)) :
    (sequence f t hf hk C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro x hx
    exact (unit_kernel f t hf hk (C.X i) x).1 hx
  · exact (ModuleCat.mono_iff_injective _).2 (h i)
  · exact (ModuleCat.epi_iff_surjective _).2 (unit_surjective f hf (C.X i))

/-- A principal quotient preserves quasi-isomorphisms between termwise t-regular complexes.
No boundedness or K-flatness is used, and the quotient ring may be any specified presentation.

Proof: right exactness of tensor gives kernel tM for the surjection M to A tensor M.
The unit maps give short exact sequences C --t--> C → C/tC and D --t--> D → D/tD.
Naturality gives a map between them with the original quasi-isomorphism on the first two
terms. The homology long exact sequence makes the third map a quasi-isomorphism, and
faithful restriction of scalars reflects that property.
Source: Stacks Tag 05RT; blueprint steps 5--7.
(blueprint: lem-pod-principal-quotient-quasi-iso) -/
theorem quasiIso_map {C D : CochainComplex (ModuleCat.{u} R) ℤ} (g : C ⟶ D)
    (hg : QuasiIso g)
    (hC : ∀ i : ℤ, Function.Injective (fun x : C.X i ↦ t • x))
    (hD : ∀ i : ℤ, Function.Injective (fun x : D.X i ↦ t • x)) :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map g) := by
  let g' := ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g
  let S := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
  let φ : sequence f t hf hk C ⟶ sequence f t hf hk D :=
    { τ₁ := g
      τ₂ := g
      τ₃ := S.map g'
      comm₁₂ := by simp [sequence]
      comm₂₃ := by
        ext i : 1
        exact (ModuleCat.extendRestrictScalarsAdj f).unit.naturality (g.f i) }
  have hg' : QuasiIso (S.map g') :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
      (sequence_shortExact f t hf hk C hC) (sequence_shortExact f t hf hk D hD) hg hg
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology g'
    (ModuleCat.restrictScalars f)).1 hg'

end CochainComplex.PrincipalQuotient
