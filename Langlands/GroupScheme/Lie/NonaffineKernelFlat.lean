import Langlands.GroupScheme.Lie.NonaffineKernelMap
import Langlands.AlgebraicGeometry.SmoothLifting.FlatBaseChange

/-! # Flat base change of square-zero reduction kernels

For a smooth group scheme `G` over `Spec R` (not assumed affine), a square-zero ideal `I` of `R`
and a flat `R`-algebra `B`, the kernel of `G(B) → G(B ⧸ I B)` is the base change of the kernel of
`G(R) → G(R ⧸ I)`: `b ⊗ x ↦ b • x|_B` is a `B`-linear isomorphism, natural in `B`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie.NonaffineKernel

open Langlands.AlgebraicGeometry.SmoothLifting

/-- Extensions of square-zero ideals are square-zero. -/
instance fact_sqZero_map {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] (J : Ideal A)
    [h : Fact (SqZero J)] : Fact (SqZero (J.map (algebraMap A A'))) :=
  ⟨h.out.map _⟩

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) (I : Ideal R)
  (B : Type u) [CommRing B] [Algebra R B]

/-- The identity modulo `I B` is the restriction of the identity modulo `I`. -/
theorem redStruct_unit₀ :
    Spec.map (redStruct I B) ≫ unit₀ G I = unit₀ G (I.map (algebraMap R B)) := by
  change (affineMap G (Ideal.quotientMapₐ (I.map (algebraMap R B)) (Algebra.ofId R B)
    Ideal.le_comap_map) (1 : AffinePoints G (R ⧸ I))).left = _
  rw [map_one]

theorem strMap_str : Spec.map (strMap (C := CommRingCat.of R) B) ≫ str (R := R) R = str B := by
  rw [str, ← Spec.map_comp]
  rfl

/-- Lifts of the identity on `B` for the kernel data and for the base-changed data agree. -/
theorem isGlobalLift_kernel_iff (y : Spec (CommRingCat.of B) ⟶ G.X.left) :
    IsGlobalLift (C := CommRingCat.of B) G.X.hom (I.map (algebraMap R B))
      (unit₀ G (I.map (algebraMap R B))) (str B) y ↔
      IsGlobalLift G.X.hom (bcI (I := I) B) (bcx₀ (unit₀ G I) B) (bcs (str (R := R) R) B) y := by
  change _ ↔ (_ = Spec.map (redStruct I B) ≫ unit₀ G I ∧
    _ = Spec.map (strMap (C := CommRingCat.of R) B) ≫ str (R := R) R)
  rw [redStruct_unit₀, strMap_str]
  rfl

theorem base_res : (base G (I.map (algebraMap R B))).1 = (GLift.res B (base G I)).1 := by
  change (1 : AffinePoints G B).left =
    Spec.map (CommRingCat.ofHom (Algebra.ofId R B).toRingHom) ≫ (1 : AffinePoints G R).left
  exact (congrArg (fun z => z.left) (map_one (affineMap G (Algebra.ofId R B)))).symm

theorem map_le_extended : I.map (Algebra.ofId R B) ≤ I.map (algebraMap R B) :=
  Ideal.map_le_iff_le_comap.mpr fun _ hx => Ideal.mem_map_of_mem (algebraMap R B) hx

/-- Restriction of kernel points from `R` to `B`. -/
abbrev kernelBcMap : Additive (kernel G I) →+ Additive (kernel G (I.map (algebraMap R B))) :=
  kernelMapAdd G I (Algebra.ofId R B) (map_le_extended I B)

variable [hI : Fact (SqZero I)]

/-- Lifts of the identity on `B` for the kernel data and the base-changed data. -/
def liftBcEquiv : LiftModule (Fact.out : SqZero (I.map (algebraMap R B)))
      (base G (I.map (algebraMap R B))) ≃ₗ[B]
    LiftModule (hI.out.map (algebraMap (CommRingCat.of R) B)) (GLift.res B (base G I)) :=
  LiftModule.equivOfIff _ _ _ _ (isGlobalLift_kernel_iff G I B) (base_res G I B)

variable [Smooth G.X.hom] [Module.Flat R B]

/-- The comparison `B ⊗[R] K_R ≃ K_B` of reduction kernels, `b ⊗ x ↦ b • x|_B`. -/
def flatKernelEquivSymm :
    B ⊗[R] Additive (kernel G I) ≃ₗ[B] Additive (kernel G (I.map (algebraMap R B))) :=
  ((toLMEquiv G I).baseChange R B _ _).trans
    (((LiftModule.isBaseChange_resLin hI.out (base G I) B).equiv.trans
      (liftBcEquiv G I B).symm).trans (toLMEquiv G (I.map (algebraMap R B))).symm)

theorem flatKernelEquivSymm_one_tmul (x : Additive (kernel G I)) :
    flatKernelEquivSymm G I B (1 ⊗ₜ x) = kernelBcMap G I B x := by
  apply (toLMEquiv G (I.map (algebraMap R B))).injective
  simp only [flatKernelEquivSymm, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply]
  rw [IsBaseChange.equiv_tmul, one_smul]
  apply Subtype.ext
  rfl

theorem flatKernelEquivSymm_tmul (b : B) (x : Additive (kernel G I)) :
    flatKernelEquivSymm G I B (b ⊗ₜ x) = b • kernelBcMap G I B x := by
  rw [show b ⊗ₜ[R] x = b • ((1 : B) ⊗ₜ[R] x) by rw [TensorProduct.smul_tmul', smul_eq_mul,
    mul_one], map_smul, flatKernelEquivSymm_one_tmul]

/-- **Flat base change of square-zero reduction kernels**:
`K_B ≃ₗ[B] B ⊗[R] K_R`, inverse to `b ⊗ x ↦ b • x|_B`. -/
def flatKernelEquiv :
    Additive (kernel G (I.map (algebraMap R B))) ≃ₗ[B] B ⊗[R] Additive (kernel G I) :=
  (flatKernelEquivSymm G I B).symm

theorem flatKernelEquiv_symm_tmul (b : B) (x : Additive (kernel G I)) :
    (flatKernelEquiv G I B).symm (b ⊗ₜ x) = b • kernelBcMap G I B x :=
  flatKernelEquivSymm_tmul G I B b x

theorem flatKernelEquiv_kernelBcMap (x : Additive (kernel G I)) :
    flatKernelEquiv G I B (kernelBcMap G I B x) = 1 ⊗ₜ x := by
  rw [flatKernelEquiv, LinearEquiv.symm_apply_eq, flatKernelEquivSymm_one_tmul]

section Naturality

variable {B} {B' : Type u} [CommRing B'] [Algebra R B'] [Module.Flat R B'] (φ : B →ₐ[R] B')

omit hI [Module.Flat R B] [Module.Flat R B'] in
theorem map_le_map_extended :
    (I.map (algebraMap R B)).map φ ≤ I.map (algebraMap R B') := by
  rw [show (I.map (algebraMap R B)).map φ = (I.map (algebraMap R B)).map (φ : B →+* B') from rfl,
    Ideal.map_map, φ.comp_algebraMap]

omit hI [Smooth G.X.hom] [Module.Flat R B] [Module.Flat R B'] in
/-- Restriction from `B` to `B'` after restriction from `R` to `B` is restriction from `R`. -/
theorem kernelMapAdd_kernelBcMap (x : Additive (kernel G I)) :
    kernelMapAdd G (I.map (algebraMap R B)) φ (map_le_map_extended I φ) (kernelBcMap G I B x) =
      kernelBcMap G I B' x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change affineMap G φ (affineMap G (Algebra.ofId R B) x.toMul.1) =
    affineMap G (Algebra.ofId R B') x.toMul.1
  rw [← affineMap_comp, show φ.comp (Algebra.ofId R B) = Algebra.ofId R B' from
    AlgHom.ext fun _ => φ.commutes _]

/-- **Naturality** of the flat base change comparison in the flat algebra. -/
theorem flatKernelEquiv_naturality (y : Additive (kernel G (I.map (algebraMap R B)))) :
    flatKernelEquiv G I B' (kernelMapAdd G (I.map (algebraMap R B)) φ
        (map_le_map_extended I φ) y) =
      LinearMap.rTensor (Additive (kernel G I)) φ.toLinearMap (flatKernelEquiv G I B y) := by
  obtain ⟨t, rfl⟩ := (flatKernelEquiv G I B).symm.surjective y
  rw [LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul b x =>
    rw [flatKernelEquiv_symm_tmul, kernelMap_smul, kernelMapAdd_kernelBcMap, map_smul,
      flatKernelEquiv_kernelBcMap, LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    rfl
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

end Naturality

end Langlands.GroupScheme.Lie.NonaffineKernel
