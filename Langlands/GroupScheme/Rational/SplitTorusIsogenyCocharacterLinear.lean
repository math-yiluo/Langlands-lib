import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacter
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.SplitTorusIsogeny

section Linear

variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]

/-- A left inverse up to a nonzero integer gives injectivity on a torsion-free module. -/
theorem injective_of_left_quasiInverse [Module.IsTorsionFree ℤ M]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] M) (n : ℤ) (hn : n ≠ 0)
    (h : g ∘ₗ f = n • LinearMap.id) : Function.Injective f := by
  intro x y hxy
  apply smul_right_injective M hn
  change n • x = n • y
  have hcomp (z : M) : g (f z) = n • z := LinearMap.congr_fun h z
  rw [← hcomp x, ← hcomp y, hxy]

/-- A right inverse up to a nonzero integer makes a finitely generated integral cokernel finite. -/
theorem finite_cokernel_of_right_quasiInverse [Module.Finite ℤ N]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] M) (n : ℤ) (hn : n ≠ 0)
    (h : f ∘ₗ g = n • LinearMap.id) : Finite (N ⧸ LinearMap.range f) := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, ?_⟩
  obtain ⟨y, rfl⟩ := (LinearMap.range f).mkQ_surjective x
  change (LinearMap.range f).mkQ (n • y) = 0
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr
  exact ⟨g y, LinearMap.congr_fun h y⟩

/-- A two-sided inverse up to a nonzero integer becomes an inverse over any characteristic-zero field. -/
theorem baseChange_bijective_of_quasiInverse (K : Type*) [Field K] [CharZero K]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] M) (n : ℤ) (hn : n ≠ 0)
    (hM : g ∘ₗ f = n • LinearMap.id) (hN : f ∘ₗ g = n • LinearMap.id) :
    Function.Bijective (f.baseChange K) := by
  have hnK : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hM' : (g.baseChange K) ∘ₗ (f.baseChange K) = n • LinearMap.id := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_smul,
      LinearMap.baseChange_id] using congrArg (fun l => l.baseChange K) hM
  have hN' : (f.baseChange K) ∘ₗ (g.baseChange K) = n • LinearMap.id := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_smul,
      LinearMap.baseChange_id] using congrArg (fun l => l.baseChange K) hN
  have hMx (x : K ⊗[ℤ] M) : g.baseChange K (f.baseChange K x) = (n : K) • x := by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Int.cast_smul_eq_zsmul] using LinearMap.congr_fun hM' x
  have hNy (y : K ⊗[ℤ] N) : f.baseChange K (g.baseChange K y) = (n : K) • y := by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Int.cast_smul_eq_zsmul] using LinearMap.congr_fun hN' y
  constructor
  · intro x y hxy
    apply smul_right_injective (K ⊗[ℤ] M) hnK
    change (n : K) • x = (n : K) • y
    rw [← hMx x, ← hMx y, hxy]
  · intro y
    refine ⟨(n : K)⁻¹ • g.baseChange K y, ?_⟩
    rw [map_smul, hNy, smul_smul, inv_mul_cancel₀ hnK, one_smul]

/-- The scalar-extension equivalence carried by a linear map with an integer quasiinverse. -/
def scalarExtensionEquivOfQuasiInverse (K : Type*) [Field K] [CharZero K]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] M) (n : ℤ) (hn : n ≠ 0)
    (hM : g ∘ₗ f = n • LinearMap.id) (hN : f ∘ₗ g = n • LinearMap.id) :
    (K ⊗[ℤ] M) ≃ₗ[K] (K ⊗[ℤ] N) :=
  LinearEquiv.ofBijective (f.baseChange K)
    (baseChange_bijective_of_quasiInverse K f g n hn hM hN)

@[simp] theorem scalarExtensionEquivOfQuasiInverse_apply
    (K : Type*) [Field K] [CharZero K]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] M) (n : ℤ) (hn : n ≠ 0)
    (hM : g ∘ₗ f = n • LinearMap.id) (hN : f ∘ₗ g = n • LinearMap.id)
    (x : K ⊗[ℤ] M) :
    scalarExtensionEquivOfQuasiInverse K f g n hn hM hN x = f.baseChange K x := rfl

end Linear

end Langlands.GroupScheme.SplitTorusIsogeny

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual cocharacter lattice of a split torus has finite coordinate rank. -/
theorem IsSplitTorus.exists_cocharacterCoordinates (hT : IsSplitTorus T.toGrp) :
    ∃ (I : Type u) (_ : Finite I), Nonempty (cocharacterLattice T ≃ₗ[ℤ] (I → ℤ)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact ⟨I, hI, ⟨((cocharacterLattice.congr eC).trans
    (splitTorus.cocharacterLatticeEquiv k I)).toIntLinearEquiv⟩⟩

/-- The actual integral cocharacter lattice of a split torus is finitely generated. -/
theorem IsSplitTorus.finite_cocharacterLattice (hT : IsSplitTorus T.toGrp) :
    Module.Finite ℤ (cocharacterLattice T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT.exists_cocharacterCoordinates
  let := hI
  exact Module.Finite.equiv e.symm

/-- The actual integral cocharacter lattice of a split torus is torsion-free. -/
theorem IsSplitTorus.torsionFree_cocharacterLattice (hT : IsSplitTorus T.toGrp) :
    Module.IsTorsionFree ℤ (cocharacterLattice T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT.exists_cocharacterCoordinates
  exact e.injective.moduleIsTorsionFree e (fun n x => e.map_smul n x)

namespace SplitTorusIsogeny

/-- A reverse torus homomorphism up to multiplication gives all four actual cocharacter conclusions. -/
theorem cocharacter_isogeny_conclusions_of_quasiInverse
    (f : A ⟶ T) (g : T ⟶ A) (n : ℤ) (hn : n ≠ 0)
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hfg : f ≫ g = n • 𝟙 A) (hgf : g ≫ f = n • 𝟙 T) :
    Function.Injective (RealTorusSpace.cocharacterMapInt f) ∧
      Finite (cocharacterLattice T ⧸ LinearMap.range (RealTorusSpace.cocharacterMapInt f)) ∧
      Function.Bijective ((RealTorusSpace.cocharacterMapInt f).baseChange ℚ) ∧
      Function.Bijective (RealTorusSpace.cocharacterMapReal f) := by
  have := hA.torsionFree_cocharacterLattice
  have := hT.finite_cocharacterLattice
  have hM : RealTorusSpace.cocharacterMapInt g ∘ₗ RealTorusSpace.cocharacterMapInt f =
      n • LinearMap.id := by
    ext ν
    change (ν ≫ f) ≫ g = n • ν
    rw [Category.assoc, hfg, Preadditive.comp_zsmul, Category.comp_id]
  have hN : RealTorusSpace.cocharacterMapInt f ∘ₗ RealTorusSpace.cocharacterMapInt g =
      n • LinearMap.id := by
    ext ν
    change (ν ≫ g) ≫ f = n • ν
    rw [Category.assoc, hgf, Preadditive.comp_zsmul, Category.comp_id]
  exact ⟨injective_of_left_quasiInverse _ _ n hn hM,
    finite_cokernel_of_right_quasiInverse _ _ n hn hN,
    baseChange_bijective_of_quasiInverse ℚ _ _ n hn hM hN,
    baseChange_bijective_of_quasiInverse ℝ _ _ n hn hM hN⟩

end SplitTorusIsogeny

end Langlands.GroupScheme
