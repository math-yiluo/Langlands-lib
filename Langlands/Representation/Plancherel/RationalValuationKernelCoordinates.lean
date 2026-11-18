import Langlands.Representation.Plancherel.MaximalLeviValuationKernel
import Langlands.Representation.Plancherel.RationalImageLattice
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Integral coordinates adapted to an actual valuation kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.ValuationKernelCoordinates

section IntegerModules

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module.Free ℤ N] [Module.Finite ℤ N]

/-- A map to a finite free integer module has a complemented kernel. -/
theorem exists_isCompl_ker (f : M →ₗ[ℤ] N) :
    ∃ C : Submodule ℤ M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    f.range_rangeRestrict
  let pi : M →ₗ[ℤ] LinearMap.ker f :=
    (LinearMap.id - s.comp f.rangeRestrict).codRestrict (LinearMap.ker f) (by
      intro x
      change f (x - s (f.rangeRestrict x)) = 0
      rw [map_sub]
      have hx := congrArg (fun y : LinearMap.range f => (y : N))
        (LinearMap.congr_fun hs (f.rangeRestrict x))
      exact sub_eq_zero.mpr hx.symm)
  have hpi (x : LinearMap.ker f) : pi x = x := by
    apply Subtype.ext
    change x.val - s (f.rangeRestrict x) = x.val
    have hx : f.rangeRestrict x = 0 := by
      apply Subtype.ext
      exact x.property
    rw [hx, map_zero, sub_zero]
  exact ⟨LinearMap.ker pi, LinearMap.isCompl_of_proj hpi⟩

end IntegerModules

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The integer-linear form of the actual ambient valuation-image map. -/
def integerMap (f : H ⟶ G) :
    Additive (rationalDiscreteValuationImage H) →ₗ[ℤ]
      Additive (rationalDiscreteValuationImage G) :=
  (rationalValuationImageMap f).toAdditive.toIntLinearMap

/-- Its kernel has the same underlying elements as the actual multiplicative
valuation kernel. -/
def kernelEquiv (f : H ⟶ G) :
    LinearMap.ker (integerMap f) ≃+ Additive (rationalValuationImageMap f).ker where
  toFun x := Additive.ofMul ⟨x.val.toMul, x.property⟩
  invFun x := ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The actual valuation kernel is an integral direct summand whenever
the ambient group is connected reductive. -/
theorem actual_exists_isCompl_ker (f : H ⟶ G) (hG : IsConnectedReductive G) :
    ∃ C : Submodule ℤ (Additive (rationalDiscreteValuationImage H)),
      IsCompl (LinearMap.ker (integerMap f)) C := by
  have := (rationalReductiveImage_free_finite G hG).1
  have := (rationalReductiveImage_free_finite G hG).2
  exact exists_isCompl_ker (integerMap f)

/-- Cyclicity of the actual valuation kernel bounds its integral rank by one. -/
theorem kernel_finrank_le_one (f : H ⟶ G)
    (hcyc : IsCyclic (rationalValuationImageMap f).ker) :
    Module.finrank ℤ (LinearMap.ker (integerMap f)) ≤ 1 := by
  have := hcyc
  have : IsAddCyclic (LinearMap.ker (integerMap f)) :=
    isAddCyclic_of_injective (kernelEquiv f).toAddMonoidHom (kernelEquiv f).injective
  obtain ⟨x, hx⟩ :=
    isAddCyclic_iff_exists_zmultiples_eq_top.mp
      (inferInstance : IsAddCyclic (LinearMap.ker (integerMap f)))
  apply finrank_le_one x
  intro y
  have hy : y ∈ AddSubgroup.zmultiples x := hx ▸ AddSubgroup.mem_top y
  exact AddSubgroup.mem_zmultiples_iff.mp hy

/-- The finite free actual valuation lattice has product coordinates whose
first block is exactly the actual valuation kernel. -/
theorem exists_product_coordinates (f : H ⟶ G)
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H) :
    ∃ (n : ℕ)
      (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ]
        (Fin (Module.finrank ℤ (LinearMap.ker (integerMap f))) → ℤ) × (Fin n → ℤ)),
      ∀ x : Additive (rationalDiscreteValuationImage H),
        (e x).2 = 0 ↔ rationalValuationImageMap f x.toMul = 1 := by
  obtain ⟨C, hC⟩ := actual_exists_isCompl_ker f hG
  have := (rationalReductiveImage_free_finite H hH).1
  have := (rationalReductiveImage_free_finite H hH).2
  let bK := Module.finBasis ℤ (LinearMap.ker (integerMap f))
  let bC := Module.finBasis ℤ C
  let e := (Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    (bK.equivFun.prodCongr bC.equivFun)
  refine ⟨Module.finrank ℤ C, e, fun x => ?_⟩
  change (bC.equivFun ((Submodule.prodEquivOfIsCompl _ _ hC).symm x).2 = 0) ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  constructor
  · intro hx
    have he := (Submodule.prodEquivOfIsCompl _ _ hC).apply_symm_apply x
    rw [Submodule.coe_prodEquivOfIsCompl', hx, Submodule.coe_zero, add_zero] at he
    have hmem := ((Submodule.prodEquivOfIsCompl _ _ hC).symm x).1.property
    rw [he] at hmem
    exact hmem
  · intro hx
    have hmem : x ∈ LinearMap.ker (integerMap f) := hx
    have he := Submodule.prodEquivOfIsCompl_symm_apply_left
      (LinearMap.ker (integerMap f)) C hC ⟨x, hmem⟩
    exact congrArg Prod.snd he

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {P M : GroupScheme (Spec (CommRingCat.of F))}

/-- For an actual maximal proper Levi, the kernel block in integral product
coordinates has zero or one coordinate. -/
theorem exists_maximalLevi_product_coordinates
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hproper : ¬ IsIso p)
    (hmax : ∀ (Q : GroupScheme (Spec (CommRingCat.of F))) (q : Q ⟶ G) (j : P ⟶ Q),
      IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q)
    (ha : IsSplitComponent a) :
    ∃ (r n : ℕ), r ≤ 1 ∧
      ∃ e : Additive (rationalDiscreteValuationImage M) ≃ₗ[ℤ]
        (Fin r → ℤ) × (Fin n → ℤ),
        ∀ x : Additive (rationalDiscreteValuationImage M),
          (e x).2 = 0 ↔ rationalValuationImageMap (l ≫ p) x.toMul = 1 := by
  obtain ⟨n, e, he⟩ := exists_product_coordinates (l ≫ p) hG hl.isConnectedReductive
  exact ⟨_, n, kernel_finrank_le_one (l ≫ p)
    (maximalLevi_rationalValuationKernel_isCyclic hG hp hl hproper hmax ha), e, he⟩

end Langlands.Plancherel.ValuationKernelCoordinates
