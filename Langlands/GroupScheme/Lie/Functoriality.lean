import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Rational.SplitTorusFiniteRank

/-! # Actual Lie-kernel maps induced by group-scheme morphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} {H G K : GroupScheme (Spec R)}
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

@[simp] theorem lieKernelHom_val (f : H ⟶ G) (x : lieKernel H A) :
    (Lie.targetMap f _ x).val = x.val ≫ f.hom.hom := rfl

theorem lieKernelHom_injective (f : H ⟶ G) [Mono f.hom.hom] :
    Function.Injective (Lie.targetMap f A) := by
  intro x y h
  apply Subtype.ext
  exact (cancel_mono f.hom.hom).mp (congrArg Subtype.val h)

/-- Postcomposition commutes with coefficient change on actual Lie kernels. -/
theorem lieKernelHom_map (f : H ⟶ G) (a : A →ₐ[R] B) (x : lieKernel H A) :
    Lie.targetMap f _ (lieKernelMap H a x) =
      lieKernelMap G a (Lie.targetMap f _ x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- Postcomposition commutes with epsilon scaling. -/
theorem lieKernelHom_scale (f : H ⟶ G) (c : A) (x : lieKernel H A) :
    Lie.targetMap f _ (lieKernelScale H c x) =
      lieKernelScale G c (Lie.targetMap f _ x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

variable [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

@[simp] theorem lieKernelHomLinear_val (f : H ⟶ G) (x : Additive (lieKernel H A)) :
    (Lie.targetMapLinear f _ x).toMul.val = x.toMul.val ≫ f.hom.hom := rfl

/-- The differential commutes with linear coefficient change. -/
theorem lieKernelHomLinear_map (f : H ⟶ G) (a : A →ₐ[R] B)
    (x : Additive (lieKernel H A)) :
    Lie.targetMapLinear f _ (lieKernelMapLinear H a x) =
      lieKernelMapLinear G a (Lie.targetMapLinear f _ x) :=
  congrArg Additive.ofMul (lieKernelHom_map f a x.toMul)

/-- The differential intertwines the adjoint actions on actual kernels. -/
theorem lieKernelHomLinear_adjoint (f : H ⟶ G) (h : Lie.AffinePoints H A)
    (x : Additive (lieKernel H A)) :
    Lie.targetMapLinear f _ (adjoint H A h x) =
      adjoint G A (h ≫ f.hom.hom) (Lie.targetMapLinear f _ x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [lieKernelHomLinear_val, adjoint_val, MonObj.mul_comp,
    GrpObj.inv_comp]
  rfl

variable {T : CommGroupScheme (Spec R)}

/-- Every character weight maps to the same weight after postcomposition. -/
theorem lieKernelHomLinear_mem_weightSpace (f : H ⟶ G) (i : T.toGrp ⟶ H)
    (α : characterLattice T) {x : Additive (lieKernel H R)}
    (hx : x ∈ weightSpace i α) :
    Lie.targetMapLinear f _ x ∈ weightSpace (i ≫ f) α := by
  intro A _ _ t
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [← lieKernelHomLinear_map, ← lieKernelHomLinear_adjoint]
  simpa only [LinearMap.map_smul] using congrArg (Lie.targetMapLinear f _) (hx A t)

/-- A monomorphism reflects membership in every actual character weight space. -/
theorem lieKernelHomLinear_mem_weightSpace_iff (f : H ⟶ G) [Mono f.hom.hom]
    (i : T.toGrp ⟶ H) (α : characterLattice T) (x : Additive (lieKernel H R)) :
    Lie.targetMapLinear f _ x ∈ weightSpace (i ≫ f) α ↔ x ∈ weightSpace i α := by
  constructor
  · intro hx A _ _ t
    apply Lie.targetMapLinear_injective f _
    rw [lieKernelHomLinear_adjoint, LinearMap.map_smul, lieKernelHomLinear_map]
    exact hx A t
  · exact lieKernelHomLinear_mem_weightSpace f i α

/-- Roots of a subgroup with monomorphic inclusion are ambient roots. -/
theorem roots_subset_comp (f : H ⟶ G) [Mono f.hom.hom] (i : T.toGrp ⟶ H) :
    roots i ⊆ roots (i ≫ f) := by
  intro α hα
  refine ⟨hα.1, ?_⟩
  intro hbot
  apply hα.2
  apply eq_bot_iff.mpr
  intro x hx
  have h := lieKernelHomLinear_mem_weightSpace f i α hx
  rw [hbot, Submodule.mem_bot] at h
  exact (Lie.targetMapLinear_injective f _).eq_iff.mp (h.trans (map_zero _).symm)

end Langlands.GroupScheme
