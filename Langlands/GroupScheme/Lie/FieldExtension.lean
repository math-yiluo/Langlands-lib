import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Mathlib.RingTheory.Flat.Basic

/-! # Field extension of actual Lie-kernel witnesses -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Lie

section Ring

variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]

local notation "b" => algebraBaseMap k K

/-- Extend the coefficients of an actual tangent point and regard it as a point of
the scheme pullback. No affineness hypothesis is needed for this map. -/
def kernelFieldExtension (G : GroupScheme (Spec (CommRingCat.of k))) :
    lieKernel G k →* lieKernel ((GroupScheme.baseChange b).obj G) K :=
  (kernelBaseChangeEquiv k K G K).symm.toMonoidHom.comp
    (lieKernelMap G (Algebra.ofId k K))

variable {H G : GroupScheme (Spec (CommRingCat.of k))}
  (i : H ⟶ G) {A : Type u} [CommRing A] [Algebra k A] [Algebra K A]
  [IsScalarTower k K A]

/-- The scheme-pullback kernel comparison commutes with group homomorphisms. -/
theorem kernelBaseChangeEquiv_target
    (x : lieKernel ((GroupScheme.baseChange b).obj H) A) :
    kernelBaseChangeEquiv k K G A
        (targetMap ((GroupScheme.baseChange b).map i) A x) =
      targetMap i A (kernelBaseChangeEquiv k K H A x) := by
  apply Subtype.ext
  exact affineBaseChangeEquiv_target k K i x.val

/-- Coefficient extension of actual tangent points commutes with postcomposition. -/
theorem kernelFieldExtension_target (x : lieKernel H k) :
    kernelFieldExtension (K := K) G (targetMap i k x) =
      targetMap ((GroupScheme.baseChange b).map i) K
        (kernelFieldExtension (K := K) H x) := by
  apply (kernelBaseChangeEquiv k K G K).injective
  rw [kernelBaseChangeEquiv_target]
  change kernelBaseChangeEquiv k K G K
      ((kernelBaseChangeEquiv k K G K).symm _) =
    targetMap i K (kernelBaseChangeEquiv k K H K
      ((kernelBaseChangeEquiv k K H K).symm _))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact lieKernelMap_target i (Algebra.ofId k K) x

end Ring

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance fieldExtensionLocalInstance1 : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Extending an actual tangent point agrees with extension of its vector by
`1 ⊗ x` through the published scalar-extension equivalence. -/
theorem schemeScalarExtension_one_tmul (x : Additive (lieKernel G k)) :
    schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) =
      Additive.ofMul (kernelFieldExtension (K := K) G x.toMul) := by
  rw [schemeScalarExtension_tmul, one_smul]
  rfl

/-- A field extension does not identify distinct actual tangent points. -/
theorem kernelFieldExtension_injective :
    Function.Injective (kernelFieldExtension (K := K) G) := by
  intro x y h
  have ht : (1 : K) ⊗ₜ[k] Additive.ofMul x =
      (1 : K) ⊗ₜ[k] Additive.ofMul y := by
    apply (schemeScalarExtension (K := K) G).injective
    simpa only [schemeScalarExtension_one_tmul, toMul_ofMul] using congrArg Additive.ofMul h
  have he := Module.Flat.tensorProduct_mk_injective
    (R := k) (S := K) (M := Additive (lieKernel G k)) ht
  exact Additive.ofMul.injective he

end Field

end Lie

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K

local instance fieldExtensionLocalInstance2 : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- A nonzero weight vector in the actual Lie-image of a subgroup retains both
properties after an arbitrary field extension. The subgroup need not be affine. -/
theorem weightSpace_lieImage_baseChange
    (j : T.toGrp ⟶ G) (α : characterLattice T)
    {H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
    (h : ∃ X ∈ weightSpace j α, X ≠ 0 ∧
      ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val) :
    ∃ X ∈ weightSpace ((GroupScheme.baseChange b).map j)
        (characterLattice.baseChange b T α), X ≠ 0 ∧
      ∃ Y : lieKernel ((GroupScheme.baseChange b).obj H) K,
        Y.val ≫ ((GroupScheme.baseChange b).map i).hom.hom = X.toMul.val := by
  obtain ⟨x, hx, hx₀, y, hy⟩ := h
  refine ⟨Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x),
    weightSpace_baseChange_mem G j α hx, ?_,
    Lie.kernelFieldExtension (K := K) H y, ?_⟩
  · intro h₀
    apply hx₀
    apply Additive.toMul.injective
    apply Lie.kernelFieldExtension_injective (K := K) G
    rw [Lie.schemeScalarExtension_one_tmul] at h₀
    have he := congrArg Additive.toMul h₀
    change Lie.kernelFieldExtension (K := K) G x.toMul = 1 at he
    change Lie.kernelFieldExtension (K := K) G x.toMul =
      Lie.kernelFieldExtension (K := K) G 1
    simpa only [map_one] using he
  · have hxy : Lie.targetMap i k y = x.toMul := Subtype.ext hy
    have he := Lie.kernelFieldExtension_target (K := K) i y
    rw [hxy] at he
    rw [Lie.schemeScalarExtension_one_tmul]
    exact congrArg Subtype.val he.symm

end Field

end Langlands.GroupScheme
