import Langlands.GroupScheme.Lie.FieldExtension
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Scalar extension of actual subgroup tangent images -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K

local instance tangentBaseChangeAffine
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance tangentBaseChangeFiniteType
    (G : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

namespace Lie

variable {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The actual differential commutes with scalar extension on pure vectors. -/
theorem targetMapLinear_schemeScalarExtension_one_tmul (j : H ⟶ G)
    (x : Additive (lieKernel H k)) :
    targetMapLinear ((GroupScheme.baseChange b).map j) K
        (schemeScalarExtension (K := K) H (1 ⊗ₜ[k] x)) =
      schemeScalarExtension (K := K) G (1 ⊗ₜ[k] targetMapLinear j k x) := by
  rw [schemeScalarExtension_one_tmul, schemeScalarExtension_one_tmul]
  exact congrArg Additive.ofMul (kernelFieldExtension_target (K := K) j x.toMul).symm

end Lie

namespace RelativeRoot

variable (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The scalar-extended span of a submodule inside the actual Lie kernel of
the scheme pullback. -/
def extendedLieSubmodule (W : Submodule k (Additive (lieKernel G k))) :
    Submodule K (Additive (lieKernel ((GroupScheme.baseChange b).obj G) K)) :=
  Submodule.span K ((fun x => Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x)) ''
    (W : Set (Additive (lieKernel G k))))

theorem extendedLieSubmodule_mono
    {W W' : Submodule k (Additive (lieKernel G k))} (h : W ≤ W') :
    extendedLieSubmodule (K := K) G W ≤ extendedLieSubmodule (K := K) G W' := by
  apply Submodule.span_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- Extension of scalar spans commutes with arbitrary submodule sums. -/
theorem extendedLieSubmodule_iSup {I : Sort v}
    (W : I → Submodule k (Additive (lieKernel G k))) :
    extendedLieSubmodule (K := K) G (⨆ i, W i) =
      ⨆ i, extendedLieSubmodule (K := K) G (W i) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.iSup_induction W
      (motive := fun x => Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x) ∈
        ⨆ i, extendedLieSubmodule (K := K) G (W i)) hx ?_ ?_ ?_
    · intro i x hx
      exact Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨x, hx, rfl⟩)
    · simpa only [TensorProduct.tmul_zero, LinearEquiv.map_zero] using
        (⨆ i, extendedLieSubmodule (K := K) G (W i)).zero_mem
    · intro x y hx hy
      simpa only [TensorProduct.tmul_add, LinearEquiv.map_add] using
        (⨆ i, extendedLieSubmodule (K := K) G (W i)).add_mem hx hy
  · exact iSup_le fun i => extendedLieSubmodule_mono G (le_iSup W i)

variable {G}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (j : H ⟶ G)

/-- The range of the actual pulled-back differential is the scalar extension
of the original differential range. -/
theorem range_targetMapLinear_baseChange :
    LinearMap.range (Lie.targetMapLinear ((GroupScheme.baseChange b).map j) K) =
      extendedLieSubmodule (K := K) G (LinearMap.range (Lie.targetMapLinear j k)) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (Lie.schemeScalarExtension (K := K) H).surjective y
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      have hgen :
          Lie.targetMapLinear ((GroupScheme.baseChange b).map j) K
              (Lie.schemeScalarExtension (K := K) H (1 ⊗ₜ[k] x)) ∈
            extendedLieSubmodule (K := K) G
              (LinearMap.range (Lie.targetMapLinear j k)) := by
        rw [Lie.targetMapLinear_schemeScalarExtension_one_tmul]
        exact Submodule.subset_span ⟨_, ⟨x, rfl⟩, rfl⟩
      have hc := (extendedLieSubmodule (K := K) G
        (LinearMap.range (Lie.targetMapLinear j k))).smul_mem c hgen
      simpa only [Lie.schemeScalarExtension_tmul, one_smul, map_smul] using hc
    | add x y hx hy =>
      simpa only [LinearEquiv.map_add, map_add] using
        (extendedLieSubmodule (K := K) G
          (LinearMap.range (Lie.targetMapLinear j k))).add_mem hx hy
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨Lie.schemeScalarExtension (K := K) H (1 ⊗ₜ[k] x),
      Lie.targetMapLinear_schemeScalarExtension_one_tmul j x⟩

/-- A represented subgroup's intrinsic tangent image commutes with actual
scheme scalar extension. -/
theorem tangentSubmodule_baseChange {F : SubgroupFunctor G}
    (hj : F.IsRepresentedBy j) :
    tangentSubmodule (F.baseChange b) =
      extendedLieSubmodule (K := K) G (tangentSubmodule F) := by
  have : Mono j.hom.hom := hj.1
  have hjK := hj.baseChange b
  have : Mono ((GroupScheme.baseChange b).map j).hom.hom := hjK.1
  rw [← hjK.2, tangentSubmodule_range, ← hj.2, tangentSubmodule_range]
  exact range_targetMapLinear_baseChange j

/-- An exact Lie-image comparison extends along every field extension, provided
an affine locally finite-type representative is supplied. -/
theorem HasLieImage.baseChange {F : SubgroupFunctor G}
    {W : Submodule k (Additive (lieKernel G k))}
    (hF : HasLieImage F W) (hj : F.IsRepresentedBy j) :
    HasLieImage (F.baseChange b) (extendedLieSubmodule (K := K) G W) := by
  apply (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
  rw [tangentSubmodule_baseChange j hj,
    (hasLieImage_iff_tangentSubmodule_eq F W).mp hF]

end RelativeRoot
end Langlands.GroupScheme
