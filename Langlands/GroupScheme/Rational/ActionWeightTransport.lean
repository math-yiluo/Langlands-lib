import Langlands.GroupScheme.Rational.SplitTorusFiniteRank
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof

/-! # Action weights under equivariant subgroup inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section KernelTargets

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

@[simp] theorem lieKernelTarget_val (x : lieKernel G A) :
    (Lie.targetMap f A x).val = x.val ≫ f.hom.hom := rfl

theorem lieKernelTarget_injective (hf : Mono f.hom.hom) :
    Function.Injective (Lie.targetMap f A) := by
  intro x y h
  apply Subtype.ext
  exact hf.right_cancellation _ _ (congrArg Subtype.val h)

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- Coefficient change commutes with postcomposition on actual kernels. -/
theorem lieKernelMap_target (a : A →ₐ[R] B) (x : lieKernel G A) :
    lieKernelMap H a (Lie.targetMap f A x) =
      Lie.targetMap f B (lieKernelMap G a x) := by
  apply Subtype.ext
  simp only [lieKernelMap_val, lieKernelTarget_val, Lie.affineMap_apply, Category.assoc]

/-- Epsilon scaling commutes with postcomposition on actual kernels. -/
theorem lieKernelScale_target (c : A) (x : lieKernel G A) :
    lieKernelScale H c (Lie.targetMap f A x) =
      Lie.targetMap f A (lieKernelScale G c x) := by
  apply Subtype.ext
  simp only [lieKernelScale_val, lieKernelTarget_val, Lie.affineMap_apply, Category.assoc]

/-- A tangent vector in an all-test image lifts to a tangent vector when the
homomorphism is a monomorphism. -/
theorem mem_map_lieKernel_iff (hf : Mono f.hom.hom) (F : SubgroupFunctor G)
    (X : lieKernel H A) :
    X.val ∈ (F.map f).carrier
        ((algSpec R).obj (op (CommAlgCat.of R (DualNumber A)))) ↔
      ∃ Y : lieKernel G A,
        Y.val ∈ F.carrier ((algSpec R).obj (op (CommAlgCat.of R (DualNumber A)))) ∧
        Lie.targetMap f A Y = X := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    change Lie.AffinePoints G (DualNumber A) at y
    change y ≫ f.hom.hom = X.val at hyx
    have hy0 : Lie.reduction G y = 1 := by
      apply hf.right_cancellation
      rw [MonObj.one_comp]
      change Lie.affineMap G (TrivSqZeroExt.fstHom R A A) y ≫ f.hom.hom = 1
      rw [Lie.affineMap_apply, Category.assoc, hyx]
      exact X.property
    exact ⟨⟨y, hy0⟩, hy, Subtype.ext hyx⟩
  · rintro ⟨Y, hY, hYX⟩
    exact ⟨Y.val, hY, congrArg Subtype.val hYX⟩

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

@[simp] theorem lieKernelTargetLinear_toMul (x : Additive (lieKernel G A)) :
    (Lie.targetMapLinear f A x).toMul = Lie.targetMap f A x.toMul := rfl

end KernelTargets

namespace RelativeRoot

section Weights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) (hf : Mono f.hom.hom)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (hbc : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ G.X),
      b.act s x ≫ f.hom.hom = c.act s (x ≫ f.hom.hom))

include hf hbc

/-- Equivariant monomorphisms preserve and reflect intrinsic action eigenvectors. -/
theorem mem_actionEigenvectors_target_iff (χ : characterLattice S)
    (X : Additive (lieKernel G k)) :
    Lie.targetMapLinear f k X ∈ actionEigenvectors c χ ↔
      X ∈ actionEigenvectors b χ := by
  constructor
  · intro h A _ _ s
    apply hf.right_cancellation
    rw [hbc]
    simpa only [lieKernelTargetLinear_toMul, lieKernelMap_target,
      lieKernelScale_target, lieKernelTarget_val] using h A s
  · intro h A _ _ s
    have he := congrArg (fun x => x ≫ f.hom.hom) (h A s)
    simpa only [lieKernelTargetLinear_toMul, lieKernelMap_target,
      lieKernelScale_target, lieKernelTarget_val, hbc] using he

/-- Equivariant monomorphisms preserve and reflect intrinsic action weight spaces. -/
theorem mem_actionWeightSpace_target_iff (χ : characterLattice S)
    (X : Additive (lieKernel G k)) :
    Lie.targetMapLinear f k X ∈ actionWeightSpace c χ ↔
      X ∈ actionWeightSpace b χ := by
  rw [mem_actionWeightSpace_iff, mem_actionWeightSpace_iff]
  exact mem_actionEigenvectors_target_iff f hf b c hbc χ X

/-- The intrinsic action support of a subgroup is unchanged by an equivariant
monomorphism, including its possible zero weight. -/
theorem actionWeightSupport_map (F : SubgroupFunctor G) :
    actionWeightSupport c (F.map f) = actionWeightSupport b F := by
  ext χ
  constructor
  · rintro ⟨X, hX, hXw, hXF⟩
    obtain ⟨Y, hYF, hYX⟩ := (mem_map_lieKernel_iff f (A := k) hf F X.toMul).mp hXF
    have hLY : Lie.targetMapLinear f k (Additive.ofMul Y) = X :=
      Additive.toMul.injective hYX
    refine ⟨Additive.ofMul Y, ?_, ?_, hYF⟩
    · intro hY
      apply hX
      rw [← hLY, hY, map_zero]
    · apply (mem_actionWeightSpace_target_iff f hf b c hbc χ _).mp
      rw [hLY]
      exact hXw
  · rintro ⟨X, hX, hXw, hXF⟩
    refine ⟨Lie.targetMapLinear f k X, ?_,
      (mem_actionWeightSpace_target_iff f hf b c hbc χ X).mpr hXw, ?_⟩
    · intro h
      apply hX
      let := hf
      apply Lie.targetMapLinear_injective f k
      rw [map_zero]
      exact h
    · exact ⟨X.toMul.val, hXF, rfl⟩

end Weights

end RelativeRoot

end Langlands.GroupScheme
