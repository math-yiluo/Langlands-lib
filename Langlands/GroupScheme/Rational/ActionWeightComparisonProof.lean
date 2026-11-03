import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # Intrinsic action eigenspaces and adjoint weight comparisons: proof -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Naturality

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- An actual action commutes with every change of test algebra. -/
theorem act_affineMap (b : AutomorphicAction H G) (f : A →ₐ[R] B)
    (h : Lie.AffinePoints H A) (g : Lie.AffinePoints G A) :
    Lie.affineMap G f (b.act h g) =
      b.act (Lie.affineMap H f h) (Lie.affineMap G f g) := by
  simp only [Lie.affineMap_apply]
  exact b.naturality _ h g

/-- Epsilon scaling fixes every constant dual-number point. -/
theorem affineMap_epsilonScaleAlg_constant (H : GroupScheme (Spec R)) (c : A)
    (h : Lie.AffinePoints H A) :
    Lie.affineMap H (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c)
      (Lie.constant H h) = Lie.constant H h := by
  simp only [Lie.constant, ← Lie.affineMap_comp]
  have he : (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c).comp
      (TrivSqZeroExt.inlAlgHom R A A) = TrivSqZeroExt.inlAlgHom R A A := by
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext <;>
      simp [GeneralLinear.DualNumber.epsilonScaleAlg]
  rw [he]

/-- The action of a constant point commutes with actual epsilon scaling. -/
theorem act_constant_lieKernelScale (b : AutomorphicAction H G) (h : Lie.AffinePoints H A)
    (c : A) (x : lieKernel G A) :
    b.act (Lie.constant H h) (lieKernelScale G c x).val =
      Lie.affineMap G (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c)
        (b.act (Lie.constant H h) x.val) := by
  rw [act_affineMap, affineMap_epsilonScaleAlg_constant, lieKernelScale_val]

end Naturality

section Eigenvectors

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

omit [IsAffineHom G.X.hom] in
/-- The zero tangent vector is an eigenvector for every character. -/
theorem zero_mem_actionEigenvectors (b : AutomorphicAction S.toGrp G)
    (χ : characterLattice S) : (0 : Additive (lieKernel G k)) ∈ actionEigenvectors b χ := by
  intro A _ _ s
  simp only [toMul_zero, map_one, OneMemClass.coe_one, AutomorphicAction.act_one]

omit [IsAffineHom G.X.hom] in
/-- Eigenvectors are closed under the actual kernel group law. -/
theorem add_mem_actionEigenvectors (b : AutomorphicAction S.toGrp G)
    (χ : characterLattice S) {X Y : Additive (lieKernel G k)}
    (hX : X ∈ actionEigenvectors b χ) (hY : Y ∈ actionEigenvectors b χ) :
    X + Y ∈ actionEigenvectors b χ := by
  intro A _ _ s
  simp only [toMul_add, map_mul, Subgroup.coe_mul, AutomorphicAction.act_mul_right,
    hX A s, hY A s]

/-- Eigenvectors are closed under epsilon scaling by base-field scalars. -/
theorem smul_mem_actionEigenvectors (b : AutomorphicAction S.toGrp G)
    (χ : characterLattice S) (c : k) {X : Additive (lieKernel G k)}
    (hX : X ∈ actionEigenvectors b χ) :
    c • X ∈ actionEigenvectors b χ := by
  intro A _ _ s
  rw [lieKernel_smul_toMul, lieKernelMap_scale, act_constant_lieKernelScale, hX A s,
    ← lieKernelScale_val, ← lieKernelScale_mul, ← lieKernelScale_mul, mul_comm]

/-- The span defining `actionWeightSpace` is exactly the intrinsic eigenvector set. -/
theorem coe_actionWeightSpace (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    (actionWeightSpace b χ : Set (Additive (lieKernel G k))) = actionEigenvectors b χ := by
  apply Set.Subset.antisymm _ Submodule.subset_span
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX => exact hX
  | zero => exact zero_mem_actionEigenvectors b χ
  | add X Y _ _ hX hY => exact add_mem_actionEigenvectors b χ hX hY
  | smul c X _ hX => exact smul_mem_actionEigenvectors b χ c hX

/-- Membership in the action weight space is the eigenvector condition. -/
theorem mem_actionWeightSpace_iff (b : AutomorphicAction S.toGrp G) (χ : characterLattice S)
    {X : Additive (lieKernel G k)} :
    X ∈ actionWeightSpace b χ ↔ X ∈ actionEigenvectors b χ := by
  rw [← SetLike.mem_coe, coe_actionWeightSpace]

/-- For conjugation, the intrinsic action weight space is the original adjoint weight space. -/
theorem actionWeightSpace_conjugation (i : S.toGrp ⟶ G) (χ : characterLattice S) :
    actionWeightSpace (AutomorphicAction.conjugation i) χ = weightSpace i χ := by
  ext X
  rw [mem_actionWeightSpace_iff, mem_weightSpace]
  refine forall_congr' fun A => ?_
  refine forall_congr' fun _ => ?_
  refine forall_congr' fun _ => ?_
  refine forall_congr' fun t => ?_
  have hc : Lie.constant S.toGrp t ≫ i.hom.hom = Lie.constant G (t ≫ i.hom.hom) := by
    simp only [Lie.constant, Lie.affineMap_apply, Category.assoc]
  rw [AutomorphicAction.conjugation_act, hc]
  constructor
  · intro h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg (fun z : Additive (lieKernel G A) => z.toMul.val) h

end Eigenvectors

/-- Intrinsic eigenvector spans are the eigenvector sets, and conjugation recovers the
Library's original adjoint weight spaces. -/
theorem actionWeightComparison : ActionWeightComparisonStatement.{u} :=
  ⟨fun _ _ _ hAff _ b χ => @coe_actionWeightSpace _ _ _ _ hAff b χ,
    fun _ _ _ hAff _ i χ => @actionWeightSpace_conjugation _ _ _ _ hAff i χ⟩

end Langlands.GroupScheme.RelativeRoot
