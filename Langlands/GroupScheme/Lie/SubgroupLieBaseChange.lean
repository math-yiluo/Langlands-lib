import Langlands.GroupScheme.Lie.SubgroupLieIdeal
import Langlands.GroupScheme.Lie.ScalarExtensionBracket
import Langlands.GroupScheme.Lie.SurjectiveDifferentialLifting

/-! # Scalar extension of tangent Lie algebras of subgroups over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

namespace Lie

/-- The range of a base-changed linear map is the base change of its range. -/
theorem range_baseChange {R M N : Type*} (A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    LinearMap.range (f.baseChange A) = (LinearMap.range f).baseChange A := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      rw [LinearMap.baseChange_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem a (LinearMap.mem_range_self f m)
    | add s t hs ht =>
      rw [map_add]
      exact Submodule.add_mem _ hs ht
  · intro z hz
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hz
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      obtain ⟨_, m, rfl⟩ := y
      exact ⟨a ⊗ₜ m, by rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]; rfl⟩
    | add s t hs ht =>
      rw [map_add]
      exact Submodule.add_mem _ (hs (LinearMap.mem_range_self _ _))
        (ht (LinearMap.mem_range_self _ _))

end Lie

namespace SubgroupFunctor

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (F : SubgroupFunctor G) (A : Type u) [CommRing A] [Algebra k A]

/-- The published tangent Lie ring, for a `k`-algebra regarded as an algebra over
`CommRingCat.of k`. -/
local instance instKernelLieRingOfField' (B : Type u) [CommRing B] [Algebra k B] :
    LieRing (Additive (lieKernel G B)) :=
  Lie.instAffineKernelLieRing (R := CommRingCat.of k) (A := B) G

/-- The published tangent Lie algebra, for a `k`-algebra regarded as an algebra
over `CommRingCat.of k`. -/
local instance instKernelLieAlgebraOfField' (B : Type u) [CommRing B] [Algebra k B] :
    LieAlgebra B (Additive (lieKernel G B)) :=
  Lie.instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := B) G

/-- Over a field, the tangent submodule of a subgroup represented by an affine
group locally of finite type commutes with scalar extension: with coefficients
in `A` it is the image of the base change of the tangent subspace over `k`. -/
theorem lie_eq_map_baseChange (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    F.lie A = ((F.lie k).baseChange A).map (Lie.kernelScalarExtension G A).toLinearMap := by
  rw [F.lie_eq_range A i hrep, F.lie_eq_range k i hrep, ← Lie.range_baseChange,
    ← LinearMap.range_comp]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := (Lie.kernelScalarExtension H A).surjective w
    exact ⟨t, (Lie.targetMapLinear_kernelScalarExtension i A t).symm⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨Lie.kernelScalarExtension H A t, Lie.targetMapLinear_kernelScalarExtension i A t⟩

/-- Over a field, the tangent submodule of a normal subgroup represented by an
affine group locally of finite type is an ideal for the actual tangent bracket
with coefficients in every commutative `k`-algebra. -/
theorem lie_lie_mem_of_isNormal_coefficients (hF : F.IsNormal) (i : H ⟶ G)
    (hrep : F.IsRepresentedBy i) (x : Additive (lieKernel G A))
    {y : Additive (lieKernel G A)} (hy : y ∈ F.lie A) :
    ⁅x, y⁆ ∈ F.lie A := by
  rw [F.lie_eq_map_baseChange A i hrep] at hy ⊢
  obtain ⟨s, hs, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := (Lie.kernelScalarExtension G A).surjective x
  refine ⟨⁅t, s⁆, ?_, (Lie.kernelScalarExtension_lie G A t s)⟩
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hs
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ =>
    rw [show ⁅t₁ + t₂, (F.lie k).subtype.baseChange A v⁆ =
        ⁅t₁, (F.lie k).subtype.baseChange A v⁆ + ⁅t₂, (F.lie k).subtype.baseChange A v⁆ from
      add_lie t₁ t₂ ((F.lie k).subtype.baseChange A v)]
    exact Submodule.add_mem _ h₁ h₂
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ =>
      rw [map_add, show ⁅a ⊗ₜ[k] x, (F.lie k).subtype.baseChange A v₁ +
          (F.lie k).subtype.baseChange A v₂⁆ =
          ⁅a ⊗ₜ[k] x, (F.lie k).subtype.baseChange A v₁⁆ +
            ⁅a ⊗ₜ[k] x, (F.lie k).subtype.baseChange A v₂⁆ from lie_add (a ⊗ₜ[k] x) _ _]
      exact Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _))
        (h₂ (LinearMap.mem_range_self _ _))
    | tmul b y =>
      rw [LinearMap.baseChange_tmul, LieAlgebra.ExtendScalars.bracket_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _
        (F.lie_lie_mem_of_isNormal hF i hrep x y.2)

/-- The tangent Lie ideal, with coefficients in a commutative `k`-algebra `A`, of
a normal subgroup functor represented by an affine group locally of finite type
over a field. Its carrier is `F.lie A`. -/
def coefficientLieIdeal (hF : F.IsNormal) (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    LieIdeal A (Additive (lieKernel G A)) :=
  { F.lie A with
    lie_mem := fun {x _} hy => F.lie_lie_mem_of_isNormal_coefficients A hF i hrep x hy }

@[simp] theorem mem_coefficientLieIdeal (hF : F.IsNormal) (i : H ⟶ G)
    (hrep : F.IsRepresentedBy i) {x : Additive (lieKernel G A)} :
    x ∈ F.coefficientLieIdeal A hF i hrep ↔ x ∈ F.lie A := Iff.rfl

end SubgroupFunctor

end Langlands.GroupScheme
