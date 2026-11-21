import Langlands.GroupScheme.Lie.SubgroupTangent
import Langlands.GroupScheme.Lie.AffineBracketFunctoriality
import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability

/-! # Tangent Lie subalgebras of subgroups and Lie ideals of normal subgroups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.SubgroupFunctor

section Subalgebra

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable (F : SubgroupFunctor G) (A : Type u) [CommRing A] [Algebra R A]
variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- The tangent submodule of a represented subgroup functor is closed under the
actual tangent Lie bracket. -/
theorem lie_lie_mem (i : H ⟶ G) (hrep : F.IsRepresentedBy i)
    {x y : Additive (lieKernel G A)} (hx : x ∈ F.lie A) (hy : y ∈ F.lie A) :
    ⁅x, y⁆ ∈ F.lie A := by
  rw [F.lie_eq_range A i hrep] at hx hy ⊢
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  exact ⟨⁅x', y'⁆, Lie.targetMapLinear_lie i x' y'⟩

/-- The tangent Lie subalgebra of a represented subgroup functor. Its carrier is
the tangent submodule `F.lie A`, which does not depend on the representing map. -/
def lieSubalgebra (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    LieSubalgebra A (Additive (lieKernel G A)) :=
  { F.lie A with lie_mem' := fun hx hy => F.lie_lie_mem A i hrep hx hy }

@[simp] theorem lieSubalgebra_toSubmodule (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    (F.lieSubalgebra A i hrep).toSubmodule = F.lie A := rfl

@[simp] theorem mem_lieSubalgebra (i : H ⟶ G) (hrep : F.IsRepresentedBy i)
    {x : Additive (lieKernel G A)} :
    x ∈ F.lieSubalgebra A i hrep ↔ x ∈ F.lie A := Iff.rfl

/-- The tangent Lie subalgebra is the range of the Lie differential of any
representing homomorphism. -/
theorem lieSubalgebra_eq_range (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    F.lieSubalgebra A i hrep = (Lie.targetMapLieHom i A).range := by
  apply LieSubalgebra.toSubmodule_injective
  rw [lieSubalgebra_toSubmodule, LieHom.range_toSubmodule, F.lie_eq_range A i hrep]
  rfl

end Subalgebra

section Ideal

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
variable [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
variable (F : SubgroupFunctor G)

omit [LocallyOfFiniteType G.X.hom] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] in
/-- Normal subgroup functors are stable under the actual adjoint action on
tangent vectors over every test algebra. -/
theorem adjoint_mem_lie_of_isNormal (hF : F.IsNormal) {A : Type u} [CommRing A]
    [Algebra (CommRingCat.of k) A] (g : Lie.AffinePoints G A)
    {y : Additive (lieKernel G A)} (hy : y ∈ F.lie A) :
    adjoint G A g y ∈ F.lie A :=
  hF _ (Lie.constant G g) y.toMul.val trivial hy

omit [LocallyOfFiniteType G.X.hom] in
/-- Over a field, tangent vectors of a subgroup represented by an affine group
locally of finite type with coefficients in a test algebra are scalar
combinations of base tangent vectors. Linear functionals therefore return the
coordinates to the base tangent submodule. -/
theorem linearFunctional_coordinates_mem_lie {d : ℕ} (c : Lie.FiniteCoordinates G d)
    (i : H ⟶ G) (hrep : F.IsRepresentedBy i)
    (A : CommAlgCat.{u} (CommRingCat.of k)) {z : Additive (lieKernel G A)}
    (hz : z ∈ F.lie A) (ℓ : A →ₗ[k] k) :
    (fun j => ℓ (c.equiv A z j)) ∈
      (F.lie (CommRingCat.of k)).map
        (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))).toLinearMap := by
  rw [F.lie_eq_range A i hrep] at hz
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := (Lie.kernelScalarExtension H A).surjective w
  induction t using TensorProduct.inductionOn with
  | add s t hs ht =>
    simp only [map_add, Pi.add_apply]
    exact Submodule.add_mem _ hs ht
  | tmul a y =>
    let f : CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k) ⟶ A :=
      CommAlgCat.ofHom (Algebra.ofId (CommRingCat.of k) A)
    have hcoord : c.equiv A (Lie.targetMapLinear i A
        (lieKernelMapLinear H (Algebra.ofId (CommRingCat.of k) A) y)) =
        fun j => algebraMap k A (c.equiv (CommAlgCat.of (CommRingCat.of k)
          (CommRingCat.of k)) (Lie.targetMapLinear i (CommRingCat.of k) y) j) := by
      rw [lieKernelTargetLinear_map]
      exact c.naturality f _
    have hmem : c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
        (Lie.targetMapLinear i (CommRingCat.of k) y) ∈
        (F.lie (CommRingCat.of k)).map
          (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))).toLinearMap := by
      refine ⟨Lie.targetMapLinear i (CommRingCat.of k) y, ?_, rfl⟩
      rw [F.lie_eq_range _ i hrep]
      exact ⟨y, rfl⟩
    have hℓ : ∀ r : k, ℓ (a * algebraMap k A r) = ℓ a * r := fun r => by
      rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    have hfun : (fun j => ℓ (c.equiv A (Lie.targetMapLinear i A
        (Lie.kernelScalarExtension H A (a ⊗ₜ y))) j)) =
        ℓ a • c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
          (Lie.targetMapLinear i (CommRingCat.of k) y) := by
      funext j
      rw [Lie.kernelScalarExtension_tmul, map_smul, map_smul, hcoord]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hℓ _
    have key := Submodule.smul_mem _ (ℓ a) hmem
    rw [← hfun] at key
    exact key

omit [LocallyOfFiniteType G.X.hom] in
/-- The coordinate image of the tangent submodule of a normal subgroup,
represented by an affine group locally of finite type, is stable under the
actual adjoint representation on every test algebra. -/
theorem isStableSubspace_adjointRepresentation (hF : F.IsNormal) {d : ℕ}
    (c : Lie.FiniteCoordinates G d) (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    (Lie.adjointRepresentation c).IsStableSubspace
      ((F.lie (CommRingCat.of k)).map
        (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))).toLinearMap) := by
  intro A x v hv ℓ
  obtain ⟨y, hy, rfl⟩ := hv
  let f : CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k) ⟶ A :=
    CommAlgCat.ofHom (Algebra.ofId (CommRingCat.of k) A)
  have hbase : (fun j => algebraMap k A
      (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) y j)) =
      c.equiv A (lieKernelMapLinear G (Algebra.ofId (CommRingCat.of k) A) y) :=
    (c.naturality f y).symm
  have hact := Lie.adjointRepresentation_affineAction c A x
    (lieKernelMapLinear G (Algebra.ofId (CommRingCat.of k) A) y)
  rw [MatrixRepresentation.affineAction_apply] at hact
  change (fun j => ℓ ((((Lie.adjointRepresentation c).affineMatrix A x : Matrix (Fin d) (Fin d) A) *ᵥ
    (fun j => algebraMap k A
      (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) y j))) j)) ∈ _
  rw [hbase, hact]
  exact F.linearFunctional_coordinates_mem_lie c i hrep A
    (F.adjoint_mem_lie_of_isNormal hF x (F.lie_map_mem _ _ hy)) ℓ

local instance : LieRing (Additive (lieKernel G (CommRingCat.of k))) :=
  Lie.instAffineKernelLieRing (R := CommRingCat.of k) (A := CommRingCat.of k) G

/-- The tangent submodule of a normal subgroup, represented by an affine group
locally of finite type, is an ideal for the actual tangent Lie bracket. -/
theorem lie_lie_mem_of_isNormal (hF : F.IsNormal) (i : H ⟶ G)
    (hrep : F.IsRepresentedBy i) (x : Additive (lieKernel G (CommRingCat.of k)))
    {y : Additive (lieKernel G (CommRingCat.of k))} (hy : y ∈ F.lie (CommRingCat.of k)) :
    ⁅x, y⁆ ∈ F.lie (CommRingCat.of k) := by
  let c := Lie.finiteCoordinates G
  let e := c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
  have hstable := F.isStableSubspace_adjointRepresentation hF c i hrep
  have hmem := hstable.tangentMatrix_mulVec_mem x.toMul (v := e y) ⟨y, hy, rfl⟩
  have hbr := Lie.adjointDifferentialLieHom_apply_bracket c x y
  have heq : (Lie.adjointRepresentation c).tangentMatrix k x.toMul *ᵥ e y = e ⁅x, y⁆ :=
    hbr
  rw [heq] at hmem
  obtain ⟨z, hz, hze⟩ := hmem
  rw [← e.injective hze]
  exact hz

local instance : LieAlgebra (CommRingCat.of k) (Additive (lieKernel G (CommRingCat.of k))) :=
  Lie.instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := CommRingCat.of k) G

/-- The tangent Lie ideal of a normal subgroup functor represented by an affine
group locally of finite type over a field. Its carrier is `F.lie k`. -/
def lieIdeal (hF : F.IsNormal) (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    LieIdeal (CommRingCat.of k) (Additive (lieKernel G (CommRingCat.of k))) :=
  { F.lie (CommRingCat.of k) with
    lie_mem := fun {x _} hy => F.lie_lie_mem_of_isNormal hF i hrep x hy }

@[simp] theorem mem_lieIdeal (hF : F.IsNormal) (i : H ⟶ G) (hrep : F.IsRepresentedBy i)
    {x : Additive (lieKernel G (CommRingCat.of k))} :
    x ∈ F.lieIdeal hF i hrep ↔ x ∈ F.lie (CommRingCat.of k) := Iff.rfl

theorem lieIdeal_toSubmodule (hF : F.IsNormal) (i : H ⟶ G) (hrep : F.IsRepresentedBy i) :
    (F.lieIdeal hF i hrep : Submodule (CommRingCat.of k)
      (Additive (lieKernel G (CommRingCat.of k)))) = F.lie (CommRingCat.of k) := rfl

end Ideal

end Langlands.GroupScheme.SubgroupFunctor
