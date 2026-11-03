import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Exact kernels from a fixed tensor with a line-detecting first factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section PureTensor

variable {A : Type u} [CommRing A] {n m : Type}

/-- If both factors have a coordinate equal to one, equality of pure tensors
forces the transformed first factor to be a unit multiple of the original one.
The assertion holds over every commutative ring, including rings with nilpotents. -/
theorem exists_unit_smul_of_pureTensor_eq
    (v v' : n → A) (w w' : m → A) (j : n) (s : m)
    (hv : v j = 1) (hw : w s = 1)
    (h : (fun ij : n × m => v' ij.1 * w' ij.2) =
      fun ij => v ij.1 * w ij.2) :
    ∃ a : Aˣ, v' = (a : A) • v := by
  have hab : v' j * w' s = 1 := by
    simpa only [hv, hw, one_mul] using congrFun h (j, s)
  let a : Aˣ := ⟨v' j, w' s, hab, (mul_comm _ _).trans hab⟩
  refine ⟨a, ?_⟩
  funext r
  change v' r = v' j * v r
  have hr : v' r * w' s = v r := by
    simpa only [hw, mul_one] using congrFun h (r, s)
  calc
    v' r = (v' r * w' s) * v' j := by
      rw [mul_assoc, (mul_comm _ _).trans hab, mul_one]
    _ = v r * v' j := congrArg (fun z => z * v' j) hr
    _ = v' j * v r := mul_comm _ _

end PureTensor

section SchemeRepresentations

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- On every scheme test, the tensor action sends a pure coefficient vector to
the pure vector formed by the two original actions. -/
theorem tensor_pointMatrix_decomposable
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (v : n → Γ(T.left, ⊤)) (w : m → Γ(T.left, ⊤)) :
    ((ρ.tensor σ).pointMatrix T x :
        Matrix (n × m) (n × m) Γ(T.left, ⊤)) *ᵥ
          (fun ij => v ij.1 * w ij.2) =
      fun ij => ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ v) ij.1 *
        ((σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) *ᵥ w) ij.2 := by
  rw [tensor_pointMatrix]
  exact GeneralLinear.kroneckerHom_mulVec n m _ _ v w

/-- Fixing a normalized pure tensor preserves its first coordinate line on
arbitrary scheme tests; no reducedness assumption on the test is used. -/
theorem unit_smul_of_tensor_fixes
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (v : n → k) (w : m → k) (j : n) (s : m)
    (hv : v j = 1) (hw : w s = 1)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (h : ((ρ.tensor σ).pointMatrix T x :
        Matrix (n × m) (n × m) Γ(T.left, ⊤)) *ᵥ
          (fun ij => scalarMap T (v ij.1 * w ij.2)) =
        fun ij => scalarMap T (v ij.1 * w ij.2)) :
    ∃ a : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun r => scalarMap T (v r)) =
        (a : Γ(T.left, ⊤)) • (fun r => scalarMap T (v r)) := by
  simp only [map_mul] at h
  rw [tensor_pointMatrix_decomposable ρ σ T x
    (fun r => scalarMap T (v r)) (fun r => scalarMap T (w r))] at h
  exact exists_unit_smul_of_pureTensor_eq
    (fun r => scalarMap T (v r)) _ (fun r => scalarMap T (w r)) _ j s
    (by rw [hv, map_one]) (by rw [hw, map_one]) h

/-- An actual finite representation whose scheme-theoretic kernel has the
prescribed subgroup range. -/
structure KernelRepresentation (i : H ⟶ G) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  kernel_range : SubgroupFunctor.range (kernelι representation) = SubgroupFunctor.range i

/-- A subgroup-fixed normalized tensor with a line-detecting first factor gives
an actual representation with exactly that subgroup as its represented kernel.
The subgroup is allowed to be nonsmooth. -/
theorem nonempty_kernelRepresentation_of_fixedTensor
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : H ⟶ G) (hN : (SubgroupFunctor.range i).IsNormal)
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (v : n → k) (w : m → k) (j : n) (s : m)
    (hv : v j = 1) (hw : w s = 1)
    (hfixed : ((ρ.tensor σ).restrict i).IsFixedVector
      (fun ij => v ij.1 * w ij.2))
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
            (fun r => scalarMap T (v r)) =
          (a : Γ(T.left, ⊤)) • (fun r => scalarMap T (v r))) →
        x ∈ (SubgroupFunctor.range i).carrier T) :
    Nonempty (KernelRepresentation i) := by
  let D := normalFixedSubrepresentation (ρ.tensor σ) i hN
  refine ⟨⟨D.dimension, D.representation, ?_⟩⟩
  apply D.range_kernel_eq hfixed
  intro T x hx
  exact hline T x (unit_smul_of_tensor_fixes ρ σ v w j s hv hw T x hx)

/-- Choose the exact-kernel representation supplied by the fixed tensor. -/
def kernelRepresentationOfFixedTensor
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : H ⟶ G) (hN : (SubgroupFunctor.range i).IsNormal)
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (v : n → k) (w : m → k) (j : n) (s : m)
    (hv : v j = 1) (hw : w s = 1)
    (hfixed : ((ρ.tensor σ).restrict i).IsFixedVector
      (fun ij => v ij.1 * w ij.2))
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
            (fun r => scalarMap T (v r)) =
          (a : Γ(T.left, ⊤)) • (fun r => scalarMap T (v r))) →
        x ∈ (SubgroupFunctor.range i).carrier T) :
    KernelRepresentation i :=
  Classical.choice (nonempty_kernelRepresentation_of_fixedTensor
    i hN ρ σ v w j s hv hw hfixed hline)

end SchemeRepresentations

end Langlands.GroupScheme.MatrixRepresentation
