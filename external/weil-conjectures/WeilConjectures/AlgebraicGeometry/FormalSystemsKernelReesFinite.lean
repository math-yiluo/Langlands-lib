/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.FormalSystemsKernelReesFiniteExistence

/-! # Finite graded kernel module of a coherent formal system

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z, statement and affine proof;
Section 0EHN (blueprint: lem-weil-pbc-formal-systems-kernel-rees-finite).
-/

@[expose] public section

universe ut

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sum of successive kernels is quasi-coherent and finite over the associated graded
ideal algebra, with generators in degree zero and the action specified by local lifts.
Source: Stacks, Lemma 087Z and Section 0EHN
(blueprint: lem-weil-pbc-formal-systems-kernel-rees-finite).

Proof:
1. Repeated reduction identifies F_l / I^r F_l with F_r. All transitions are sheaf
surjections. Lift a kernel section locally to F_(n+m+1); it belongs to I^n F_(n+m+1).
Multiplying by I^m lands in K_(n+m). Differences of lifts belong to I^(n+1), hence are
killed by I^m. Differences of representatives in I^(m+1) likewise act by zero. Glue the
resulting bilinear maps. A common lift checks associativity, the unit, and the associated
graded algebra multiplication (def-weil-pbc-coherent-formal-module).
2. On an affine open, the formal system corresponds to a finite completion module M,
with F_r = M/I^r M (lem-weil-pbc-coherent-formal-modules-affine). Its kernels are
I^n M/I^(n+1) M. Kernels are quasi-coherent (pqf-lem-coherent-ft-locnoeth and
lem-weil-pbc-quasi-coherent-module-kernel). Ideal products and quotients have the expected
affine sections (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections). Tilde preserves
colimits, so identifies both sheaf sums with the associated sheaves of the corresponding
algebraic direct sums, respecting the displayed operations
(lem-weil-pbc-affine-tilde-gamma-adjunction; lem-weil-pbc-spec-module-tilde-sections).
3. Finite generators of M/IM generate the associated graded module in degree zero
(lem-weil-pbc-completed-module-associated-graded-generators). Tilde preserves the resulting
surjection (lem-weil-pbc-affine-tilde-gamma-adjunction), giving finite degree-zero generators
of the sheaf module over the sheaf algebra, without asserting O_X-finite type.
4. Every point has such an affine neighbourhood. Quasi-coherence and finite generation
are local (pqf-def-coherent), so the affine conclusions prove the statement globally. -/
theorem formalSystems_kernel_rees_finite {X : Scheme.{ut}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) :
    (∐ (formalKernelPiece F)).IsQuasicoherent ∧
    ∃ A : GradedSheafAlgebra (formalAssociatedGradedPiece I),
      A.unit = formalAssociatedGradedπ I 0 ∧
      (∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          A.mul m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) ∧
      ∃ M : GradedSheafModule A (formalKernelPiece F),
        M.IsLocallyGeneratedInDegreeZero ∧
        ∀ (m n : ℕ) (U : X.Opens)
          (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
          (x : (formalKernelPiece F n).val.obj (op U))
          (t : (F.obj.obj (op (m + n))).val.obj (op U)),
          (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F (m + n)).val.app (op U)
            (M.act m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t := by
  refine ⟨?_, formalSystems_kernel_rees_finite_exists I F⟩
  have hF (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  let (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent := hF n
  let (n : ℕ) : (formalKernelPiece F n).IsQuasicoherent := by
    cases n with
    | zero => exact hF 0
    | succ n => exact Scheme.Modules.isQuasicoherent_kernel _
  have hsum := Scheme.Modules.isQuasicoherent_sigma
    (fun n : ULift.{ut} ℕ ↦ formalKernelPiece F n.down)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Sigma.reindex (Equiv.ulift : ULift.{ut} ℕ ≃ ℕ) (formalKernelPiece F)) hsum

end AlgebraicGeometry
