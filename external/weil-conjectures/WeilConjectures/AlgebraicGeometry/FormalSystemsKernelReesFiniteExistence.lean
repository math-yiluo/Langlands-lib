/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAlgebraExists
import WeilConjectures.AlgebraicGeometry.FormalKernelGradedActionExists
import WeilConjectures.AlgebraicGeometry.FormalKernelGradedActionLocalGenerators
@[expose] public section
universe ut
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The graded algebra and finite graded module construction, without the independent
quasi-coherence assertion about the coproduct of kernels.
Source: Stacks Project, Cohomology of Schemes, Lemma 087Z (affine proof), via Lemma 087W
and Section 0EHN; https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-systems-kernel-rees-finite-existence).

Proof:
1. The reduction condition iterates to identify F_l / I^r F_l with F_r for l >= r >= 1.
The transitions are sheaf epimorphisms. A local lift of x in K_n to F_(m+n+1) lies in
I^n F_(m+n+1), with I^0 F = F. Multiplication by a in I^m therefore gives an element
of K_(m+n). Differences of lifts lie in I^(n+1) F_(m+n+1), and differences of
representatives of a lie in I^(m+1); their products vanish by annihilation at level
m+n+1. Thus the result glues uniquely. Local representatives of quotient sections
exist because quotient projections are sheaf epimorphisms. This gives bilinear,
restriction-compatible action maps on every open, including nonaffine opens.
2. The same construction multiplies I^m/I^(m+1) and I^n/I^(n+1). Products of power
ideal sections factor through I^(m+n) by iterated ideal multiplication; this supplies
c in the displayed formula. Changing representatives changes the product by
I^(m+n+1). The degree-zero unit is the quotient projection from O_X. Ring and
module laws follow locally by using representatives and lifts to one common level:
both associativity expressions become (ab)t = a(bt), commutativity becomes ab = ba,
and the unit acts as 1. Sheaf uniqueness makes these local equalities global, giving
A and a graded module M with the required formulas for every existing lift t.
3. On an affine neighbourhood Spec R, Lemma 087W identifies the formal system with
N/I^r N for a finite module N over the I-adic completion of R. Ideal-product and
quotient affine sections identify the algebra pieces with I^n/I^(n+1) and the kernel
pieces with I^n N/I^(n+1) N, including K_0 = N/IN. The tilde/global-sections
adjunction identifies their sheaves, and the representative formulas from steps 1--2
identify the operations with multiplication on these module quotients.
4. The completed-module associated-graded generator lemma gives finite generators of
N/IN and says their lifts generate each I^n N/I^(n+1) N with coefficients from I^n.
Tilde preserves the resulting epimorphism from a finite sum of graded algebra copies.
Choose the corresponding degree-zero sections on the affine neighbourhood. For any
section on any smaller open, this sheaf epimorphism supplies coefficient sections
locally near each point; its degree-n component is exactly the finite sum in
IsLocallyGeneratedInDegreeZero. Affine neighbourhoods cover X, proving that predicate.
No global lifts or global generating family on X are asserted. -/
theorem formalSystems_kernel_rees_finite_exists {X : Scheme.{ut}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) :
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
  obtain ⟨A, hunit, hmul⟩ := formalAssociatedGraded_algebra_exists I
  obtain ⟨M, hact⟩ := formalKernel_graded_action_exists I F A hunit hmul
  refine ⟨A, hunit, hmul, M, ?_, hact⟩
  apply formalKernel_graded_action_local_generators I F A M
  intro n U a x t ht
  exact hact n 0 U a x t ht
end AlgebraicGeometry
