/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # The second adic system in Grothendieck devissage

Source: Stacks Project, Tag 088A, construction of G_e and the uniform torsion bound
(blueprint: lem-weil-pbc-devissage-second-adic-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Construct the K-adic system by algebraizing the K-power quotients of an I-adic system.
The isomorphism sigma records compatibility in both indices, not just on individual terms.
The isomorphism theta is the canonical interchange of the two quotient operations:
its equation with the two quotient projections specifies it uniquely.

Source: Stacks Project, Tag 088A, proof from the closed-immersion identification through
 the K^(4t) bound (blueprint: lem-weil-pbc-devissage-second-adic-system).

Proof:
1. For each positive e, use the closed-immersion coherent and formal equivalences of
Tag 087T together with the assumed completion equivalence on V(K^e). Apply essential
surjectivity to the formal quotient system M_n/K^e M_n. The result is a coherent module
G_e killed by K^e, uniquely determined up to its compatible isomorphism.
2. Full faithfulness lifts the quotient transitions uniquely. Reducing G_(e+1) modulo
K^e gives G_e since their I-completions have that identification. Thus the G_e and these
transitions define N in Coh(X,K). The quotient comparisons assemble into sigma;
full faithfulness gives naturality in e and their formal-system maps give naturality in n.
3. Two successive ideal quotients are the quotient by the sum of the ideal products.
Their cokernel universal properties give theta, characterized by the projection equation.
The quotient of alpha lifts to delta by full faithfulness. Faithfulness proves its
transition compatibility and the displayed comparison square.
4. The component torsion hypothesis gives a uniform exponent t. Reduction modulo K^e
bounds the kernels and cokernels by K^(2t), by the reduction assertion of Remark 0888.
The same remark transfers this bound through I-completion to the lifted maps G_e to
H/K^e H, with exponent 4t. This is the asserted component bound for delta.
All levels are positive (op e means e+1); no assertion is made at exponent zero.
-/
theorem grothendieckDevissage_secondAdicSystem
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅ (M.obj ⋙ formalCompletionFunctor K).flip)
      (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
        (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip),
      (∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H.obj ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H.obj ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj)) ∧
      (∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n)) ∧
      (∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (kernel (δ.hom.app (op e)))) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (cokernel (δ.hom.app (op e))))) := by
  obtain ⟨θ, hθ⟩ := grothendieckDevissage_secondAdicSystem_comparison I K H.obj
  obtain ⟨N, δ, σ, hsquare, htorsionδ⟩ :=
    grothendieckDevissage_secondAdicSystem_core I K M hthick H α htorsion θ
  exact ⟨N, δ, σ, θ, hθ, hsquare, htorsionδ⟩

end AlgebraicGeometry
