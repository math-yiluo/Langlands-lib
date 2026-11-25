/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLift
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion

/-! # Algebraization after a supplied quotient interchange

Source: Stacks Project, Tags 088A and 0888
(blueprint: lem-weil-pbc-devissage-second-adic-system-core).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraize the K-power quotients, with compatible maps and a uniform torsion bound.
The supplied θ is characterized by its projection equation; N and δ are constructed
jointly with σ, rather than being arbitrary objects.
Source: Stacks Project, Tags 088A and 0888
(blueprint: lem-weil-pbc-devissage-second-adic-system-core).

Proof: identify coherent modules and formal systems killed by K^e with the
corresponding categories on V(K^e), using the closed-immersion equivalences.
Algebraize the formal systems M_n/K^e M_n by hthick. Full faithfulness lifts
the transitions uniquely; reduction modulo K^e gives the previous level,
since completion preserves quotients and reflects isomorphisms. This defines N.
The chosen algebraization isomorphisms give σ, natural in n and e; naturality
in e follows from the definition of the lifted transitions. Reduce α modulo
K^e and compose with the inverse of θ. Full faithfulness lifts this map to
δ_e. Faithfulness proves transition compatibility, giving δ and the square.
If K^t kills the component kernels and cokernels of α, reduction modulo K^e
kills those of the reduced map by K^(2t), by Remark 0888. On affine opens of
V(K^e), the same remark transfers this completed bound to δ_e with exponent
4t. These local annihilation identities give the global uniform bound. Since
t is positive, so is 4t; every level used has exponent e+1 or n+1.
-/
theorem grothendieckDevissage_secondAdicSystem_core
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
        (cokernel (α.hom.app (op n)))))
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅
        (M.obj ⋙ formalCompletionFunctor K).flip),
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
  obtain ⟨N, δ, σ, hsquare⟩ :=
    grothendieckDevissage_secondAdicSystem_lift_data I K M hthick H α θ
  obtain ⟨t, ht, hα⟩ := htorsion
  refine ⟨N, δ, σ, hsquare, 4 * t, ?_, ?_⟩
  · omega
  · exact grothendieckDevissage_secondAdicSystem_torsion
      I K M hthick H α θ N δ σ hsquare t ht hα

end AlgebraicGeometry
