/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageRecoverLevels

/-!
# Grothendieck existence by devissage

Source: Stacks Project, Cohomology of Schemes, Lemma 088A (blueprint:
lem-weil-pbc-grothendieck-existence-devissage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraizing a formal coherent module which is algebraizable on all thickenings
and differs from a completion by uniform ideal-power torsion.
Source: Stacks Project, Lemma 088A (blueprint: lem-weil-pbc-grothendieck-existence-devissage).

Proof, following the five steps of the node and Stacks Lemma 088A:
1. By lem-weil-pbc-closed-immersion-coherent-equivalence (Stacks 087T), pushforward
identifies coherent modules and formal systems on X_e with those on X killed by K^e.
The thickening hypothesis therefore gives the corresponding completion equivalence.
2. Apply this equivalence to (F_n / K^e F_n)_n to obtain coherent modules G_e killed
by K^e. The quotient transitions induce G_{e+1} / K^e G_{e+1} ≅ G_e, so these form
an object of Coh(X,K) (def-weil-pbc-coherent-formal-module).
3. The comparison induces G_e → H / K^e H. Use
lem-weil-pbc-formal-systems-annihilated-by-power (Stacks Remark 0888) to choose a
uniform componentwise exponent t, then obtain bounds K^(2t) after quotienting by K^e
and K^(4t) for the kernels and cokernels of G_e → H / K^e H.
4. Apply lem-weil-pbc-grothendieck-existence-easy (Stacks 0889), part (1), with ideal K.
It gives coherent F, a map a : F → H with K-power-torsion kernel and cokernel, and
an isomorphism (G_e)_e ≅ (F / K^e F)_e compatible with a.
5. Fix a positive level n and reduce the comparison modulo I^n. The uniqueness clause
of lem-weil-pbc-grothendieck-existence-easy identifies F / I^n F with F_n. Uniqueness
makes these isomorphisms compatible with the transitions, hence F^ ≅ (F_n).

Kernel forks and cokernel coforks are taken in Coh(X,I), not in the ambient category
of all inverse systems. Their universal properties avoid an extra abelian-instance binder.
The index `op n` denotes level n+1. The noetherian witness in the thickening hypothesis
is derived from the closed immersion into X; it imposes no additional geometric condition.
-/
theorem grothendieck_existence_devissage
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X)
    (α : M ⟶ completion X I |>.obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧
      ∃ k : KernelFork α, ∃ c : CokernelCofork α,
        Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧
        (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower K.toModulesι t).2 (k.pt.obj.obj (op n)))) ∧
        (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower K.toModulesι t).2 (c.pt.obj.obj (op n))))) :
    ∃ F : CoherentModules X, Nonempty ((completion X I).obj F ≅ M) := by
  obtain ⟨t, ht, k, c, hk, hc, hkt, hct⟩ := htorsion
  have hcomponent := ((coherentFormalModule_annihilated_iff X I K M
    ((completion X I).obj H) α).out 4 1 rfl rfl).mp
    ⟨k, c, hk, hc, t, ht, fun n ↦ ⟨hkt n, hct n⟩⟩
  obtain ⟨N, δ, σ, θ, hθ, hsquare, hδ⟩ :=
    grothendieckDevissage_secondAdicSystem I K M hthick H α hcomponent
  obtain ⟨F, a, β, hβ, ha, _⟩ :=
    grothendieckExistenceEasy_torsionTriple K H N δ hδ
  obtain ⟨φ, hφ⟩ := grothendieckDevissage_recoverLevels I K M H α hcomponent
    N δ σ θ hθ hsquare F a β hβ ha
  refine ⟨F, ⟨?_⟩⟩
  exact ObjectProperty.isoMk _ (NatIso.ofComponents φ (fun {_ _} f ↦ hφ _ _ f))

end AlgebraicGeometry
