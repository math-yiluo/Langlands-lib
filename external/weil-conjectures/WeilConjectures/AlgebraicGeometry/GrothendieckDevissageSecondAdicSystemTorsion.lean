/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicTorsionKernel
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicTorsionCokernel

/-! # Uniform torsion bound for a compatible second-ideal algebraization

Source: Stacks Project, Tags 088A and 0888.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A fixed compatible algebraization has the uniform exponent 4t.
There is no existence conclusion: N, δ and σ are supplied, and no projection
characterization of θ is needed for this estimate.
Source: Stacks Project, Tag 088A (lemma-existence-tricky), the two applications
of Remark 0888 (remark-inverse-systems-kernel-cokernel-annihilated-by).
https://stacks.math.columbia.edu/tag/088A
https://stacks.math.columbia.edu/tag/0888
(blueprint: lem-weil-pbc-devissage-second-adic-system-torsion).

Proof: On an affine open, the kernel and cokernel of α_n are the ordinary
module kernel and cokernel and are killed by K^t. For a,b in K^t, define the
canonical reverse map by lifting ay and multiplying its lift by b. The kernel
bound makes it independent of the lift. Its two composites with α_n are
multiplication by ab. Reduce these identities modulo K^(e+1). Hence the kernel
and cokernel of the reduced map are killed by K^(2t), uniformly in e,n.
The comparison square and the invertible σ and θ identify this reduced map
with the nth component of the I-completion of δ_e.

Set Z_e = V(K^(e+1)). Both coherent terms of δ_e are killed by K^(e+1), so
the closed-immersion equivalence descends δ_e to a coherent map on Z_e.
For its completed map, the preceding bound is K^(2t) at every I-level.
Remark 0888 passes these component bounds to the formal kernel and cokernel,
with exponent 2*(2t). In detail, the reverse maps for pairs of scalars in
K^(2t) commute with all reduction maps, so their inverse limits give reverse
maps on the finite completed modules. Their two composite identities kill
the completed kernel and cokernel by K^(4t).

The assumed completion equivalence on Z_e is exact and reflects zero objects.
To check compatibility with ideal products, write each product as the image
of the ideal-action map J tensor P → P, where J is the image of K^(4t) on Z_e
and P is the coherent kernel or cokernel. On affine opens, completion of finite
modules over a Noetherian ring is tensoring with its flat completed ring.
It therefore preserves this image and identifies its action map with the
completed ideal-action map. The completed products are zero by the preceding
bound on the completed kernel and cokernel. This calculation on affine opens
shows that their formal completions are zero. Reflection of zero by the global
completion equivalence on Z_e now gives zero coherent products on Z_e; no
faithfulness assumption on completion of an individual affine open is needed.
Closed pushforward identifies these products with the stated products on X,
using the ideal-product comparison for the closed immersion. The same argument
works for every e with exponent 4t, without a choice of N or δ. -/
theorem grothendieckDevissage_secondAdicSystem_torsion
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip)
    (hsquare : ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (hα : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (cokernel (δ.hom.app (op e)))) := by
  intro e
  exact ⟨
    grothendieckDevissage_secondAdicSystem_torsion_kernel I K M hthick H α θ N δ σ
      hsquare t ht hα e,
    grothendieckDevissage_secondAdicSystem_torsion_cokernel I K M hthick H α θ N δ σ
      hsquare t ht hα e⟩

end AlgebraicGeometry
