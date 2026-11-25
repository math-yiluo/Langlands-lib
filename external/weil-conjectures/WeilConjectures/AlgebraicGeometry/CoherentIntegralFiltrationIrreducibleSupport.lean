/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentSupportAdicChain
import WeilConjectures.AlgebraicGeometry.CoherentGenericFilteredExtension
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationExtension
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! # The irreducible-support step of coherent integral filtration

Source: Stacks Project, Tag 01YF, irreducible-support paragraphs, using Tag 01YE.
(blueprint: lem-pc-s3-irreducible-support-filtration-step)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Filter a coherent module with irreducible support, assuming smaller supports filtered.

Source: Stacks Project, Tag 01YF, ideal-power and generic-inclusion paragraphs,
using Tags 01Y9 and 01YE (https://stacks.math.columbia.edu/tag/01YF).
(blueprint: lem-pc-s3-irreducible-support-filtration-step)

Proof: Let J be the vanishing ideal of T with its reduced induced closed subscheme
structure. Some power J^n kills F by Tag 01Y9. The powers J^k F and their successive
cokernels are coherent; each graded quotient is supported in T and annihilated by J.
A graded quotient with proper support has a filtration by hsmaller. For a quotient G
with full support T, the stalk of J at ξ is the ambient maximal ideal: a local function
vanishing at ξ vanishes on T in its domain, since ξ specializes to every point of T.
Thus the maximal ideal kills Gξ. Give T its reduced induced integral scheme structure
and apply Tag 01YE to obtain a monomorphism from the pushforward of a finite sum of a
coherent ideal I into G, invertible near ξ. Since Gξ is nonzero, I is nonzero. The source
has a coherent filtration by partial sums with each factor the pushforward of I; finite
closed pushforward preserves coherence and finite sums. The cokernel Q is coherent,
its support is contained in T by stalk exactness, and its stalk at ξ is zero. Its support
is therefore strictly smaller than T, so hsmaller supplies its filtration. The coherent
short-exact extension theorem concatenates these filtrations to filter G. Descending
through the J-adic powers, concatenate the graded filtrations to filter F. If n = 0,
F is zero and the length-zero filtration suffices. No induction on full support occurs
inside this step; all uses of support induction are precisely the supplied hsmaller. -/
theorem coherentIntegralFiltration_of_irreducible_support
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (hsmaller : ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊂ (T : Set X) →
      HasCoherentIntegralFiltration G)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X)) :
    HasCoherentIntegralFiltration F := by
  classical
  have graded (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
      (hGT : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X))
      (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
        ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) :
      HasCoherentIntegralFiltration G := by
    by_cases hfull : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = (T : Set X)
    · obtain ⟨A, Q, f, g, w, hs, hA, hQ, hAf, hQT⟩ :=
        coherent_generic_filtered_extension X T ξ hξ G hG hfull hkill
      exact coherentIntegralFiltration_of_shortExact X (ShortComplex.mk f g w)
        hs hA hG hQ hAf (hsmaller Q hQ hQT)
    · exact hsmaller G hG (Set.ssubset_iff_subset_ne.mpr ⟨hGT, hfull⟩)
  obtain ⟨n, P, hP0, hPn, hP, hstep⟩ := coherent_support_adic_chain X T ξ hξ F hF hSupp
  have hgood : ∀ k, k ≤ n → HasCoherentIntegralFiltration (P k) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      have := Subobject.subsingleton_of_isZero hPn
      refine ⟨0, fun _ ↦ ⊥, fun _ _ _ ↦ le_rfl, rfl, Subsingleton.elim _ _, ?_, ?_⟩
      · intro j
        have hc := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
        exact hc.2.2.2.2 _ _ Subobject.botCoeIsoZero.symm hc.2.2.2.1
      · intro j
        exact Fin.elim0 j
    | @of_succ k hk ih =>
      obtain ⟨G, f, g, w, hs, hG, hGT, hkill⟩ := hstep k (Nat.lt_of_succ_le hk)
      exact coherentIntegralFiltration_of_shortExact X (ShortComplex.mk f g w)
        hs (hP (k + 1) hk) (hP k (Nat.le_trans (Nat.le_succ k) hk)) hG
        ih (graded G hG hGT hkill)
  simpa only [hP0] using hgood 0 (Nat.zero_le n)

end AlgebraicGeometry.Scheme.Modules
