/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# Site-perfect coefficient duals and Tor windows

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/`
`sec-the-remaining-operations/sk-thm-sf-ctf-stability/det-thm-sf-hom-ctf.proof.md`
(blueprint: lem-sf-finite-ring-site-perfect-dual-window).
-/

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

@[expose] public section

namespace AlgebraicGeometry.Etale

/-! The finite-ring and boundedness hypotheses are retained in the statement even though the
generic dualizable argument only uses the site-perfect and Tor-amplitude hypotheses. -/

/--
Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/`
`sec-the-remaining-operations/sk-thm-sf-ctf-stability/det-thm-sf-hom-ctf.proof.md`, dualizable
case: a bounded finite-projective local model has dual in degrees `[-b,-a]`, and internal Hom is
its derived tensor with the second variable
(blueprint: lem-sf-finite-ring-site-perfect-dual-window).

Let `A` be a finite commutative ring killed by `ell ^ r`, `ell` prime and invertible on `T`. Let
`K` in `D(T_ét, A)` be site-perfect (étale locally a bounded complex of finite projective constant
`A`-modules) with Tor amplitude in `[a,b]`, and let `M` be bounded with Tor amplitude in `[c,d]`.
Then the coefficient dual `K^∨ = RHom(K, A_T)` has Tor amplitude in `[-b,-a]`; the canonical
evaluation-transpose map `K^∨ ⊗ᴸ M ⟶ RHom(K, M)`
(`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom K M`, the transpose of
`K ⊗ᴸ (K^∨ ⊗ᴸ M) ≅ (K ⊗ᴸ K^∨) ⊗ᴸ M ⟶ A_T ⊗ᴸ M ≅ M`) is an isomorphism; and `RHom(K, M)` has Tor
amplitude in `[c-b,d-a]`.

Proof (statement stage; the steps of the node):
1. Instantiate the generic ringed-site perfect-duality theorem (lem-sfb-ringed-site-perfect-duality)
   with the small étale ringed site of `T` and the coefficient sheaf `A_T`: a finite projective
   constant `A`-module is a direct summand of a finite free `A_T`-module. Hence `K^∨` is perfect,
   the bidual map `K ⟶ K^∨∨` is an isomorphism, and for every `M` the evaluation-transpose
   comparison `K^∨ ⊗ᴸ M ⟶ RHom(K, M)` is an isomorphism (second clause).
2. By the étale site-perfect dualizability lemma (`DerivedCategory.IsSitePerfect.isDualizable`)
   `K` has a dual `L` with an exact pairing `(L, K)`; the Koszul braiding swaps it
   (`DerivedCategory.nonempty_exactPairing_swap`), and `L ≅ K^∨` by Yoneda through the closed
   structure (`DerivedCategory.coefficientDualIsoOfExactPairing`). The two-sided-dual Tor-window
   lemma (lem-sf-source-dual-tor-interval) gives `K^∨` Tor amplitude in `[-b,-a]` (first clause).
3. For a module sheaf `F` in degree zero, `M ⊗ᴸ F[0]` has cohomology in `[c,d]`; the tensor
   cohomology-interval lemma (lem-sf-source-tensor-cohomology-interval) applied to `K^∨` and
   `M ⊗ᴸ F[0]`, with associativity of the derived tensor, gives `K^∨ ⊗ᴸ M` Tor amplitude in
   `[c-b,d-a]`.
4. Tor amplitude is invariant under isomorphism, so it transports along the isomorphism of
   Step 1 to `RHom(K, M)` (third clause; compare
   `Etale.torAmplitudeIn_derivedHom_of_isDualizable_aux`). No ordering of the endpoints is
   used: if `a > b` then `K = 0` and all conclusions hold trivially.
-/
theorem finiteRingSitePerfectDualWindow
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ell r : ℕ) [Fact ell.Prime] (_hr : 0 < r)
    (_hkill : ∀ x : A, (ell ^ r) • x = 0)
    {T : Scheme.{u}} [HasInvertibleExponent A T]
    {a b c d : ℤ}
    {K M : DerivedCategoryModule A T}
    (hK : DerivedCategory.IsSitePerfect K)
    (hKt : DerivedCategory.hasTorAmplitudeIn A T a b K)
    (_hM : _root_.DerivedCategory.TStructure.t.bounded M)
    (hMt : DerivedCategory.hasTorAmplitudeIn A T c d M) :
    DerivedCategory.hasTorAmplitudeIn A T (-b) (-a)
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} A) T).obj (op K)) ∧
      IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) ∧
      DerivedCategory.hasTorAmplitudeIn A T (c - b) (d - a)
        (((RHom(T)[ModuleCat.{u + 1} A]).obj (op K)).obj M) := by
  have hdual : DerivedCategory.IsDualizableEtale K := hK.isDualizable
  have hdual' := hdual
  obtain ⟨_⟩ := hdual
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  have hKt' := (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).1 hKt
  have hMt' := (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).1 hMt
  have hdualAmp := _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt'
  refine ⟨?_, ?_, ?_⟩
  · apply (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).2
    exact (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T (-b) (-a)).prop_of_iso
      (DerivedCategory.coefficientDualIsoOfExactPairing Kᘁ K).symm hdualAmp
  · exact MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K M
  · apply (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).2
    exact torAmplitudeIn_derivedHom_of_isDualizable_aux (A := ModuleCat.{u + 1} A) hKt' hdual' hMt'

end AlgebraicGeometry.Etale

end
