# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.HilbRepGotz (finite_piece)` is dropped; see the port edit below.
- Manual edit for Mathlib drift (FLT line 96, line 108 here): `(monomial s (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)) : MvPolynomial (Fin (n + 1)) R₀).IsHomogeneous m := by` is replaced by `(monomial s ((p : MvPolynomial (Fin (n + 1)) R₀).coeff s) : MvPolynomial (Fin (n + 1)) R₀).IsHomogeneous m := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 98, line 110 here): `by_cases hs : coeff s (p : MvPolynomial (Fin (n + 1)) R₀) = 0` is replaced by `by_cases hs : (p : MvPolynomial (Fin (n + 1)) R₀).coeff s = 0`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 102, line 114 here): `let u : (Fin (n + 1) →₀ ℕ) → Sm R₀ n m := fun s => ⟨monomial s (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)), hw s⟩` is replaced by `let u : (Fin (n + 1) →₀ ℕ) → Sm R₀ n m := fun s => ⟨monomial s ((p : MvPolynomial (Fin (n + 1)) R₀).coeff s), hw s⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 109, line 121 here): `monomial s (algebraMap R₀ A (coeff s (p : MvPolynomial (Fin (n + 1)) R₀))) := by` is replaced by `monomial s (algebraMap R₀ A ((p : MvPolynomial (Fin (n + 1)) R₀).coeff s)) := by`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 113, line 125 here): `lam R₀ m A (monomial s (algebraMap R₀ A (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)))) =` is replaced by `lam R₀ m A (monomial s (algebraMap R₀ A ((p : MvPolynomial (Fin (n + 1)) R₀).coeff s))) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 120, line 132 here): `show algebraMap R₀ A (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)) =` is replaced by `show algebraMap R₀ A ((p : MvPolynomial (Fin (n + 1)) R₀).coeff s) =`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 121, line 133 here): `coeff s (p : MvPolynomial (Fin (n + 1)) R₀) • (1 : A) by rw [Algebra.smul_def, mul_one],` is replaced by `(p : MvPolynomial (Fin (n + 1)) R₀).coeff s • (1 : A) by rw [Algebra.smul_def, mul_one],`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 142, line 154 here): `refine ⟨∑ s ∈ q.support, coeff s q • w R₀ m A s, ?_⟩` is replaced by `refine ⟨∑ s ∈ q.support, q.coeff s • w R₀ m A s, ?_⟩`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 125, line 137 here): `change coeff s (p : MvPolynomial (Fin (n + 1)) R₀) • monomial s (1 : R₀) = monomial s (coeff s (p : MvPolynomial (Fin (n + 1)) R₀))` is replaced by `change (p : MvPolynomial (Fin (n + 1)) R₀).coeff s • monomial s (1 : R₀) = monomial s ((p : MvPolynomial (Fin (n + 1)) R₀).coeff s)`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 23 here); in 19 lines the replacements `Type` (universe 0) → `Type uz` (18 places), `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The FLT construction works over the absolute base `Spec ℤ`. With schemes in universe `uz`, the ring `ℤ : Type` can only serve as a base in universe 0, so the absolute base ring `ℤ` is replaced by `ULift.{uz} ℤ` (the ring `ℤ` lifted to universe `uz`, isomorphic to `ℤ`). The new helper module `Langlands.AlgebraicGeometry.ULiftIntAlgebra` provides the `ULift ℤ`-algebra structure of every commutative ring (`Langlands.ULiftInt.algebra`), algebra maps from ring maps (`Langlands.ULiftInt.toAlgHom`), uniqueness of ring maps out of `ULift ℤ` (`Langlands.ULiftInt.ringHom_ext`) and noetherianity of `ULift ℤ`. In this file this module is imported; `Langlands.ULiftInt.algebra` is declared as a local instance; `Langlands.ULiftInt.toAlgHom φ` replaces FLT's `φ.toIntAlgHom`; Mathlib's `specULiftZIsTerminal` (`Spec (ULift ℤ)` is terminal) replaces `specZIsTerminal`. In the statement, the projective space `Proj ℤ[X₀, …, X_N]` receiving the closed immersion becomes `Proj (ULift ℤ)[X₀, …, X_N]`; otherwise the statement only changes by the universe generalization. The proof is the FLT proof with these replacements. The changed lines are:
  - after line 10 here, inserted:
    replacement:

    ```lean
    import Langlands.AlgebraicGeometry.ULiftIntAlgebra
    ```
  - after line 452 here, inserted:
    replacement:

    ```lean
    attribute [local instance] Langlands.ULiftInt.algebra in
    ```
  - line 470 here:
    FLT text (universe-0 port):

    ```lean
          ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
    ```

    replacement:

    ```lean
          ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ))),
    ```
  - line 482 here:
    FLT text (universe-0 port):

    ```lean
      have hpers : ∀ (A : Type) [CommRing A] (N : FG ℤ n m h A), W h A N →
    ```

    replacement:

    ```lean
      have hpers : ∀ (A : Type uz) [CommRing A] (N : FG (ULift.{uz} ℤ) n m h A), W h A N →
    ```
  - line 489 here:
    FLT text (universe-0 port):

    ```lean
        @Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace ℤ _ (Sm ℤ n m) _
    ```

    replacement:

    ```lean
        @Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace (ULift.{uz} ℤ) _ (Sm (ULift.{uz} ℤ) n m) _
    ```
  - lines 492–493 here:
    FLT text (universe-0 port):

    ```lean
      have hclosed : ∀ (A : Type) [CommRing A] [Algebra ℤ A] (N : FG ℤ n m h A),
          ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra ℤ B] (φ : A →ₐ[ℤ] B),
    ```

    replacement:

    ```lean
      have hclosed : ∀ (A : Type uz) [CommRing A] [Algebra (ULift.{uz} ℤ) A] (N : FG (ULift.{uz} ℤ) n m h A),
          ∃ 𝔞 : Ideal A, ∀ (B : Type uz) [CommRing B] [Algebra (ULift.{uz} ℤ) B] (φ : A →ₐ[(ULift.{uz} ℤ)] B),
    ```
  - line 506 here:
    FLT text (universe-0 port):

    ```lean
        AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal ℤ (FG ℤ n m h)
    ```

    replacement:

    ```lean
        AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal (ULift.{uz} ℤ) (FG (ULift.{uz} ℤ) n m h)
    ```
  - lines 511–513 here:
    FLT text (universe-0 port):

    ```lean
      let pt : ∀ (A : Type) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ Z) := fun A _ =>
        (equivW ℤ m h A (hgen A) (hpers A)).trans
          ((ptZ A).trans (Equiv.subtypeUnivEquiv fun g => specZIsTerminal.hom_ext _ _))
    ```

    replacement:

    ```lean
      let pt : ∀ (A : Type uz) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ Z) := fun A _ =>
        (equivW (ULift.{uz} ℤ) m h A (hgen A) (hpers A)).trans
          ((ptZ A).trans (Equiv.subtypeUnivEquiv fun g => specULiftZIsTerminal.hom_ext _ _))
    ```
  - line 517 here:
    FLT text (universe-0 port):

    ```lean
      have hQ : grOf ℤ m h B Q = Module.Grassmannian.map φ.toIntAlgHom (grOf ℤ m h A P) := by
    ```

    replacement:

    ```lean
      have hQ : grOf (ULift.{uz} ℤ) m h B Q = Module.Grassmannian.map (Langlands.ULiftInt.toAlgHom φ) (grOf (ULift.{uz} ℤ) m h A P) := by
    ```
  - line 519 here:
    FLT text (universe-0 port):

    ```lean
        rw [idealOf_map, idealOf_grOf ℤ m h A (hgen A), hPQ]
    ```

    replacement:

    ```lean
        rw [idealOf_map, idealOf_grOf (ULift.{uz} ℤ) m h A (hgen A), hPQ]
    ```
  - line 522 here:
    FLT text (universe-0 port):

    ```lean
      change (ptZ B ⟨grOf ℤ m h B Q, _⟩).1 ≫ ι = (Spec.map (CommRingCat.ofHom φ) ≫ (ptZ A ⟨grOf ℤ m h A P, _⟩).1) ≫ ι
    ```

    replacement:

    ```lean
      change (ptZ B ⟨grOf (ULift.{uz} ℤ) m h B Q, _⟩).1 ≫ ι = (Spec.map (CommRingCat.ofHom φ) ≫ (ptZ A ⟨grOf (ULift.{uz} ℤ) m h A P, _⟩).1) ≫ ι
    ```
  - lines 524–525 here:
    FLT text (universe-0 port):

    ```lean
      change (ptG B (grOf ℤ m h B Q)).1 = Spec.map (CommRingCat.ofHom φ.toIntAlgHom.toRingHom) ≫ (ptG A (grOf ℤ m h A P)).1
      rw [← hnatG A B φ.toIntAlgHom (grOf ℤ m h A P), hQ]
    ```

    replacement:

    ```lean
      change (ptG B (grOf (ULift.{uz} ℤ) m h B Q)).1 = Spec.map (CommRingCat.ofHom (Langlands.ULiftInt.toAlgHom φ).toRingHom) ≫ (ptG A (grOf (ULift.{uz} ℤ) m h A P)).1
      rw [← hnatG A B (Langlands.ULiftInt.toAlgHom φ) (grOf (ULift.{uz} ℤ) m h A P), hQ]
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth`
(representability of the Hilbert functor): let `h` satisfy `h d = C(n + d, n)` for `d < m`, the
persistence bound for `e ≥ m` over fields, and attainment of `h e`, `h (e + 1)` for `e ≥ m`. Then
points with Hilbert function `h` are stable under base change, and there are a scheme `Hilb` and
bijections `pt A : Point A n h ≃ (Spec A ⟶ Hilb)` natural in ring maps, with a closed immersion of
`Hilb` into some `ℙᴺ` over `ULift ℤ` (FLT: over `ℤ`).

Proof (namespace `HilbRepGotz`, with base ring `R₀ = ULift ℤ`). Section `Theta`: `theta` identifies
`A ⊗[R₀] (forms of degree m over R₀)` with the forms of degree `m` over `A` (`thetaE`, inverse `lam`
on monomials). Section `IdealOf`: a submodule `N` of `A ⊗ Sm` gives the ideal `idealOf A N` generated
by the corresponding forms, with `piece (idealOf A N) m ≅ (A ⊗ Sm) / N` (`pieceEquiv`) and
`comap_K_eq`; it is compatible with base change (`idealOf_map`). Section `Points`: points of the
Grassmannian `FG` of rank-`(h m)` quotients of `A ⊗ Sm` (ported `Module.Grassmannian`) satisfying
`W` (the piece in degree `m + 1` is projective of rank `h (m + 1)`) correspond bijectively to Hilbert
points (`grOf`, `equivW`), using generation in degree `m`
(`Point.I_eq_span_of_forall_finrank_piece_succ_le`) and Gotzmann persistence over rings
(`HilbertFunctor.exists_point_I_eq_of_projective_piece_succ`). The Grassmannian is represented by a
scheme with a closed immersion into projective space (ported Grassmannian representability), and
`W` is a closed condition (`HilbertFunctor.exists_ideal_forall_projective_piece_succ_iff` plus the
ported closed-subfunctor theorem), so its locus `Z` is a closed subscheme representing the Hilbert
points; `pt` and its naturality are transported along `equivW`, with ring maps turned into
`ULift ℤ`-algebra maps by `Langlands.ULiftInt.toAlgHom`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.Sm`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.finite_homogeneousSubmodule`
- scoped instance `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.instFiniteSm`
- private theorem `HilbRepGotz.finite_piece`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.degree_eq_of_mem_support`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta_tmul`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta_mem`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.w`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.lam`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.lam_monomial`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.lam_map`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.lam_theta`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta_injective`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta_surjective`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.thetaE`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.thetaE_apply_coe`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.decompose_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.homogeneousComponent_mem_of_mem_span`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.mem_of_mem_span_of_isHomogeneous`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.formsOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.formsOf_le`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.idealOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.idealOf_generated`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta_mem_idealOf`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.K`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.map_thetaE_eq_K`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.pieceEquiv`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.comap_K_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.theta_cancel_tmul`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.idealOf_map`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.FG`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.W`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.projective_piece_idealOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.rankAtStalk_piece_idealOf`
- abbrev `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.KP`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.grOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.grOf_toSubmodule`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.formsOf_grOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.idealOf_grOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.W_grOf`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.grOf_eq_of_I_eq`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.equivW`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz.equivW_apply`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal` (same contribution).
Other project modules imported: `Langlands.AlgebraicGeometry.ULiftIntAlgebra` (same contribution).
Other imports: `Mathlib`.
