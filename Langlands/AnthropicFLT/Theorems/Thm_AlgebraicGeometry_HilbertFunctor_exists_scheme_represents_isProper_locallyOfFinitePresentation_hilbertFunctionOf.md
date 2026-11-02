# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.solution n P hP`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (3 places) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The FLT construction works over the absolute base `Spec ℤ`. With schemes in universe `uz`, the ring `ℤ : Type` can only serve as a base in universe 0, so the absolute base ring `ℤ` is replaced by `ULift.{uz} ℤ` (the ring `ℤ` lifted to universe `uz`, isomorphic to `ℤ`). The new helper module `Langlands.AlgebraicGeometry.ULiftIntAlgebra` provides the `ULift ℤ`-algebra structure of every commutative ring (`Langlands.ULiftInt.algebra`), algebra maps from ring maps (`Langlands.ULiftInt.toAlgHom`), uniqueness of ring maps out of `ULift ℤ` (`Langlands.ULiftInt.ringHom_ext`) and noetherianity of `ULift ℤ`. In this file this module is imported; `Langlands.ULiftInt.algebra` is declared as a local instance. In the statement, `Spec ℤ` and `Proj ℤ[X₀, …, X_N]` become `Spec (ULift ℤ)` and `Proj (ULift ℤ)[X₀, …, X_N]`, `ProjSpace.π ℤ N` becomes `ProjSpace.π (ULift ℤ) N`, and `algebraMap ℤ A` becomes the algebra map of `Langlands.ULiftInt.algebra A` (a local instance for the statement); otherwise the statement only changes by the universe generalization. The changed lines are:
  - after line 11 here, inserted:
    replacement:

    ```lean
    import Langlands.AlgebraicGeometry.ULiftIntAlgebra
    ```
  - after line 28 here, inserted:
    replacement:

    ```lean
    attribute [local instance] Langlands.ULiftInt.algebra in
    ```
  - lines 36–37 here:
    FLT text (universe-0 port):

    ```lean
          ∃ (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ))
            (pt : ∀ (A : Type) [CommRing A],
    ```

    replacement:

    ```lean
          ∃ (Hilb : Scheme.{uz}) (p : Hilb ⟶ Spec (CommRingCat.of (ULift.{uz} ℤ)))
            (pt : ∀ (A : Type uz) [CommRing A],
    ```
  - lines 46–47 here:
    FLT text (universe-0 port):

    ```lean
            (∀ (A : Type) [CommRing A] (x : Point A n (hilbertFunctionOf n P m)),
                pt A x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ∧
    ```

    replacement:

    ```lean
            (∀ (A : Type uz) [CommRing A] (x : Point A n (hilbertFunctionOf n P m)),
                pt A x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (ULift.{uz} ℤ) A))) ∧
    ```
  - lines 50–51 here:
    FLT text (universe-0 port):

    ```lean
            ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
              IsClosedImmersion ι ∧ ι ≫ ProjSpace.π ℤ N = p :=
    ```

    replacement:

    ```lean
            ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ))),
              IsClosedImmersion ι ∧ ι ≫ ProjSpace.π (ULift.{uz} ℤ) N = p :=
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`:
for a Hilbert polynomial `P` there is `D₀` such that for every `m ≥ D₀` there are a scheme `Hilb` with
a morphism `p : Hilb ⟶ Spec (ULift ℤ)` (FLT: `Spec ℤ`) and bijections `pt A` between points with
Hilbert function `hilbertFunctionOf n P m` over `A` and morphisms `Spec A ⟶ Hilb`, such that: points
are stable under base change; `y.I` is the extension of `x.I` iff `pt B y = Spec φ ≫ pt A x`; every
`pt A x` lies over the structure morphism of `Spec A`; `p` is proper and locally of finite
presentation; every finite set of points of `Hilb` lies in an affine open; and `p` factors through a
closed immersion into `ℙᴺ` over `ULift ℤ`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf` (same contribution).
Other project modules imported: `Langlands.AlgebraicGeometry.ULiftIntAlgebra` (same contribution).
Other imports: `Mathlib`.
