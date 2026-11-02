# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The FLT construction works over the absolute base `Spec ℤ`. With schemes in universe `uz`, the ring `ℤ : Type` can only serve as a base in universe 0, so the absolute base ring `ℤ` is replaced by `ULift.{uz} ℤ` (the ring `ℤ` lifted to universe `uz`, isomorphic to `ℤ`). The new helper module `Langlands.AlgebraicGeometry.ULiftIntAlgebra` provides the `ULift ℤ`-algebra structure of every commutative ring (`Langlands.ULiftInt.algebra`), algebra maps from ring maps (`Langlands.ULiftInt.toAlgHom`), uniqueness of ring maps out of `ULift ℤ` (`Langlands.ULiftInt.ringHom_ext`) and noetherianity of `ULift ℤ`. In this file this module is imported; `Langlands.ULiftInt.algebra` is declared as a local instance; Mathlib's `specULiftZIsTerminal` (`Spec (ULift ℤ)` is terminal) replaces `specZIsTerminal`. In the statement, `Spec ℤ` and `Proj ℤ[X₀, …, X_N]` become `Spec (ULift ℤ)` and `Proj (ULift ℤ)[X₀, …, X_N]`, `ProjSpace.π ℤ N` becomes `ProjSpace.π (ULift ℤ) N`, and `algebraMap ℤ A` becomes the algebra map of `Langlands.ULiftInt.algebra A` (a local instance for the statement); otherwise the statement only changes by the universe generalization. The proof is the FLT proof with these replacements. The changed lines are:
  - after line 10 here, inserted:
    replacement:

    ```lean
    import Langlands.AlgebraicGeometry.ULiftIntAlgebra
    ```
  - after line 29 here, inserted:
    replacement:

    ```lean
    attribute [local instance] Langlands.ULiftInt.algebra in
    ```
  - lines 37–38 here:
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
  - lines 47–48 here:
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
  - lines 51–52 here:
    FLT text (universe-0 port):

    ```lean
            ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
              IsClosedImmersion ι ∧ ι ≫ ProjSpace.π ℤ N = p := by
    ```

    replacement:

    ```lean
            ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ))),
              IsClosedImmersion ι ∧ ι ≫ ProjSpace.π (ULift.{uz} ℤ) N = p := by
    ```
  - line 60 here:
    FLT text (universe-0 port):

    ```lean
      refine ⟨Hilb, ι ≫ ProjSpace.π ℤ N, pt, hbc, ?_, ?_, ?_, ?_, ?_, N, ι, hι, rfl⟩
    ```

    replacement:

    ```lean
      refine ⟨Hilb, ι ≫ ProjSpace.π (ULift.{uz} ℤ) N, pt, hbc, ?_, ?_, ?_, ?_, ?_, N, ι, hι, rfl⟩
    ```
  - line 70 here:
    FLT text (universe-0 port):

    ```lean
        exact specZIsTerminal.hom_ext _ _
    ```

    replacement:

    ```lean
        exact specULiftZIsTerminal.hom_ext _ _
    ```
  - lines 74–75 here:
    FLT text (universe-0 port):

    ```lean
        haveI : IsNoetherianRing (CommRingCat.of ℤ) := inferInstanceAs (IsNoetherianRing ℤ)
        haveI : IsLocallyNoetherian (Spec (CommRingCat.of ℤ)) := inferInstance
    ```

    replacement:

    ```lean
        haveI : IsNoetherianRing (CommRingCat.of (ULift.{uz} ℤ)) := inferInstanceAs (IsNoetherianRing (ULift.{uz} ℤ))
        haveI : IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{uz} ℤ))) := inferInstance
    ```
  - line 80 here:
    FLT text (universe-0 port):

    ```lean
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ) ι F
    ```

    replacement:

    ```lean
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ)) ι F
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`:
for a Hilbert polynomial `P` there is `D₀` such that for every `m ≥ D₀` there are a scheme `Hilb` with
a morphism `p : Hilb ⟶ Spec (ULift ℤ)` (FLT: `Spec ℤ`) and bijections `pt A` between points with
Hilbert function `hilbertFunctionOf n P m` over `A` and morphisms `Spec A ⟶ Hilb`, such that: points
are stable under base change; `y.I` is the extension of `x.I` iff `pt B y = Spec φ ≫ pt A x`; every
`pt A x` lies over the structure morphism of `Spec A`; `p` is proper and locally of finite
presentation; every finite set of points of `Hilb` lies in an affine open; and `p` factors through a
closed immersion into `ℙᴺ` over `ULift ℤ`.

Proof. From the ported
`HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf`, set
`p = ι ≫ ProjSpace.π (ULift ℤ) N`. The converse of naturality uses injectivity of `pt B` and
stability under base change. The structure-morphism equation holds because `Spec (ULift ℤ)` is
terminal (`specULiftZIsTerminal.hom_ext`). Properness and local finite presentation come from the
closed immersion into the proper, finitely presented projective space over the noetherian ring
`ULift ℤ`, and the affine-open property from the ported
`exists_isAffineOpen_forall_mem_of_isAffineHom_proj`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj` (same contribution).
Other project modules imported: `Langlands.AlgebraicGeometry.ULiftIntAlgebra` (same contribution).
Other imports: `Mathlib`.
