# The per-polynomial Hilbert schemes are H-projective

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705),
as part of the proof of
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement`. The
operator's answer to request `98389b48910e54088e0e2b2ba6aaad9c` allows such
prerequisite proofs to stay under Task 5705.

## Source and licence

The main theorem of this module is an adapted copy of the theorem
`P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP.main`
of the Library module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`
(lines 313–780 there). That module is a port of the file of the same name in the
Anthropic Lean formalization of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; literature id
`anthropic-flt-complete-lean-source-6e837e75`).

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of
the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.
The header comment of the Lean file records the origin and that the file is
modified. The modifications are listed below.

## What is proved

```lean
theorem Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.exists_isHProjective_hilbertPolynomial_piece
    (S : Type uz) [CommRing S] {X : Scheme.{uz}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X)
    (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f) (P : Polynomial ℚ) :
    ∃ (C : Scheme.{uz}) (πC : C ⟶ Spec (CommRingCat.of S)) (pt : …),
      (naturality of pt) ∧ (surjectivity of pt) ∧ (injectivity of pt up to isomorphism) ∧
      IsProper πC ∧ LocallyOfFinitePresentation πC ∧ IsHProjective πC
```

The data and the first five conclusions are exactly those of `HilbP.main`, which
is the Library theorem
`AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`.
The scheme `C` represents, on affine tests `Spec S'` over `Spec S`, the closed
subschemes of `X ×_S Spec S'` that are flat and locally of finite presentation
over `Spec S'` and whose geometric fibres have Hilbert polynomial `P` (measured
by `geomFibreH0Finrank` of the tensor powers of the pullback of `𝓛X`). The
classifier `pt` is natural for base change along ring maps, surjective, and
injective up to isomorphism over `X ×_S Spec S'`. The morphism `πC` is proper
and locally of finite presentation.

The new conclusion is `IsHProjective πC` (Library
`Langlands.AlgebraicGeometry.IsHProjective`): there is a closed immersion
`C ⟶ ProjectiveSpace S N` for some `N`, compatible with the morphisms to
`Spec S`.

## Helper lemma

`isHProjective_πHS`: let `H` be a scheme over `Spec (ULift ℤ)` with a closed
immersion `ιP : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift ℤ))`
satisfying `ιP ≫ ProjSpace.π (ULift ℤ) N = pH`. Then the base change
`πHS H pH S : H ×_{ULift ℤ} Spec S ⟶ Spec S` (the abbreviation `πHS` of the
source module, `pullback.snd` of `pH` and `Spec (ULift ℤ → S)`) is H-projective.
The FLT `Proj` of the polynomial grading and `ProjSpace.π` are, by definition,
the Library `ProjectiveSpace (ULift ℤ) N` and `projectiveSpaceToSpec`; the
proof uses this definitional equality and then the Library theorem
`IsHProjective.of_isPullback` (module `ProjectiveSpace.BaseChange`) for the
chosen pullback square. The algebra structure of `S` over `ULift ℤ` is the local
instance `Langlands.ULiftInt.algebra`, as in the source module.

## Changes against the Library text of `HilbP.main`

The proof is the proof of `HilbP.main` with these changes.

1. The theorem is renamed `exists_isHProjective_hilbertPolynomial_piece` and
   placed in the namespace `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily`
   (the source namespace `…HilbP` is opened for its local definitions and
   lemmas, such as `HS`, `πHS`, `ptHS`, `hnatHS` and `emb`). The
   conclusion gets the extra conjunct `IsHProjective πC`.
2. In the positive case (some field `K` and homogeneous ideal with Hilbert
   polynomial `P` exist), the FLT theorem
   `HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`
   provides the graded Hilbert scheme `H` of `ℙⁿ` over `ULift ℤ` together with a
   closed immersion `ιP` into `Proj (ULift ℤ)[x_0, …, x_NP]` over `ULift ℤ`. The
   source discards this last clause with `-`; here it is kept as
   `NP, ιP, hιP, hιPπ`.
3. The source constructs `C` with a closed immersion `ιC : C ⟶ HS H pH S` and
   sets `πC := ιC ≫ πHS H pH S`. The new conjunct is proved by composing `ιC`
   with the closed immersion `i' : HS H pH S ⟶ ProjectiveSpace S N'` given by
   `isHProjective_πHS`. A composite of closed immersions is a closed immersion.
4. In the negative case (no such ideal exists), the source takes `C = ∅`. The
   new conjunct is proved with the empty morphism `Scheme.emptyTo` into
   `ProjectiveSpace S 0`, a closed immersion, and its compatibility with the
   morphisms to `Spec S` holds because `∅` is initial.
5. The `refine` steps that build the conclusion get one more `?_` for the new
   conjunct (two lines).

The rest of the module is unchanged text of the source module: the imports (two
are added: `Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange` and the source
module itself), the options `maxHeartbeats`, `synthInstance.maxHeartbeats`,
`backward.isDefEq.respectTransparency.types false`, the `attribute [-instance]` and
`attribute [-simp]` lines, the `open` lines and the local instance
`MvPolynomial.gradedAlgebra`. The option `linter.style.haveILetI false` is set
because the copied proof uses `haveI` and `letI` throughout.

## Dependencies

Mathlib, the ported FLT modules imported by the source module, the source module
itself, `Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange` and
`Langlands.AlgebraicGeometry.ULiftIntAlgebra`. No new axioms and no new
definitions.
