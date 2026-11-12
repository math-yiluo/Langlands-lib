# Whittaker multiplicity at most one over every nonarchimedean local field

Author: Worker 5089. This module defines one proposition,
`Langlands.Whittaker.LocalFieldMultiplicityOneStatement` (universes `uF`, `uV`).
It is a statement only: nothing here proves it, and no declaration assumes it.

## Statement

For every field `F : Type uF` with `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and Mathlib's `IsNonarchimedeanLocalField F`, every
`n : ℕ`, every complex vector space `V : Type uV`, every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F` and every representation
`π : Representation ℂ (GeneralLinear (n + 1) F) V` with `IsAdmissible π` and
`Representation.IsIrreducible π`:

```text
∀ ℓ₁ ℓ₂ : glFunctionals ψ n π, ℓ₁.val ≠ 0 →
  ∃! c : ℂ, ℓ₂ = c • ℓ₁.
```

- The field is an arbitrary nonarchimedean local field: `IsNonarchimedeanLocalField`
  bundles a valuative topology, local compactness and a nontrivial valuation, so
  finite extensions of `ℚ_p` and Laurent-series fields `𝔽_q((t))` are both included.
  There is no restriction to `PadicField`. The field and carrier universes are
  independent.
- `GeneralLinear (n + 1) F` is the actual matrix group `GL_(n+1)(F)` with the
  topology induced by `F`; positive rank is written `n + 1`, so rank one (`n = 0`)
  is included.
- `IsAdmissible π` is the published smoothness plus finite-dimensionality of the
  fixed vectors of every open subgroup. `V` carries no topology.
- `HarmonicAnalysis.UnitaryAdditiveCharacter F` bundles continuity, unit-circle
  values and nontriviality of `ψ`.
- `glFunctionals ψ n π` is the published space of linear forms `λ` on `V` with
  `λ(π(u) v) = θ(u) λ(v)` for every upper unitriangular `u`, where
  `θ(u) = ψ(Σ_i u_(i,i+1))` is `standardCharacter ψ n`.

The equality `ℓ₂ = c • ℓ₁` is in the functional submodule; its subtype inclusion
identifies it with equality of the underlying linear forms. No subgroup,
character, functional space or representation predicate is redefined.

This is the same proposition as the published
`Langlands.Whittaker.MultiplicityOneStatement`, with its quantification over
`p`, `Fact p.Prime` and `F : PadicField.{uF} p` (with `F.canonicalNormedField`)
replaced by quantification over every nonarchimedean local field with an
arbitrary topology satisfying `IsNonarchimedeanLocalField`. It uses the same
field context as `Langlands.Whittaker.MirabolicRestrictionInjectivityStatement`.

### Equivalent form

The scalar form expresses multiplicity **at most one**. If `glFunctionals ψ n π`
is zero, no `ℓ₁` satisfies the premise and the assertion is vacuous. If `ℓ₁` is
nonzero, dimension at most one says that `ℓ₁` spans the space, and nonvanishing
of `ℓ₁` makes the scalar unique. Conversely, the stated spanning property forces a
nonzero functional space to be one-dimensional. Genericity is not assumed and no
nonzero functional is asserted to exist.

## Source correspondence

I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n, F),
where F is a non-Archimedean local field*, Russian Math. Surveys 31:3 (1976),
1–68. Registered source `bernstein-zelevinsky-1976-representations-gln`, file
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
SHA-256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
PDF page numbers coincide with the printed page numbers.

- 3.1 (page 28): `F` is a locally compact non-discrete field with a
  non-Archimedean valuation. No characteristic restriction is made.
- 5.1 and 5.5 (pages 44–45): `U = U_n` is the upper unitriangular group;
  every character of `U` has the form `θ(a_1, …, a_(n-1))(u) = ψ_0(Σ a_i u_(i,i+1))`
  for a fixed nontrivial additive character `ψ_0`.
- 5.6 (page 45): `θ(a_1, …, a_(n-1))` is non-degenerate when every `a_i ≠ 0`.
  `standardCharacter ψ n` is `θ(1, …, 1)` for `ψ_0 = ψ`.
- 5.7 (page 45): an algebraic representation `(π, G, E)` is non-degenerate when
  `E_(U,θ) ≠ 0`, where `E_(U,θ)` is the quotient of `E` by the span of the
  vectors `π(u) v − θ(u) v` (2.30).
- 5.16 (page 50), proved in §7 (pages 57–60) following Gelfand and Kazhdan:
  "Let `G = G_n` and let `(π, G, E)` be a non-degenerate, irreducible, admissible
  representation. Then `dim E_(U,θ) = 1` for any non-degenerate character `θ` of
  `U`."

`glFunctionals ψ n π` is the algebraic dual of `E_(U,θ)` for `θ = θ(1, …, 1)`.
If `π` is non-degenerate, Theorem 5.16 makes this dual one-dimensional, which is
the scalar statement. If `π` is degenerate, `E_(U,θ) = 0`, the dual is zero, and
the scalar statement holds vacuously. The Lean statement is therefore exactly
Theorem 5.16 for the standard character, written in the dual, scalar form. The
rank is `n + 1` instead of BZ76's `n`.

No errata note for this source was found in the published notes
(`notes/errata/`).

## Imports

`Langlands.Representation.Whittaker.GeneralLinear` (`standardCharacter`,
`glFunctionals`), `Langlands.Representation.Smooth.Definitions` (`IsAdmissible`),
`Mathlib.NumberTheory.LocalField.Basic` (`IsNonarchimedeanLocalField`) and
`Mathlib.RepresentationTheory.Irreducible` (`Representation.IsIrreducible`).

## Use

The proof of `Langlands.Whittaker.MirabolicRestrictionInjectivityStatement`
(Task 5546) uses this multiplicity-one statement over arbitrary nonarchimedean
local fields to show that the mirabolic kernel of a Whittaker functional has no
Whittaker coinvariants.
