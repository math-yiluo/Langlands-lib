# Scalar gauges of sections from trivialized tensor powers

Let `X` be a scheme and `L` a module sheaf on `X`. Two tensor powers of `L` are
in the Library. The monoidal one, `L.tensorPowFLT n`, comes from the ported
Anthropic FLT development and is left-associated: `L^(n+1) = L^n ⊗ L`. The
explicit one, `Langlands.Scheme.Modules.tensorPow L n`, is right-associated and
uses the sheafified sectionwise tensor product: `L^(n+1) = L ⊗ L^n`.

- The shared `monoidalTensorIso A B` is the inverse of the FLT comparison
  `Scheme.Modules.tensorIsoSheafify`. It identifies the monoidal tensor product
  with the explicit one.
- `tensorPowComparison L n` is an isomorphism between the two tensor powers,
  built by induction on `n`. The case `n = 0` is the identity of the structure
  sheaf. In the inductive step the factors are swapped by the symmetry, the
  tensor products are compared by the inverse FLT comparison, and the inductive
  isomorphism is applied in the second factor. No coherence with other
  comparison maps is asserted.

Fix a trivialization `τ : L.tensorPowFLT n ≅ 𝟙_ X.Modules`.

- `gauge τ s` is a function on an open `U`, defined for a section `s` of `L`
  over `U`. It sends the `n`-th tensor power section
  `Scheme.Modules.tensorPowSectionFLT s n` through `τ`. Sections of the monoidal
  unit over `U` are functions on `U`.
- `gauge_restrict` says that gauges commute with restriction to smaller opens.
  It uses the naturality of `τ` and the restriction formula for tensor power
  sections.
- `gauge_smul` states `gauge τ (g • s) = g ^ n * gauge τ s` for a function `g`
  on `U`. It uses the published FLT homogeneity of tensor power sections and
  the linearity of `τ`.
- `isUnit_gauge` states that the gauge of a local generator (`IsFrameOn s U`)
  is a unit. The `n`-th tensor power of a generator is a generator (published
  FLT lemma), isomorphisms preserve generators, and a generator `w` of the unit
  sheaf on `U` satisfies `g * w = 1` for some `g`.

## Provenance

This is an internal construction. In the torsion bracket argument for eventual
quasi-projectivity of fine moduli schemes of ordinary polarized full-level data
(module `TorsionBracketMapReduction`) the gauge is applied to the published trivialization
`Datum.torsionEvaluationLinePowerIso` of the `n`-th power of a torsion
evaluation line, transported by `tensorPowComparison`. It turns a choice of
local generators of the evaluation lines into scalars whose change under
rescaling of the generators is the `n`-th power of the scaling unit. Using
the triviality of these `n`-th powers is the route by which
`TorsionBracketMapReduction` derives `TorsionBracketMapStatement`.
