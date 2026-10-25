# Whittaker type from a nonzero spanning functional

Author: Worker 184.

The closed proposition
`Langlands.RankinSelberg.WhittakerTypeFromMultiplicityStatement.{uF,uV}`
states an internal derived algebraic adapter into the existing
`Langlands.RankinSelberg.IsOfWhittakerType` predicate of
[AnalyticStatement](AnalyticStatement.md). This module defines the proposition;
it does not prove it.

The field `F : Type uF` has `Field F` and `TopologicalSpace F` instances.
For every `n : ℕ`, the group is `Langlands.GeneralLinear (n + 1) F`.
The character `θ : upperUnipotent (n + 1) F →* ℂˣ` is arbitrary.
The representation carrier `V : Type uV` has `AddCommGroup V` and
`Module ℂ V` instances, with `uF` and `uV` independent. For every
representation `π` on this carrier, the hypotheses are:

- `Representation.IsIrreducible π`;
- `IsAdmissible π`, using the existing predicate, which includes smoothness;
- existence of `ℓ : Whittaker.functionals (upperUnipotent (n + 1) F) θ π`
  with `ℓ.val ≠ 0` such that every element `ℓ'` of this full functional
  submodule equals `c • ℓ` for some `c : ℂ`.

The conclusion is exactly `IsOfWhittakerType n θ π`: admissibility, finite
generation of `π.asModule` over
`MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F)`, and
`Nonempty (Whittaker.functionals (upperUnipotent (n + 1) F) θ π ≃ₗ[ℂ] ℂ)`.
Neither finite generation nor this linear equivalence is a hypothesis.
There is no finite-dimensionality assumption on `V`.

The provenance is elementary algebra applied to the existing Library
definitions, rather than a separate assertion attributed to the original
analytic literature. The intended derivation has two steps. First, Mathlib's
`Representation.irreducible_iff_isSimpleModule_asModule` identifies
irreducibility with simplicity of the group-algebra module. A nonzero vector
in a simple module generates it, so the module is finitely generated over
the group algebra. Second, the complex linear map `c ↦ c • ℓ` onto the
functional space is surjective by the scalar-multiple hypothesis and
injective because `ℓ.val ≠ 0`. Its inverse supplies the linear equivalence
in the conclusion. Admissibility passes through unchanged.

This is conditional packaging. It does not prove multiplicity one, existence
of a nonzero Whittaker functional, or genericity of square-integrable
representations. Those mathematical inputs must be supplied separately in
applications. The arbitrary character allows both
`Whittaker.standardCharacter ψ n` and
`Whittaker.inverseStandardCharacter ψ n`; the statement imposes no
continuity, nontriviality, or standard-character assumption on `θ`.
