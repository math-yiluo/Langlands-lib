# Statement: positivity of orbital integrals

The module `Langlands.BaseChange.OrbitalIntegralPositivityStatement` (namespace
`Langlands.BaseChange`) states, as the proposition `OrbitalIntegralPositivityStatement.{u}`,
that the orbital integral of a nonnegative test function at a regular semisimple element where
it is positive is itself positive, for every choice of the measures. The statement is **not
proved** here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL. I.2.4 (printed pp. 14–16): the orbital
  integral `Λ^{G(F)}(f, γ)` over `G_γ(F) \ G(F)` for the quotient of Haar measures;
  II.2.6 (printed p. 66): functions with a central character, compactly supported modulo
  the centre, obtained from compactly supported functions by the averaging map `f ↦ f_ω`,
  and the extension of `Λ^{G(F)}(·, γ)` to them with the same measure `dḡ_γ` on
  `G_γ(F) \ G(F)`; II.6.1 (printed p. 118): the global method of II.6 is carried out for a
  global field `F` of positive characteristic; II.6.3 (printed p. 119): the local orbital
  integral `Λ^{G(F_v)}(·, γ)` on the functions with central character, defined by the
  quotient measure `dg_v/dg_{v,γ}` on `G_γ(F_v) \ G(F_v)`, and the function `f_v^0`,
  supported in `Z¹_v K_v` (`Z¹_v` the image of the norm in the centre) and satisfying
  `f_v^0(z g) = ω_v⁻¹(z)` for `z ∈ Z¹_v`, `g ∈ K_v`; II.6.8 (printed pp. 124–125):
  `Λ^{G(F_v)}(f_v, γ) > 0` for `f_v = f_v^0` at the places outside `S` (HL deduce it from
  `γ ∈ K_v`: "Puisque `γ` appartient à `K_v`, on a [...] `> 0`", p. 124) and, at the places
  of `S ∖ {v₀, v₁}`, for `f_v = (f̃_v)_{ω_v}`, where `f̃_v` is the characteristic function of
  the open compact set `X_v` of the `k⁻¹ x k` with `k ∈ Γ_v` and `x ∈ γ V_{γ,v}`
  (p. 125).

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`) and
`n : ℕ`, and let `GL_n(F)` carry its Borel σ-algebra (introduced locally with
`letI ... := borel _`). Use `open scoped ComplexOrder`, so that `≤` and `<` on `ℂ` are the
partial order with `z ≤ w` iff `w - z` is real and nonnegative. For every Haar measure `μF`
on `GL_n(F)`, every `f : SchwartzBruhat (GL_n(F))` and every `γ : GL_n(F)` such that

- `JacquetLanglands.IsRegularSemisimple γ` (separable characteristic polynomial),
- `0 ≤ f g` for every `g` (so `f` is real and nonnegative), and
- `0 < f γ`,

the following holds, where the coset space `G_γ(F) \ GL_n(F)`
(`QuotientIntegration.LeftQuotient (glCentralizer γ)`, with Task 7416's centralizer
`glCentralizer γ`) carries its Borel σ-algebra (introduced locally with `letI ... := borel _`
and a `BorelSpace` instance `⟨rfl⟩`, as is the σ-algebra of `GL_n(F)`): for every right Haar
measure `μγ` on `glCentralizer γ` (`IsHaarMeasure` and `IsMulRightInvariant`) and every
measure `νγ` on the coset space with `QuotientIntegration.IsCompatible (glCentralizer γ) μF
μγ νγ` (the Library's compatibility of a quotient measure with `μF / μγ`: nonzero, regular,
right invariant, and satisfying the integration formula for compactly supported continuous
functions),

`0 < Langlands.TraceFormula.orbitalIntegral γ νγ f`,

the orbital integral `∫ f(x⁻¹ γ x) dνγ(x)` over `G_γ(F) \ GL_n(F)` of Task 7402. The
conclusion says that this integral is a positive real number.

## Use

In the global comparison of HL II.6.7–II.6.10 (printed pp. 123–126), the orbital integrals of
the global test function `f = ⊗ f_v` at the chosen global regular elliptic norm `γ` must not
vanish. At `v₀` and `v₁` they are nonzero by Tasks 7446 and 7457. At the other places HL use
positivity (II.6.8). HL's setting differs from this statement in two ways: their global
field, and hence every `F_v`, has positive characteristic (II.6.1, printed p. 118: the
result being known in characteristic zero, they assume from then on that `F` has
characteristic `> 0`), and their local test functions have a central character. This
statement keeps the host task's characteristic-zero scope (`CharZero F`) and concerns
compactly supported functions; it does not apply verbatim to HL's functions. It applies to
the characteristic-zero analogues of the compactly supported functions underlying II.6.8:

- at the places of `S ∖ {v₀, v₁}`, HL start from the characteristic function `f̃_v` of the
  open compact set `X_v` of the `k⁻¹ x k` (`k` in a small open compact subgroup `Γ_v`,
  `x ∈ γ V_{γ,v}`), where `V_{γ,v}` is a small open compact neighbourhood of `1` in the torus
  `T(F_v) = G_γ(F_v)` with `γ V_{γ,v}` inside the regular norms (HL ask for `f_v`
  "à support dans `G(F_v)_r ∩ N_v(G(E_v))`"; the openness of the regular norms, statement
  12 (c), `NormNeighbourhoodStatement`, is the corresponding local fact in characteristic
  zero). Over a field of characteristic zero, the characteristic function of an open compact
  set of the same form containing `γ` is compactly supported, nonnegative and equal to `1`
  at `γ`, so this statement gives the positivity of its orbital integral at `γ`. HL's test function is `f_v = (f̃_v)_{ω_v}`, its
  average over `Z¹_v` (II.2.6), which transforms under `Z¹_v` by `ω_v⁻¹` and is compactly
  supported only modulo the centre;
- outside `S`, the analogue is the characteristic function of `K_v = GL_n(o_v)` (compactly
  supported, nonnegative, equal to `1` at `γ ∈ K_v`), to which this statement applies; HL's
  `f_v^0` is supported in `Z¹_v K_v` and transforms under `Z¹_v` by `ω_v⁻¹`, so it is
  compactly supported only modulo the centre.

For the compactly supported functions and for those with a central character HL use the
same local quotient measure `dg_v/dg_{v,γ}` on `G_γ(F_v) \ G(F_v)`, the kind of quotient over
which `orbitalIntegral` integrates: II.2.6 (p. 66) extends `Λ^{G(F)}(·, γ)` to the functions with a central character with the same
measure `dḡ_γ` on `G_γ(F) \ G(F)`, and II.6.3 (p. 119) defines `Λ^{G(F_v)}(·, γ)` on them by
`dg_v/dg_{v,γ}`. The step not formalized here is the passage from the compactly supported
functions to the functions transforming under `Z¹_v` by the central character `ω_v⁻¹`
(from `f̃_v` to `(f̃_v)_{ω_v}`, and from the characteristic function of `K_v` to `f_v^0`).
For `(f̃_v)_{ω_v}`, HL control the central saturation through their choice of `V_{γ,v}`
(p. 124). The second of their conditions is printed as `Z(F_v) V_{γ,v} ∩ O_{G(F_v)}(γ) = {γ}`;
the support argument of p. 125 uses the translated separation
`Z(F_v) γ V_{γ,v} ∩ O_{G(F_v)}(γ) = {γ}`, and the printed form appears to omit the factor
`γ` (for noncentral `γ` and small enough `V_{γ,v}`, `γ` is not in `Z(F_v) V_{γ,v}`). The
translated separation can be arranged by shrinking `V_{γ,v}` about `1`: `O_{G(F_v)}(γ) ∩ T(F_v)` is
finite, and since the image of `γ` in `PGL_n(F_v)` is strongly regular (p. 124), `γ` is
its only point in `Z(F_v) γ`.

## Proof idea (not formalized)

The integrand `x ↦ f(x⁻¹ γ x)` is continuous (`f` is locally constant), nonnegative, and
compactly supported on `G_γ(F) \ GL_n(F)`, because the conjugacy class of a semisimple element
is closed and the orbit map `G_γ(F) \ GL_n(F) → GL_n(F)` is proper onto it. It is positive at
the trivial coset, hence on a nonempty open set of cosets, and a compatible quotient measure
charges every nonempty open set (the Library's `IsCompatible.isOpenPosMeasure`, in
`Langlands/Analysis/Local/QuotientMass.lean`, under its hypotheses on the group). So the
integral is positive.

## Hypotheses

- `CharZero F`, as in Tasks 7416, 7432 and 7446: the Library's `IsRegularSemisimple` asks for
  a separable characteristic polynomial, which is HL's regularity in characteristic zero.
  HL's own use of positivity in II.6.8 is in positive characteristic (II.6.1); the
  statement does not cover that case.
- `γ` regular semisimple: then `G_γ(F)` is a torus and the orbit of `γ` is closed, which makes
  the integrand compactly supported on the coset space.
- `f ≥ 0` everywhere and `f γ > 0`: both are needed; a function of varying sign can have
  vanishing orbital integrals.

## Measures

Every measure is quantified: the statement holds for every Haar measure `μF`, every right Haar
measure `μγ` on the centralizer and every compatible quotient measure `νγ`. Nothing is chosen
or normalized; the positivity does not depend on the normalization.

## Dependencies and names

The module imports Task 7416's `Langlands.BaseChange.OrbitalIntegral` (`glCentralizer`),
Task 7402's `Langlands.TraceFormula.TwistedOrbital` (`orbitalIntegral`), the Library's
`Langlands.Analysis.Local.QuotientMeasure` (`QuotientIntegration.LeftQuotient`,
`QuotientIntegration.IsCompatible`) and `Langlands.HarmonicAnalysis.Basic`
(`SchwartzBruhat`), and Mathlib's `ComplexOrder`, with the names and argument orders cited in
the task.
