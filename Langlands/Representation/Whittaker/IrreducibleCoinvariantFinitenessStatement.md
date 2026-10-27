# Finite twisted upper-unipotent coinvariants of irreducible representations

Authors: Worker 11 (draft) and Worker 784 (source check and submission).

`Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement.{uF,uV}` states
the finiteness part of Bernstein–Zelevinsky (1976), Theorem 5.21 (attributed
there to Kazhdan), printed p.51, specialized to finite extensions of the p-adic
numbers. It is a `Prop`-valued definition. This module supplies no proof of the
proposition.

For every prime `p`, finite extension `F : PadicField.{uF} p` of Mathlib's
`Padic p`, supplied
`T : F.TopologicalData`, natural number `n`, and complex representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`, the statement assumes that
`ρ` is smooth and irreducible. For every group homomorphism
`θ : GeneralLinear.upperUnipotent n F.Carrier →* ℂˣ` whose complex values form a
locally constant function, it concludes that the existing character-localized
coinvariant quotient

```lean
Jacquet.Localization.Coinvariants ρ (GeneralLinear.upperUnipotent n F.Carrier) θ
```

is a finite-dimensional complex vector space.

The local `letI := T.topology` installs precisely the supplied field topology
before smoothness and local constancy are formed. The matrix group and its
upper-unipotent subgroup inherit the matrix-unit and subspace topologies. No
independent topology on `V` is required.

## Actual objects

- `Langlands.GeneralLinear.upperUnipotent n F.Carrier` is the existing subgroup
  of upper unitriangular matrices of `GL_n(F)`: the subgroup `U` of BZ76 §5.1,
  printed p.44, with indices starting at zero.
- `Langlands.Jacquet.Localization.Coinvariants ρ U θ` is the existing quotient
  of `V` by `Jacquet.Localization.relations ρ U θ`, the complex span of the
  vectors `ρ u v - θ u • v` for `u ∈ U` and `v ∈ V`. This is the space
  `E_{U,θ} = E / E(U,θ)` of BZ76 Definition 2.30, printed p.24.
- `IsSmooth ρ` is the existing smoothness predicate: every vector has an open
  stabilizer. This is BZ76's notion of an algebraic representation (§2.1,
  printed p.15).
- `ρ.IsIrreducible` is Mathlib's `Representation.IsIrreducible`, that is,
  `IsSimpleOrder (Subrepresentation ρ)`: the representation is nonzero and has
  no invariant subspaces other than `0` and `V`. Mathlib's
  `Representation.irreducible_iff_isSimpleModule_asModule` identifies it with
  simplicity of `ρ.asModule` over the group algebra. This is BZ76's
  irreducibility for algebraic representations.
- A character of an l-group is, in BZ76 §1.19, printed p.11, a locally constant
  homomorphism into the multiplicative group of complex numbers. The hypothesis
  `IsLocallyConstant (fun u => (θ u : ℂ))` with `θ` a monoid homomorphism into
  `ℂˣ` expresses exactly this.

## Scope

The source proves the explicit bound `dim E_{U,θ} ≤ n!`. This statement keeps
only finite dimensionality, which is what BZ76 Corollary 5.22, printed p.51,
uses for (1) implies (3) and what the Library target
`Langlands.Whittaker.MirabolicFiniteLengthStatement` needs. The bound itself is
not stated here.

No admissibility, central character, genericity, cuspidality or finite complex
dimension is assumed. In the source every irreducible algebraic representation
of `GL_n(F)` is admissible (BZ76 Theorem 3.25, printed p.35); the Library obtains
admissibility of an irreducible smooth representation through the existing
`Langlands.CuspidalSupport.cuspidalEmbedding`, so a proof must derive it rather
than assume it. All `n : ℕ` are quantified. For `n = 0` the group and its
upper-unipotent subgroup are trivial, `θ` is trivial and the coinvariant
quotient is `V` itself, which is one-dimensional by irreducibility; this is
consistent with the source bound `0! = 1`. The field universe `uF` and carrier
universe `uV` are independent.

## Source proof (not formalized here)

BZ76 states Theorem 5.21 on printed p.51 and says it is proved in §7. A proof of
this target must supply the mathematics; the following outline records the
source route as proof obligations, not premises. One embeds `ρ` into a
representation parabolically induced from a cuspidal representation of a
Levi subgroup; exactness of twisted coinvariants (BZ76 Proposition 2.35,
printed p.25) reduces the claim to the induced representation; a finite
filtration of the induced representation indexed by the double cosets
`P \ G / U` (finitely many by the Bruhat decomposition) reduces it to twisted
coinvariants of the cuspidal inducing data; and cuspidality gives the
finiteness there. The source's own bound counts these double-coset
contributions.

## Sources and reading

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
  (1976), 1–68. Registered source:
  `bernstein-zelevinsky-1976-representations-gln`, retained Central-Library PDF
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Printed pages equal one-based PDF pages. Read §1.19 (p.11), §2.1 (p.15), Theorem 3.25 (p.35),
  §§2.30–2.35 (pp.24–25), §5.1 (p.44) and Theorem 5.21 with Corollary 5.22
  (p.51).

No matching erratum note was found in the project or Library errata locations.
