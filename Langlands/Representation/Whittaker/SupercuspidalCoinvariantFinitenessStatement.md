# Finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations

Author: Worker 784.

`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement.{uF,uV}` is a
`Prop`-valued definition. It states that the twisted upper-unipotent
coinvariants of an irreducible supercuspidal representation of `GL_m(F)` are
finite-dimensional, for every character. This is the single-block case of the
cuspidal coefficient assertion in Bernstein–Zelevinsky (1976), Theorem 7.12,
step (5), printed p.61. That step refers back to §5.18 with Proposition 5.15(a)
and Theorem 5.16 (printed pp.49–50). The source proves the stronger
dimension-zero-or-one claim, and only finite dimension is stated here.

This module publishes a statement and nothing more. It contains no proof of
the proposition and does not assume it anywhere. Publishing the statement does
not establish it. A proof is a separate later contribution (see
"Successor proof" below).

## Exact statement

For every prime `p` with `[Fact p.Prime]`, every finite extension
`F : PadicField.{uF} p` of Mathlib's `ℚ_p`, every supplied
`T : F.TopologicalData`, and every `m : ℕ`, the statement assumes `0 < m` and
then installs `letI := T.topology`. Then for every
`σ : SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier)` it assumes

- `σ.IsIrreducible`, and
- `GeneralLinear.IsSupercuspidal σ.representation`.

For every monoid homomorphism
`η : GeneralLinear.upperUnipotent m F.Carrier →* ℂˣ` with
`IsLocallyConstant (fun u => (η u : ℂ))`, it concludes

```lean
FiniteDimensional ℂ
  (Jacquet.Localization.Coinvariants σ.representation
    (GeneralLinear.upperUnipotent m F.Carrier) η)
```

The binder order is
`∀ p [Fact p.Prime] F T (m : ℕ), 0 < m → letI := T.topology; ∀ σ, σ.IsIrreducible → GeneralLinear.IsSupercuspidal σ.representation → ∀ η, IsLocallyConstant (fun u => (η u : ℂ)) → FiniteDimensional …`.
The field universe `uF` and the carrier universe `uV` are independent
parameters. The coefficient field `ℂ` lies in `Type 0`, which is the first
universe argument of `SmoothRep`.

## Actual objects

All objects are existing Library declarations, imported unchanged by their
Lean names. No new construction is introduced.

- `GeneralLinear m F.Carrier` (`Langlands.Group.GL.Basic`) is Mathlib's
  `Matrix.GeneralLinearGroup (Fin m) F.Carrier`, the group of invertible
  `m × m` matrices over `F.Carrier`. With `T.topology` installed it carries the
  instance-inferred topology. That is Mathlib's units topology over the
  entrywise matrix topology, the same instance as
  `T.generalLinearTopology m` in `Langlands.Group.GL.Padic`. This is
  `G = G_m = GL(m,F)` in BZ76 §3.1.
- `GeneralLinear.upperUnipotent m F.Carrier` (`Langlands.Group.GL.UpperUnipotent`)
  is the subgroup of upper triangular matrices whose diagonal entries are all
  `1`. This is the source's `U = U_m` (BZ76 §§3.2 and 5.1, printed pp.29 and 44).
  It carries the subspace topology. Local constancy of `η` refers to this
  topology.
- `SmoothRep.{0,uF,uV} ℂ G` (`Langlands.Representation.Category.Basic`) is the
  full subcategory of Mathlib's `Rep ℂ G` on the objects in which every vector
  has an open stabilizer. These are the algebraic representations of BZ76
  §2.1(a), printed p.15. No topology is placed on the carrier, and no finite
  dimension is required.
- `σ.IsIrreducible` is `SmoothRep.IsIrreducible`, which is Mathlib's
  `Representation.IsIrreducible` of the underlying action. It says the lattice
  of invariant subspaces is simple, so the carrier is nonzero and has no
  invariant subspaces other than `0` and itself. This is BZ76's
  irreducibility (printed p.15).
- `Jacquet.Localization.Coinvariants ρ U η` (`Langlands.Representation.Jacquet.Localization`)
  is the quotient of the carrier by `Jacquet.Localization.relations ρ U η`.
  That is the complex span of the vectors `ρ u v - (η u : ℂ) • v` for `u ∈ U`
  and `v` in the carrier.
- A character of an l-group is, in BZ76 §1.19 (printed p.11), a locally
  constant homomorphism into `ℂ^*`. The monoid homomorphism `η` with
  `IsLocallyConstant (fun u => (η u : ℂ))` is exactly such a character of
  `U_m`.

The local `letI := T.topology` installs exactly the supplied field topology
before smoothness, admissibility, supercuspidality and local constancy are
formed.

### Quotient sign convention

The relations are `ρ u v - (η u : ℂ) • v`, with `η` itself and not its inverse.
In the quotient, `u ∈ U_m` therefore acts on every class by the scalar
`η u`. This is the source's convention in Definition 2.30 (printed p.24):
`E(H,θ)` is spanned by the vectors `π(h)ξ - θ(h)ξ`, and `E_{H,θ} = E/E(H,θ)`.
Here `H = U_m`, `θ = η` and `E` is the carrier of `σ`. The conclusion is about
`E_{U,θ}` itself. It is not about its dual, which the source describes in 2.30
as the functionals `ξ*` with `π*(h)ξ* = θ^{-1}(h)ξ*`. Because every locally
constant character is quantified, the statement would be equivalent with the
inverse convention. The Lean uses the convention above.

## The supercuspidality predicate

`GeneralLinear.IsSupercuspidal ρ` (`Langlands.Representation.Classification.Supercuspidal`)
is defined as

```lean
IsAdmissible ρ ∧
  ∀ B : BlockShape n, B.parabolic F ≠ ⊤ →
    ∀ g : GeneralLinear n F,
      Subsingleton (Jacquet.Coinvariants ρ (B.conjugateUnipotent g))
```

Here:

- `IsAdmissible ρ` (`Langlands.Representation.Smooth.Definitions`) means
  smoothness together with `Module.Finite ℂ` of the fixed vectors of every
  open subgroup. This is BZ76's admissibility, §2.1(b), printed p.15: for every
  open subgroup `N`, the `N`-invariant vectors form a finite-dimensional space.
- `B : BlockShape n` is an ordered list of positive block sizes with sum `n`.
  `B.parabolic F` is the standard block upper triangular subgroup, and
  `B.unipotentSubgroup F` is its block-unipotent radical, the kernel of the
  projection to the diagonal blocks. `B.conjugateUnipotent g` is the image of
  that radical under conjugation by `g`.
- `Jacquet.Coinvariants ρ N` is the ordinary quotient by the span of
  `ρ(u)v - v` for `u ∈ N`. Vanishing means that this quotient is a
  subsingleton.

### Relation to BZ76 cuspidality

BZ76 §3.18 (printed p.34) calls a representation `π` of `G_α`
*quasi-cuspidal* if `r_{β,α}(π) = 0` for all `β ≤ α` with `β ≠ α`. It says
that "an admissible quasi-cuspidal representation is called cuspidal". By
§3.12(b) (printed p.32), `r_{β,α}(π)` is the natural representation of `G_β`
on the ordinary coinvariants `E_{U_β(α)}`, with no normalizing twist. Here
`U_β` is the horospherical subgroup of §3.5 (printed p.30). For one block
`α = (m)` the partitions `β` are the ordered positive block shapes of `m`, and
`U_β` is the standard block-unipotent radical `B.unipotentSubgroup F`.

So for `GL_m`, BZ76 cuspidality says: `σ` is admissible, and the ordinary
coinvariants of every standard block-unipotent radical with at least two
blocks vanish. `IsSupercuspidal` differs from this in two ways, neither of
which changes its content:

- **Conjugates.** `IsSupercuspidal` also quantifies over all conjugates
  `g U_β g⁻¹`. The published theorem `GeneralLinear.isSupercuspidal_iff_standard`
  (module `Langlands.Representation.Classification.SupercuspidalContragredientAux`)
  proves that `IsSupercuspidal ρ` is equivalent to
  `IsAdmissible ρ ∧ ∀ B, B.parabolic F ≠ ⊤ → Subsingleton (Jacquet.Coinvariants ρ (B.unipotentSubgroup F))`.
  So the extra conjugates add nothing.
- **Properness.** Properness is expressed as `B.parabolic F ≠ ⊤` and not as
  "`B` has at least two blocks". One-block shapes give the whole group
  (published `GeneralLinear.BlockShape.singleBlock_parabolic_eq_top`, module
  `Langlands.Group.GL.SingleBlock`). Shapes with at least
  two blocks give a proper subgroup. That second fact is standard: a matrix
  with a nonzero entry below the diagonal blocks is not block upper
  triangular. It is recorded here for comparison only and is not used by the
  statement.

The published theorem `CuspidalSupport.singleBlockCuspidalityClause` (module
`Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof`) also
identifies `IsSupercuspidal ρ` with the product-Levi cuspidality
`CuspidalSupport.IsLeviCuspidal B (ρ.comp (B.leviEmbedding F.Carrier))` for
one-block shapes `B`.

The Library name "supercuspidal" follows the published `Supercuspidal` pair,
which cites Casselman (1995), §5.1, for this admissible Jacquet-vanishing
condition. For `GL_m` in this statement the predicate is BZ76's "cuspidal" by
the comparison above. No deeper comparison theorem, such as compact support
of matrix coefficients, is involved. The pair `σ.IsIrreducible`,
`IsSupercuspidal σ.representation` is exactly the defining property of the
existing full subcategory `GeneralLinear.SupercuspidalRep`.

## Scope and what is not assumed

The statement covers all positive ranks `m`, including `m = 1`, every
irreducible supercuspidal `σ`, and every locally constant character `η`. In
particular `η` may be trivial or degenerate.

The statement does not assume any of the following:

- genericity or non-degeneracy of `σ` (BZ76 §5.7) or of `η` (BZ76 §5.6);
- the existence of a nonzero Whittaker functional, or a chosen additive
  character;
- unitarity or a central character;
- finite dimension of the carrier of `σ`;
- a tensor factorization;
- any multiplicity-one result, in particular not the unproved Library
  proposition `Langlands.Whittaker.MultiplicityOneStatement`;
- any other theorem-valued premise.

Rank `0` is excluded by `0 < m`, as the task specifies. The boundary cases are
remarks only and are not part of the statement:

- **Rank one.** `upperUnipotent 1 F.Carrier` is trivial, so `η` is trivial and
  the coinvariant quotient is the whole carrier. The only block shape of `1`
  has one block, so `IsSupercuspidal` reduces to admissibility. The rank-one
  case therefore says that an irreducible admissible representation of
  `GL_1(F)` is finite-dimensional. In the source this is Theorem 5.16 for
  `n = 1`: dimension one, since `U_1` is trivial and its only character is
  vacuously non-degenerate.
- **Rank two and higher.** An irreducible supercuspidal representation of
  `GL_m(F)` with `m ≥ 2` is infinite-dimensional (a standard fact, not
  formalized here). This is why finite carrier dimension must not be assumed.

## Relation to the source assertion

In the proof of Theorem 7.12 (printed pp.60–61), step (5) reads, for an
irreducible cuspidal representation `(ρ, G_β, V)`:

> Now `U ∩ G_β = ∏ U_{n_i}` and `θ^{w⁻¹}|_{U ∩ G_β} = ∏ θ_i`, where `θ_i` is a
> character of `U_{n_i}`. Recalling that `ρ` is irreducible and cuspidal, we
> see, exactly as in 5.18, that if at least one of the `θ_i` is degenerate,
> then `V_{∏U_{n_i}, ∏θ_i} = 0`. But if all the `θ_i` are non-degenerate, then
> `dim V_{∏U_{n_i}, ∏θ_i} = 1`.

Take the single-block case `β = (m)`, so that `r = 1`, `G_β = G_m` and
`∏ U_{n_i} = U_m`. The assertion then becomes: for an irreducible cuspidal
`(ρ, G_m, V)` and a character `θ` of `U_m`, `V_{U_m,θ} = 0` if `θ` is
degenerate and `dim V_{U_m,θ} = 1` if `θ` is non-degenerate. "Exactly as in
5.18" refers to these source facts:

- **§5.18** (printed p.50): "If `π` is cuspidal and irreducible, then
  `π|_P = τ_P^0`. The proof follows from Proposition 5.15a) and Theorem 5.16."
  The same section says that a quasi-cuspidal representation is
  non-degenerate.
- **Proposition 5.15(a)** (printed p.49): for a representation of the mirabolic
  `P`, vanishing of `E_{U_β}` for every non-trivial horospherical `U_β` implies
  `E_{U,θ} = 0` for every degenerate `θ`. This is the implication (2) ⇒ (3).
  The proof notes that a degenerate `θ` is trivial on some non-trivial
  `U_β ⊂ U`, so `E_{U,θ}` is a quotient of `E_{U_β}`.
- **Theorem 5.16** (printed p.50, proved in §7): for a non-degenerate,
  irreducible, admissible representation of `G_n`, `dim E_{U,θ} = 1` for every
  non-degenerate character `θ` of `U`.

By §§5.5–5.6 (printed p.45), every character of `U_m` has the form
`θ(a_1, …, a_{m-1})` and is either non-degenerate (all `a_i ≠ 0`) or
degenerate. Hence the source gives `dim V_{U_m,θ} ≤ 1` for **every** character
`θ`. Since any space of dimension at most one is finite-dimensional, the
statement here follows from that assertion. It is strictly weaker: it states
only **finite dimension**. The following source assertions are not stated
here:

- the bound `dim ≤ 1`;
- vanishing for a degenerate character;
- dimension exactly one for a non-degenerate character.

The quantification over every locally constant `η`, rather than over the
source's parametrized characters `θ(a_1, …, a_{m-1})`, does not use the
classification of §5.5. That classification is needed only to compare the
statement with the source's case division.

## Successor proof and ownership boundaries

The proof is not supplied here. Worker 288 owns the exact proof successor,
which will be published after this statement is in the Library. The following
are obligations and boundaries for that proof. They are not premises of the
statement.

- **Independence.** The proof must not depend, directly or transitively, on
  `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` or its parent
  proof task 5ab445dc-d2b4-4072-80d1-6370870a4a26. It must not depend on the
  Levi target `Langlands.Whittaker.LeviCuspidalCoinvariantFinitenessStatement`
  of task 3ff5c8fb-397c-4345-bcb3-5d98a0993d18. It must also avoid any mirabolic
  finite-length route that uses that parent finiteness, including task
  5428fe2c-013c-482d-aa6e-7df43e7191aa, unless an independently published route
  is verified.
- **Derivatives.** Vanishing of the proper positive derivatives and finrank
  one of the top derivative of an irreducible supercuspidal representation are
  the published but unproved statement
  `Langlands.Classification.SupercuspidalDerivatives`
  (module `Langlands.Representation.Classification.SupercuspidalDerivativesStatement`,
  BZ77 §4.4, Gelfand–Kazhdan). They and their eventual proof are owned by
  task 8e5b4563-0365-41c7-b134-70f2a0b36292, clause (a). That task is not a
  proved input, and this pair does not duplicate it.
- **Remaining steps.** A proof along the source route still needs three steps
  that neither statement supplies:
  - normalization or conjugacy of an arbitrary locally constant `η`
    (BZ76 §§5.5–5.6);
  - vanishing for degenerate characters (the Proposition 5.15(a) argument,
    from the standard Jacquet vanishing given by `isSupercuspidal_iff_standard`);
  - a comparison of the non-degenerate case with the actual top derivative.
- **Multiplicity one.** `Langlands.Whittaker.MultiplicityOneStatement` is
  unproved and may not be cited as a theorem.

## Consumer

This is a focused prerequisite of proof task
3ff5c8fb-397c-4345-bcb3-5d98a0993d18, whose unchanged target is
`Langlands.Whittaker.LeviCuspidalCoinvariantFinitenessStatement`. According to
that task, the final Levi assembly will use three ingredients:

- the published `Langlands.CuspidalSupport.padicLeviCuspidalFactorization`. It
  gives blocks `A i : GeneralLinear.SupercuspidalRep.{uF,uV}` of positive rank
  `B.size i`, which satisfy exactly this statement's hypotheses at carrier
  universe `uV`;
- the published `Langlands.FiniteTensor.characterLocalizationEquiv`;
- the eventual exact proof of this single-block proposition.

## Sources and reading

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Mathematical
  Surveys 31:3 (1976), 1–68. Registered source:
  `bernstein-zelevinsky-1976-representations-gln`. Central-Library PDF
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`,
  verified for this pair. Printed pages equal one-based PDF pages.

Passages read directly for this pair on 2026-10-29:

- §1.19, p.11 (characters);
- §2.1, p.15 (irreducible, algebraic and admissible representations);
- §§2.30–2.35, pp.24–25 (`E(H,θ)`, `E_{H,θ}` and exactness);
- §§3.2–3.5, pp.29–30 (`U_n`, partitions, `G_α`, horospherical subgroups);
- §3.12, p.32 (the functors `r_{β,α}`);
- §3.18, p.34 (quasi-cuspidal and cuspidal);
- §§5.1–5.7, pp.44–45 (`U_n`, characters of `U_n`, non-degeneracy);
- §§5.12–5.18, pp.48–50 (Corollary 5.14, Proposition 5.15, Theorem 5.16, §5.18);
- §§7.11–7.12, pp.60–61 (step (5) on p.61).

On 2026-10-29 the Library notes and wiki (including `notes/errata/`), the
project literature collection and index, and the Central-Library listing were
searched for errata. No erratum or correction for this source was found.

The supercuspidality predicate itself is documented in its own published pair
`Langlands/Representation/Classification/Supercuspidal.md`, which cites
Casselman (1995), §5.1.
