# Conductor identity for a cuspidal sigma-lift

`Langlands.BaseChange.CuspidalSigmaLiftConductorStatement` defines the
conductor identity as a proposition with independent universes `u`, `v`,
`uV`, `uW` in that order. The identity remains a proof obligation. The
definition imports the published `Norm`, `TwistedCharacter`,
`CuspidalSigmaLift`, and `ExtensionInvariants` modules. Lean calls the
representations `Π₁` and `Π` below `P₁` and `P`.

## The proposition

Let `F` and `E` be nonarchimedean local fields, in universes `u` and `v`,
with the specified `ValuativeRel` and topological structures. Assume
`CharZero F`, an `F`-algebra structure on `E`, and `IsModuleTopology F E`.
For every `σ : E ≃ₐ[F] E` and `l : ℕ` satisfying `IsCyclicAlgebra σ l`,
the proposition quantifies over the following data.

- An irreducible supercuspidal representation `π` of `GL_(k+1)(F)` on a
  complex vector space `V : Type uV`, with an admissibility proof `hπ`.
- Natural numbers `s`, `k₁` and an equality `h : s * (k₁ + 1) = k + 1`,
  and an irreducible supercuspidal representation `Π₁` of `GL_(k₁+1)(E)`
  on a complex vector space `W₁ : Type uW`.
- An admissible representation `Π` of `GL_(k+1)(E)` on `W : Type uW`,
  with admissibility proof `hP` and the existence of a representation
  equivalence from `Π` to the full normalized orbit product
  `Π₁ × Π₁^σ × ⋯ × Π₁^(σ^(s-1))`. In Lean this product is
  `sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁`, pulled back along
  `(GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom`.
- An intertwining equivalence `A : SigmaIntertwiner σ (k + 1) P` and
  a scalar `c : ℂ` satisfying `IsSigmaLift σ l π hπ P hP A c`.
  The intertwiner identifies `P` with its pullback along
  `entrywiseAut σ (k + 1)`. The six needed topological instances for
  `GL_(k+1)(F)` and `GL_(k+1)(E)` come from the three
  `LocalFieldTopology.generalLinear_*` theorems.
- Natural numbers `f`, `d` satisfying `IsResidueDegree F E f` and
  `IsDifferentExponent F E d`, and a finite set `X` of characters
  `Fˣ →* ℂˣ` with `κ ∈ X ↔ IsNormTrivial E κ` for every `κ`.

Write `a(ρ)` for `Conductor.firstFixedLevel ρ`, the least level at which
the conductor subgroup fixes a nonzero vector, with value `⊤` if there is
no such level. The conclusion is the following equality in `WithTop ℕ`.

```text
Σ_{κ ∈ X} a(κπ) = f · (s · a(Π₁) + (k + 1) · d).
```

Here `κπ` is `Langlands.twist (κ.comp GeneralLinear.determinant) π`.
Every coefficient is cast from `ℕ` to `WithTop ℕ`. The sum indexes characters,
so distinct characters giving isomorphic twists contribute distinct summands.

The ranks are written `k + 1` and `k₁ + 1` to match the Library's fixed-level
conductor. The two carrier types `W₁` and `W` share the universe `uW`, as in
Task 7470's `CuspidalSigmaLiftStructureStatement`, so that its witnesses can
be used directly. The mathematical structure theorem of Henniart–Lemaire
II.4.12 gives an orbit product for a cuspidal sigma-lift with
`s = Nat.card (normTwistStabilizer E π)`. The present proposition takes any
`s` and `Π₁` witnessing the product equivalence. Uniqueness of cuspidal
support determines the multiset of factors of the lifted representation.
See JPSS 1981 §2.2, printed p. 201, and [CuspidalSigmaLift.md](CuspidalSigmaLift.md).

## From epsilon factors to conductors

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), Chapter 1, Proposition 6.9(ii), printed pp. 60–61
(PDF pp. 74–75), literature ID `arthur-clozel-1989-base-change`, give the
epsilon-factor identity for representations of ranks `n`, `m` and their lifts.
The original printed p. 61 has the factor `λ(E/F, ψ_F)^(-mn)`. With the trivial
character of `GL_1` as the second representation and its trivial lift, this
gives the following identity.

```text
ε(z, Π, ψ_E) = λ(E/F, ψ_F)^(-n) · ∏_{κ ∈ K(E/F)} ε(z, κπ, ψ_F),
ψ_E = ψ_F ∘ Tr_{E/F}.
```

The negative exponent follows the original formula and corrects the sign in
the task summary. The conductor comparison uses the power of `q_F^(-z)`, so
the lambda factor, which is constant in the complex variable `z`, drops out.
See Arthur–Clozel (6.7), printed p. 60.

Choose `ψ_F` trivial on `𝒪_F` and nontrivial on `𝔭_F^(-1)`. The trace
codifferent is `𝔭_E^(-d)`, so `ψ_E` is trivial on `𝔭_E^(-d)` and
nontrivial on `𝔭_E^(-d-1)`. See Serre, *Local Fields* (1979), Chapter III,
§3, printed p. 50 (PDF p. 57), literature ID `serre-1979-local-fields`,
and [ExtensionInvariants.md](ExtensionInvariants.md).

For the convention that an additive character `ψ` has exponent `n(ψ)` when
its largest ideal of triviality is `𝔭_K^(-n(ψ))`, the standard epsilon factor
of a generic irreducible `ρ` of `GL_m(K)` is a nonzero constant times
`q_K^(-(a(ρ) + m n(ψ)) z)`. Jacquet–Piatetski-Shapiro–Shalika,
*Conducteur des représentations du groupe linéaire* (1981), §1.1 and
Théorème (5.1), printed pp. 199 and 211 (PDF pp. 1 and 13), literature ID
`jpss-1981-conductor`, give the conductor interpretation at additive exponent
zero. Changing the additive character gives the shift by `m n(ψ)`.

Consequently `q_E = q_F^f`, `n(ψ_F) = 0`, and `n(ψ_E) = d` give the
following identity by comparing exponents.

```text
Σ_κ a(κπ) = f · (a(Π) + n d).
```

The full normalized orbit product hypothesis lets the source argument use
additivity from multiplicativity of epsilon factors. Arthur–Clozel use
that multiplicativity at the start of the proof of Proposition 6.9, printed
p. 61. The automorphism `σ` preserves `𝒪_E`, its maximal ideal, and each of
the congruence subgroups defining the conductor. Thus
`a(Π₁^(σ^i)) = a(Π₁)`, and the product gives `a(Π) = s · a(Π₁)`.
The Lean telescope asks for the product equivalence and admissibility of `Π`.
The full product matters for the additivity argument. For example, the
Steinberg representation of `GL_2` has conductor one even though its two
cuspidal support characters have conductor zero.

Arthur–Clozel formulate the epsilon identity for their normalized base-change
lift. The Lean hypothesis uses the distributional σ-lift of Henniart–Lemaire
II.2.7, with the intertwiner and nonzero scalar as data. A formal proof
following Arthur–Clozel would have to relate these lift conventions and
translate the epsilon identity to the fixed-level conductors. See
[TwistedCharacter.md](TwistedCharacter.md).

Henniart, *La conjecture de Langlands locale numérique pour GL(n)* (1988),
§6.1(4)–(5), printed p. 514 (PDF p. 19), literature ID
`henniart-1988-numerical`, gives the corresponding epsilon identity and the
following Swan-exponent form.

```text
f · sw(Ch_(E/F)(π)) = -f · c_wild · n + Σ_κ sw(κπ),
c_wild = d - e + 1.
```

Passing to the Swan exponent with truncated subtraction requires a separate
count of unramified rank-one characters.

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), II.4.6, Théorème (4), printed p. 89
(PDF p. 97), literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
state the equivalent normalized epsilon-factor identity. Specializing the
second representation to the trivial character of `GL_1` and comparing
exponents gives the following form.

```text
Σ_κ a(κπ) = f · a(Π) + n · Σ_κ a(κ).
```

The conductor-discriminant formula gives `Σ_κ a(κ) = f d`, so this is the
same formula. The Lean proposition uses `d` directly because clause (W4) of
`LocalCyclicBaseChangeStatement` is phrased using the different exponent.

## Input existence, topology, and finiteness

A finite local-field extension has a residue degree, and in characteristic
zero separability makes the trace codifferent a nonzero fractional ideal,
hence a power of the maximal ideal. The two uniqueness lemmas in
`ExtensionInvariants` show that their characterizations determine `f` and
`d`. By local class field theory the norm subgroup of a cyclic extension has
index `l` and is open. The quotient has exactly `l` complex characters, which
gives the set `X`. Each norm-trivial character is continuous and smooth
because it factors through this quotient by an open subgroup.

The two valuations are independent data in the telescope.
`IsModuleTopology F E` gives `E` its topology as a finite-dimensional
`F`-vector space. Finiteness is part of `IsCyclicAlgebra`. The topology
determines the valuation ring as the set of power-bounded elements, so the
valuation rings are compatible, with `𝒪_F ⊆ 𝒪_E`.

The representations `κπ` and `Π₁` are irreducible supercuspidal and therefore
generic. The newvector theorem gives finite conductors for them. The Library
provides `Conductor.firstFixedLevel_of_hasNewvectorLevel` and the proved
`Conductor.supercuspidalPadicConductorExponent` for a `PadicField` with its
canonical structures and supplied genericity and normalization data
(`Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof`).
Applying that specialization to the arbitrary local-field carriers here needs
field, structure, and genericity comparisons. The conclusion uses the total
conductor in `WithTop ℕ`.

JPSS 1981 uses the Godement–Jacquet standard epsilon factor, and the Library's
conductor exponent statement uses the JPSS pair factor against the trivial
character of `GL_1`. Their comparison remains open in the Library. The same
coverage notes document Jacquet's 2012 correction to the general essential-vector
existence proof. The Library's proved supercuspidal case uses a separate
existence argument. See [coverage.md](../../notes/local-factors/coverage.md)
and [EssentialStatement.md](../Representation/Conductor/EssentialStatement.md).

Arthur–Clozel Proposition 6.9 and this statement allow arbitrary cyclic degree
`l`. The product `sigmaOrbitProduct` requires `E` to be a nonarchimedean
local field. Under `CharZero F`, the separability of the characteristic
polynomial used in `IsSigmaLift`'s test-function concordance agrees with
Henniart–Lemaire's squarefree convention.

## Rank-one checks and the source proof

For rank one, `π = 1`, and unramified `E/F`, the norm-trivial characters are
unramified, `d = 0`, and the lifted character is trivial. Both sides are zero.
For a tame totally ramified extension of degree `l`, `f = 1`, `d = l - 1`,
and the `l - 1` nontrivial norm-trivial characters each have conductor one.
The lifted character has conductor zero, and both sides are `l - 1`.

Arthur–Clozel's proof begins on printed p. 61 and continues through p. 70
(PDF pp. 75–84). It reduces to square-integrable and supercuspidal data,
uses Rankin–Selberg functional equations over the base and extension,
globalizes the local representations, and applies global base change.
The proof reaches the epsilon-factor conclusion on printed pp. 69–70.
A future proof needs a dependency route independent of this conductor identity.
