# Irreducible smooth representations of `Dˣ` are finite-dimensional

The module
`Langlands.JacquetLanglands.CorrespondenceInputs.DivisionUnitsFiniteDimensional`
states one proposition, `IrreducibleDivisionUnitsFiniteDimensionalStatement`,
and does not prove it. Let `D` be a finite-dimensional central division
algebra over a nonarchimedean local field `F`. Then every irreducible smooth
complex representation of `D^×` is finite-dimensional. The statement is the
closed form of the Library's predicate `IrreducibleDivisionUnitsFiniteDimensional`
(in `Langlands.JacquetLanglands.CharacterStatements`): it quantifies over all
such `F` and `D`.

## Notation

- `F` is a nonarchimedean local field: `[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]` (the Mathlib class),
  of any characteristic.
- `D` is a finite-dimensional central division algebra over `F`:
  `[DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]`. It carries its `F`-module topology
  (`[TopologicalSpace D] [IsModuleTopology F D]`), and `D^×` carries the
  units topology. `F` and `D` both live in `Type u`.
- `IrreducibleDivisionUnitsFiniteDimensional.{u, uW} F D` says the
  following. For every complex vector space `W : Type uW` and every
  `ρ' : Representation ℂ Dˣ W`, if `ρ'` is smooth (`IsSmooth`: every vector
  is fixed by an open subgroup) and irreducible
  (`Representation.IsIrreducible`), then `FiniteDimensional ℂ W`.

## The statement

`IrreducibleDivisionUnitsFiniteDimensionalStatement` says that for every
nonarchimedean local field `F : Type u` and every finite-dimensional central
division algebra `D : Type u` over `F` with its module topology,
`IrreducibleDivisionUnitsFiniteDimensional.{u, uW} F D` holds. The carrier
universe `uW` is arbitrary.

## Why the statement is true

Let `O_D` be the valuation ring of `D` and `𝔭_D` its maximal ideal. The
valuation of `D` is invariant under conjugation, so the compact open
subgroups `K_k = 1 + 𝔭_D^k` are normal in `D^×`. They form a basis of
neighbourhoods of `1`.

Let `W` be a nonzero irreducible smooth representation. A nonzero vector is
fixed by some `K_k`. The subspace `W^{K_k}` is then nonzero and
`D^×`-stable, because `K_k` is normal, so `W = W^{K_k}`. Hence `W` is a
representation of `Γ = D^× / K_k`.

Let `ϖ` be a uniformizer of `F`. It is central in `Γ`, and the subgroup it
generates has finite index in `Γ`. Indeed, `O_D^× / K_k` is finite, and
`D^× / (O_D^× ϖ^ℤ)` is finite (cyclic of order `n` if `D` has dimension
`n²`).

Choose coset representatives `γ_1, …, γ_r`. For a nonzero `w ∈ W`,
irreducibility gives `W = span {γ_i ϖ^j w}`. So `W` is a finitely generated
module over `ℂ[ϖ, ϖ^{-1}]` and has countable dimension. By Schur's lemma for
irreducible representations of countable dimension over `ℂ`, the central
element `ϖ` acts by a scalar. Hence `W = span {γ_1 w, …, γ_r w}` is
finite-dimensional.

The same conclusion also follows from the finiteness of Hecke algebras in
Bernstein–Deligne, *Le « centre » de Bernstein*, Corollaire 3.4 (printed
p. 27 of the same volume as DKV). Let `G` be the group of points of a
reductive group over a nonarchimedean local field. For a compact open
subgroup `K`, the corollary says that the Hecke algebra `H(G, K)` is a
module of finite type over the Bernstein centre. In particular, the remark
after the proof says, `H(G, K)` is of finite type over its own centre, which
is a finitely generated `ℂ`-algebra. Complex admissibility is a consequence
of this. If `W` is irreducible smooth and `W^K ≠ 0`, then `W^K` is a simple
`H(G, K)`-module. It is a finitely generated module over the centre of
`H(G, K)`. By Nakayama's lemma some maximal ideal of the centre kills it,
and the Nullstellensatz makes the quotient field `ℂ`, so `W^K` is
finite-dimensional. In the paragraph that follows, Bernstein–Deligne derive
the same finiteness with rational coefficients from the complex case. They
state explicitly that every irreducible representation over that field is
admissible. Over `ℂ` the corollary gives this only as the consequence just
described. Apply it to `G = D^× = GL_1(D)` and `K = K_k`. Since `K_k` is
normal, it fixes all of `W`, so `W = W^{K_k}` is finite-dimensional.

## Derived content and differences from the sources

The sources use compactness modulo the centre of `D^×` without stating this
finite-dimensionality as a numbered result.

- DKV, §B.1.g (printed pp. 81–82), work under the hypothesis of §B.1.f that
  `G'_S` is a product of multiplicative groups of division algebras. They
  obtain a map `π' ↦ π` from `E(G'_S, ω_S)` to `E²(G_S, ω_S)`, which is
  plainly injective. It is surjective because `G'_S / Z_S` is compact, so
  the characters of `G'_S` form a complete system. Compactness is used
  there for the completeness of characters at a fixed central character,
  not for finite-dimensionality.
- Badulescu 2002, in the proof of Proposition 5.8 (printed p. 734), uses the
  linear independence of characters on the regular elements of a product of
  groups `D_v^×`, which "est compact modulo le centre". The corresponding
  passage of the arXiv TeX source is lines 3134–3137.
- Badulescu 2002, §6 (Annexe, printed p. 745), notes that when `G / Z` is
  compact, the characters of all irreducible smooth representations of `G`
  with central character `ω` form a Hilbert basis of the space of class
  functions considered there, in any characteristic, "comme pour les
  groupes compacts". He notes that this is the case for the unit group of a
  division algebra over `F`.

This statement is derived. It is the closed form of the Library's predicate,
with the argument above as its justification. It holds for every
nonarchimedean local field, not only in characteristic zero, and for
carriers in every universe `uW`.

## Role

Because every irreducible smooth representation `ρ'` of `D^×` is
finite-dimensional, its character is an ordinary trace function: its value at
`g'` is the trace of the linear map `ρ'(g')`. Given the predicate, the Library
proves two consequences in `Langlands.JacquetLanglands.CharacterStatements`:

- `IrreducibleDivisionUnitsFiniteDimensional.isAdmissible`: irreducible
  smooth representations of `D^×` are admissible.
- `isJacquetLanglandsPair_iff_trace`: for `ρ : Representation ℂ
  (GeneralLinear n F) V` and `ρ' : Representation ℂ Dˣ W`,
  `IsJacquetLanglandsPair F D n ρ ρ'` is equivalent to the conjunction of
  the following conditions:
  - `Module.finrank F D = n ^ 2`;
  - `ρ` is irreducible and essentially square-integrable;
  - `ρ'` is irreducible and smooth;
  - there is an admissibility witness `hρ : IsAdmissible ρ` such that, for
    all `g : GeneralLinear n F` and `g' : Dˣ` with `Corresponds F D g g'`,
    the character of `ρ` has the local value
    `(-1)^(n-1) * LinearMap.trace ℂ W (ρ' g')` at `g`
    (`HasCharacterValue ρ hρ g ((-1) ^ (n - 1) * LinearMap.trace ℂ W (ρ' g'))`).

  The pointwise identity `Θ_ρ(g) = (-1)^(n-1) trace ρ'(g')` is only the
  character condition of this conjunction, not the whole relation.

Mathematically, the statement also serves the uniqueness of the partner on
the side of `D^×` and the comparison of central characters, through Schur's
lemma and linear independence of characters.

## Sources

- J. N. Bernstein, P. Deligne, D. Kazhdan, M.-F. Vignéras,
  *Représentations des groupes réductifs sur un corps local*, Hermann, 1984.
  Registered as `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`
  (printed page = PDF page − 4). The locators are:
  - Bernstein–Deligne, *Le « centre » de Bernstein*, Corollaire 3.4 and
    the remarks after it, printed p. 27 (PDF page 31);
  - Deligne–Kazhdan–Vignéras, §B.1.g, printed pp. 81–82 (PDF pages
    85–86).
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps
  locaux de caractéristique non nulle*, Ann. Sci. École Norm. Sup. (4) 35
  (2002), no. 5, 695–747. Registered as the publication folder
  `badulescu-2002-jl-char-p` (registered fingerprint
  `dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`).
  The folder holds the published PDF, SHA-256
  `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`
  (printed page = PDF page + 694), and the arXiv TeX source
  `math0201117.tex`, SHA-256
  `5d7a70b1052dd220f94b4136f64d6b6bc0491d792bf5545c60eb44a82ae74219`.
  The locators are:
  - proof of Proposition 5.8, printed p. 734 (PDF page 40); TeX source
    lines 3134–3137;
  - §6 (Annexe), printed p. 745 (PDF page 51).
