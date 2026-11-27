# Existence of the inverse Jacquet–Langlands transfer for unitary central characters

The module `Langlands.JacquetLanglands.CorrespondenceInputs.UnitaryDivisionTransfer`
states one proposition, `UnitaryDivisionTransferExistenceStatement`, and does
not prove it. In characteristic zero, every irreducible admissible
representation of `D^×` with unitary central character has a
Jacquet–Langlands partner on `GL_n(F)`. This is the existence of the image of
every class of `E²(D^×)` under the bijection of the Théorème principal of
Deligne–Kazhdan–Vignéras (DKV).

## Notation

- `F` is a nonarchimedean local field: `[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]` (the Mathlib class),
  here with `[CharZero F]`.
- `D` is a finite-dimensional central division algebra over `F`:
  `[DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]`. It carries its `F`-module topology
  (`[TopologicalSpace D] [IsModuleTopology F D]`), and `D^×` carries the
  units topology. `F` and `D` both live in `Type u`.
- `GeneralLinear n F` is `GL_n(F)`, with the topology induced from matrices.
  The theorems of `Langlands.JacquetLanglands.DivisionUnits` show that both
  `GL_n(F)` and `D^×` are Hausdorff, locally compact and totally
  disconnected topological groups.
- `SmoothRep.{0, u, uW} ℂ G` (`Langlands.Representation.Category.Basic`) is
  the category of smooth complex representations of `G` with carriers in
  `Type uW`. For an object `B`, `B.representation` is the underlying
  `Representation`. `Representation.IsIrreducible` means that the lattice of
  subrepresentations is simple. `IsAdmissible` is the Library's
  admissibility: smooth, with finite-dimensional spaces of vectors fixed by
  each open subgroup.
- `Units.map (algebraMap F D : F →* D) : Fˣ →* Dˣ` is the inclusion of `F^×`.
  Since `D` is central over `F`, its image is the centre of `D^×`.
- `HasScalarCharacter ρ z ω` (`Langlands.Classification`, in
  `Langlands.Representation.Classification.ConstituentRelations`) means
  `ρ (z c) v = ω c • v` for all `c` and all vectors `v`. Here it says that
  `F^×` acts on `B` through the character `ω : Fˣ →* ℂˣ`.
- `IsJacquetLanglandsSmoothPair F D n A B`
  (`Langlands.JacquetLanglands.Relation`) is the conjunction of
  `Module.finrank F D = n ^ 2`, irreducibility and essential
  square-integrability of `A`, irreducibility of `B`, admissibility of both,
  and the character identity. The identity says that for all
  `g : GeneralLinear n F` and `g' : Dˣ` with `Corresponds F D g g'` there is
  `c : ℂ` with `HasCharacterValue A g ((-1)^(n-1) * c)` and
  `HasCharacterValue B g' c`, that is, `Θ_A(g) = (-1)^(n-1) Θ_B(g')`.
  `Corresponds F D g g'` asks `g` to be regular elliptic, `g'` to be regular,
  and the characteristic polynomial of `g` to equal the reduced
  characteristic polynomial of `g'`. `HasCharacterValue ρ hρ g c` says that
  the distribution character of `ρ` is `c` times Haar measure near `g`.

## The statement

`UnitaryDivisionTransferExistenceStatement` says the following. Let `F` be a
nonarchimedean local field of characteristic zero, `D` a finite-dimensional
central division algebra over `F` with its module topology, and `n` a
natural number with `Module.finrank F D = n ^ 2`. Let
`B : SmoothRep.{0, u, uW} ℂ Dˣ` satisfy three hypotheses:

1. it is irreducible;
2. it is admissible;
3. there is `ω : Fˣ →* ℂˣ` with
   `HasScalarCharacter B.representation (Units.map (algebraMap F D)) ω`
   and `‖ω z‖ = 1` for all `z : Fˣ`.

Then there is `A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)` with
`IsJacquetLanglandsSmoothPair F D n A B`.

The carrier universes `uV` and `uW` are independent. The character `ω` is
not assumed continuous. Because `B` is smooth and nonzero, `ω` is trivial on
the open subgroup of `F^×` that fixes a nonzero vector, so `ω` is
automatically a smooth unitary character.

## Why the statement is true

DKV, Théorème principal (§c of the introduction, printed p. 34): there is a
bijection `π' ↦ π` from `E²(G')` onto `E²(G)`, where `G' = GL(m, D)` and
`G = GL(n, F)`. It is characterized by `(-1)^m χ_{π'} = (-1)^n χ_π` on the
regular classes of `G'`. Here `E(G)` denotes the classes of irreducible
admissible representations, `E(G, ω)` those with central character `ω`, and
the exponent `2` asks for square-integrability (printed p. 34). For `m = 1`
the relation reads `χ_π(g) = (-1)^(n-1) χ_{π'}(g')`. DKV give a complete
proof when characters are locally integrable, which Harish-Chandra proved in
characteristic zero (printed p. 34).

For `G' = D^×`, the group is compact modulo its centre `F^×`. An irreducible
admissible representation with unitary central character therefore has
matrix coefficients of constant absolute value along cosets of the centre
and bounded on the compact quotient, so it is square-integrable. Hence its
class lies in `E²(D^×)`. DKV use exactly this domain in §B.1.g (printed
pp. 81–82), where the map `π' ↦ π` is defined on `E(G'_S, ω_S)` with values
in `E²(G_S, ω_S)`. They pass to a single place in §B.1.h (printed p. 82),
where the sign `(-1)^(n-1)` is fixed by matching the trivial representation
with the Steinberg representation.

From this, the statement follows. Let `B` be as in the statement. Its class
`π'` lies in `E²(D^×)`, and its image `π ∈ E²(GL_n(F))` is irreducible,
admissible and square-integrable, with
`χ_π(g) = (-1)^(n-1) χ_{π'}(g')` for corresponding `g ↔ g'`. An admissible
representation of `GL_n(F)` has countable dimension, because it is the union
of its fixed spaces under a countable decreasing basis of compact open
subgroups, each finite-dimensional. So `π` has a realization `A` with
carrier in `Type uV` for every universe `uV`. Each conjunct of
`IsJacquetLanglandsSmoothPair F D n A B` then holds:

- `A` is essentially square-integrable with `s = 0`.
- Both representations are admissible.
- At a regular elliptic `g`, the character of `A` has a local value
  (Harish-Chandra; in the Library,
  `Langlands.BaseChange.ordinaryRegularSemisimpleCharacterValues_charZero`).
- `B`, an irreducible smooth representation of `D^×`, is finite-dimensional,
  so its character has the value `trace B(g')` at `g'`
  (`hasCharacterValue_trace`).

DKV's identity is then the required relation between these values.

## Derived content and differences from the sources

The statement is derived from DKV's theorem. It differs in these respects:

- DKV's domain `E²(D^×)` is described here by hypotheses on a
  representative: irreducible, admissible, with a central character of
  absolute value one. For the group `D^×`, compact modulo its centre, these
  describe exactly the square-integrable classes.
- DKV state a bijection on classes. This statement is only the existence of
  the image of each class, phrased for bundled representatives with carriers
  in fixed universes. Asking for `A` in an arbitrary universe `uV` is no
  stronger, because `π` has countable dimension.
- The Library's relation asks `A` to be essentially square-integrable, as
  Badulescu does. A square-integrable `A` is essentially square-integrable
  with `s = 0`.
- Characters are evaluated through local values of distribution characters
  (`HasCharacterValue`). The correspondence of elements is the Library's
  `Corresponds F D g g'`, equality of the characteristic polynomial of `g`
  and the reduced characteristic polynomial of `g'`. This is DKV's
  injection of conjugacy classes `{G'} → {G}` (introduction §a, printed
  p. 33).
- The hypothesis `CharZero F` is DKV's. Badulescu 2002 proves the
  correspondence for every nonarchimedean local field. This module states
  only the characteristic-zero form.

## Role

Mathematically, the statement gives the existence half of the
Jacquet–Langlands correspondence on the side of `D^×`, the second conjunct of
`IsJacquetLanglandsBijection` in `Langlands.JacquetLanglands.Statements`.
An irreducible admissible `B` is finite-dimensional, so by Schur's lemma it
has a central character `ω`. Its absolute value is `|z|^r` for a real `r`.
Since `Nrd z = z^n` for `z ∈ F^×`, the twist `B₀ = |Nrd|^(-r/n) ⊗ B` has
unitary central character. If `A₀` is a partner of `B₀`, then
`|det|^(r/n) ⊗ A₀` is a partner of `B`. This module does not carry out that
argument.

## Sources

- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres
  centrales simples p-adiques*, in J. N. Bernstein, P. Deligne, D. Kazhdan,
  M.-F. Vignéras, *Représentations des groupes réductifs sur un corps
  local*, Hermann, 1984, pp. 33–117. Registered as
  `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`
  (printed page = PDF page − 4). The locators are:
  - introduction §a, printed p. 33 (PDF page 37);
  - notation `E`, `E(G, ω)` and `E²`, and the Théorème principal, printed
    p. 34 (PDF page 38);
  - §B.1.f–h, printed pp. 81–82 (PDF pages 85–86).
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps
  locaux de caractéristique non nulle*, Ann. Sci. ÉNS 35 (2002). Registered
  as the publication folder `badulescu-2002-jl-char-p` (registered
  fingerprint
  `dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`).
  The file cited is its TeX source `math0201117.tex`, SHA-256
  `5d7a70b1052dd220f94b4136f64d6b6bc0491d792bf5545c60eb44a82ae74219`.
  Théorème 1.1 (lines 197–204) gives the bijection in every characteristic.
  Lines 206–207 note that DKV proved it in characteristic zero.
