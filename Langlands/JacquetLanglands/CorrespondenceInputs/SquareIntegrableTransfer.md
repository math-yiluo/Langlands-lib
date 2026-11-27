# Existence of the Jacquet–Langlands transfer of a square-integrable representation

The module `Langlands.JacquetLanglands.CorrespondenceInputs.SquareIntegrableTransfer`
states one proposition, `SquareIntegrableTransferExistenceStatement`, and
does not prove it. In characteristic zero, every irreducible representation of
`GL_n(F)` that is square-integrable modulo the centre, with unitary central
character, has a Jacquet–Langlands partner on `D^×`. The source is the
Théorème principal of Deligne–Kazhdan–Vignéras (DKV) for `G' = D^×`. The
statement is the surjectivity half of that theorem, restricted to inputs on
`GL_n(F)` with unitary central character.

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
  disconnected topological groups. The definition of the relation below
  installs these facts locally.
- `SmoothRep.{0, u, uV} ℂ G` (`Langlands.Representation.Category.Basic`) is
  the category of smooth complex representations of `G` with carriers in
  `Type uV`. For an object `A`, `A.representation` is the underlying
  `Representation`. `Representation.IsIrreducible` means that the lattice of
  subrepresentations is simple, so in particular the carrier is nonzero.
- `IsSquareIntegrable ρ` (`Langlands.JacquetLanglands.EssentiallySquareIntegrable`)
  is square-integrability modulo the centre. For every Borel Haar measure on
  `GL_n(F)/Z`, it asks for three things: `ρ` is admissible, `ρ` has a
  central character of absolute value one with open kernel, and for every
  vector `v` and every smooth linear functional `ℓ` the function
  `g ↦ |ℓ(ρ(g) v)|` on `GL_n(F)/Z` is square-integrable.
- `IsJacquetLanglandsSmoothPair F D n A B`
  (`Langlands.JacquetLanglands.Relation`) is `IsJacquetLanglandsPair` applied
  to the underlying representations `A.representation` and
  `B.representation`. It is the conjunction of `Module.finrank F D = n ^ 2`,
  irreducibility and essential square-integrability of `A.representation`,
  irreducibility of `B.representation`, and the following condition. There
  are admissibility witnesses `hA : IsAdmissible A.representation` and
  `hB : IsAdmissible B.representation` such that, for all
  `g : GeneralLinear n F` and `g' : Dˣ` with `Corresponds F D g g'`, there is
  `c : ℂ` with `HasCharacterValue A.representation hA g ((-1)^(n-1) * c)`
  and `HasCharacterValue B.representation hB g' c`. In other words,
  `Θ_A(g) = (-1)^(n-1) Θ_B(g')`.
- `Corresponds F D g g'` (`Langlands.JacquetLanglands.RegularElliptic`)
  means that `g` is regular elliptic, `g'` is regular, and the characteristic
  polynomial of `g` equals the reduced characteristic polynomial of `g'`.
- `HasCharacterValue ρ hρ g c` (`Langlands.JacquetLanglands.LocalCharacter`)
  means that for every Haar measure `μ` the distribution character of `ρ`
  equals `c · μ` on test functions supported near `g`, that is,
  `χ_ρ(g) = c`.

## The statement

`SquareIntegrableTransferExistenceStatement` says the following. Let `F` be a
nonarchimedean local field of characteristic zero, `D` a finite-dimensional
central division algebra over `F` with its module topology, and `n` a
natural number with `Module.finrank F D = n ^ 2`. Let
`A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)` be irreducible with
`IsSquareIntegrable A.representation`. Then there is
`B : SmoothRep.{0, u, uW} ℂ Dˣ` with `IsJacquetLanglandsSmoothPair F D n A B`.

The carrier universes `uV` and `uW` are independent.

## Why the statement is true

DKV, Théorème principal (§c of the introduction, printed p. 34): there is a
bijection `π' ↦ π` from `E²(G')` onto `E²(G)`, where `G' = GL(m, D)` and
`G = GL(n, F)`. It is characterized by the character relation
`(-1)^m χ_{π'} = (-1)^n χ_π` on the regular classes of `G'`. Here `E²`
denotes the isomorphism classes of irreducible admissible representations
that are square-integrable in DKV's sense (notation on printed p. 34). The
definition is in §A.4.c (printed p. 63). An admissible representation is
square-integrable if its restriction to `G°` has square-integrable
coefficients (property D1). Here `G°` is the subgroup of §A.4.a (printed
p. 61): the common kernel of `|χ(g)|_F` over the rational characters `χ` of
`G`. For `GL_n(F)` this is `{g : |det g|_F = 1}`. No condition on the
central character is imposed. For `GL_1(F)`, for example, `G°` is the
compact group `O_F^×`, and the character `|·|_F` lies in `E²` although its
central character is not unitary. For these groups DKV's square-integrability
is therefore the convention that Badulescu calls essentially
square-integrable. Unitarity enters only through the sets `E(G, ω)`, where
`ω` is a unitary central character (printed p. 34). For
`m = 1`, `G' = D^×` with `D` of dimension `n²`, the relation reads
`χ_π(g) = (-1)^(n-1) χ_{π'}(g')`. DKV give a complete proof when characters
are locally integrable, which Harish-Chandra proved in characteristic zero
(printed p. 34).

For `G' = D^×` the proof is DKV §B.1 (printed pp. 78–82). The last steps
are these:

- B.1.f (printed p. 81): orthogonality of characters and the Schwarz
  inequality reduce the global comparison of traces to one term, with
  multiplicity one.
- B.1.g (printed pp. 81–82): every `π' ∈ E(G'_S, ω_S)` is a local component
  of an automorphic representation. This gives an injective map
  `π' ↦ π` into `E²(G_S, ω_S)`. It is surjective because `G'_S` is compact
  modulo its centre, so its characters form a complete system.
- B.1.h (printed p. 82): descent to a single place gives a bijection from
  `E²(G_v)` onto `E²(G'_v)` with `χ_π = a χ_{π'}`. The sign is
  `a = (-1)^(n-1)`, because the trivial representation corresponds to the
  Steinberg representation.

From this, the statement follows. Let `A` be as in the statement. It is
admissible, its central character is unitary, and its coefficients are
square-integrable modulo the centre. Its restriction to `G°` then has
square-integrable coefficients, because `G° ∩ Z` is compact and `Z G°` has
finite index in `G`. So the class of `A` lies in `E²(GL_n(F))`, and by
surjectivity there is `π' ∈ E²(D^×)` with
`χ_A(g) = (-1)^(n-1) χ_{π'}(g')` for corresponding `g ↔ g'`. Since `D^×` is
compact modulo its centre, `π'` is finite-dimensional, so `π'` has a
realization `B` with carrier in `Type uW` for every universe `uW`. Each
conjunct of `IsJacquetLanglandsSmoothPair F D n A B` then holds:

- `A` is essentially square-integrable with exponent `s = 0`
  (`IsSquareIntegrable.isEssentiallySquareIntegrable`).
- `A` is admissible (`IsSquareIntegrable.isAdmissible`), and `B` is
  admissible because it is finite-dimensional.
- At a regular elliptic `g`, the character of `A` has a local value. This is
  Harish-Chandra's theorem, and the Library proves it in characteristic zero
  as `Langlands.BaseChange.ordinaryRegularSemisimpleCharacterValues_charZero`.
- At `g'`, the character of `B` has the value `trace B(g')`
  (`hasCharacterValue_trace`).

DKV's identity is then the required relation between these values.

## Derived content and differences from the sources

The statement is derived from DKV's theorem. It differs in these respects:

- DKV state a bijection on isomorphism classes. This statement only gives
  surjectivity, and only for inputs with unitary central character. It is
  phrased for bundled representatives with carriers in fixed universes.
  Asking for `B` in an arbitrary universe `uW` is no stronger, because `π'`
  is finite-dimensional.
- The hypothesis `IsSquareIntegrable A.representation` is narrower than
  membership in DKV's `E²(GL_n(F))`. It asks for a unitary central character
  and for coefficients square-integrable modulo the centre. DKV's `E²`
  (§A.4.a and §A.4.c, printed pp. 61 and 63) only asks for square-integrable
  coefficients on `G°`, and so contains representations with non-unitary
  central character, such as `|·|_F` on `GL_1(F)`. The statement is
  therefore the restriction of DKV's surjectivity to inputs with unitary
  central character. DKV's twisting property (§d, item 4, printed p. 35)
  relates the general input to this case. See the Role section.
- The Library's relation asks `A` to be essentially square-integrable
  (`IsEssentiallySquareIntegrable`). This agrees with DKV's notion of
  square-integrability on `G°` and with Badulescu's essential
  square-integrability. An `A` with `IsSquareIntegrable` is essentially
  square-integrable with exponent `s = 0`
  (`IsSquareIntegrable.isEssentiallySquareIntegrable`).
- Characters are evaluated through local values of distribution characters
  (`HasCharacterValue`). At regular semisimple points these are DKV's
  `χ_π(g)` (printed p. 33).
- DKV's correspondence of elements is the injection `{G'} → {G}` of
  conjugacy classes (introduction §a, printed p. 33). The Library's
  `Corresponds F D g g'` compares the characteristic polynomial of `g` with
  the reduced characteristic polynomial of `g'`, and asks `g` to be regular
  elliptic and `g'` regular.
- DKV state the Théorème principal for a nonarchimedean local field (printed
  p. 34). Their proof is complete when characters are locally integrable,
  and Harish-Chandra proved local integrability in characteristic zero. The
  hypothesis `CharZero F` selects this case of DKV's theorem. Badulescu
  2002, Théorème 1.1 and the paragraph after it (printed p. 696), states the
  correspondence for a nonarchimedean local field, credits DKV with the
  characteristic-zero case, and proves the case of nonzero characteristic.
  This module states only the characteristic-zero form.

## Role

Mathematically, the statement gives the existence half of the
Jacquet–Langlands correspondence on the side of `GL_n(F)`, the first
conjunct of `IsJacquetLanglandsBijection` in
`Langlands.JacquetLanglands.Statements`. An irreducible essentially
square-integrable `A` is `|det|^s ⊗ A₀` with `A₀` square-integrable (the
definition of `IsEssentiallySquareIntegrable`). If `B₀` is a partner of
`A₀`, then `|Nrd|^s ⊗ B₀` is a partner of `A`, because `det g = Nrd g'` for
corresponding elements. This is the compatibility of the correspondence with
twisting by characters of `F^×` (DKV, §d, item 4, printed p. 35). It
extends the statement from inputs with unitary central character to all of
`E²(GL_n(F))`. This module does not carry out that argument.

## Sources

- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres
  centrales simples p-adiques*, in J. N. Bernstein, P. Deligne, D. Kazhdan,
  M.-F. Vignéras, *Représentations des groupes réductifs sur un corps
  local*, Hermann, 1984, pp. 33–117. Registered as
  `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`
  (printed page = PDF page − 4). The locators are:
  - introduction §a, printed p. 33 (PDF page 37);
  - Théorème principal and the notation `E`, `E(G, ω)` and `E²`, printed
    p. 34 (PDF page 38);
  - §d, notation `πμ` for twisting by a character `μ` of `F^×`, printed
    p. 34 (PDF page 38), and item 4 (twisting, `π'μ ↦ πμ`), printed p. 35 (PDF
    page 39);
  - §A.4.a (the subgroup `G°`), printed p. 61 (PDF page 65);
  - §A.4.c (definition of square-integrable representations, property D1),
    printed p. 63 (PDF page 67);
  - §B.1.f–h, printed pp. 81–82 (PDF pages 85–86).
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
  Théorème 1.1, printed p. 696 (PDF page 2; TeX source lines 197–204),
  gives the bijection `E²(G) → E²(G')` of classes of essentially
  square-integrable representations, with sign `(-1)^(n-r)`, for a
  nonarchimedean local field. The paragraph after it on the same page (TeX
  source lines 206–207) credits DKV with the characteristic-zero case. The
  paper proves the case of nonzero characteristic.
