# The Steinberg character on the regular elliptic set

The module `Langlands.JacquetLanglands.TransferInputs.SteinbergEllipticCharacter`
states one proposition, `SteinbergEllipticCharacterStatement`, and does not
prove it. For a nonarchimedean local field `F` of characteristic zero and
`n > 0`, some irreducible square-integrable representation of `GL_n(F)` has
character value `(-1)^(n-1)` at every regular elliptic element. The Steinberg
representation is such a representation.

## Notation

- `F` is a nonarchimedean local field (`[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]`) of characteristic
  zero (`[CharZero F]`), in `Type u`.
- `GeneralLinear n F` is `GL_n(F)` with the topology induced from matrices.
  The `haveI` lines supply its Hausdorff, locally compact and totally
  disconnected structure from `Langlands.JacquetLanglands.DivisionUnits`.
- `SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)` is the category of smooth
  complex representations of `GL_n(F)` with carriers in `Type uV`.
- `IsSquareIntegrable` (`Langlands.JacquetLanglands.EssentiallySquareIntegrable`)
  is square-integrability modulo the centre: admissible, with a unitary
  central character, and with matrix coefficients square-integrable on
  `GL_n(F)/Z` for every Haar measure there. `IsSquareIntegrable.isAdmissible`
  extracts admissibility.
- `IsRegularElliptic g` (`Langlands.JacquetLanglands.RegularElliptic`) says
  that the characteristic polynomial of `g` is separable and irreducible over
  `F`.
- `HasCharacterValue ρ hρ g c` (`Langlands.JacquetLanglands.LocalCharacter`)
  says that for every Haar measure `μ` on `GL_n(F)` the distribution
  character of `ρ` is `c • μ` on test functions supported near `g`, that is,
  Harish-Chandra's character function is constant `c` near `g`.

## The statement

`SteinbergEllipticCharacterStatement` says: for every such `F` and every
`n > 0` there are `St : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)` and
`hSt : IsSquareIntegrable St.representation` such that `St` is irreducible and
`HasCharacterValue St.representation hSt.isAdmissible g ((-1) ^ (n - 1))` for
every regular elliptic `g`.

The carrier universe `uV` is free.

## Why the statement is true

The Steinberg representation `St_n` of `GL_n(F)`, the quotient of the
space `C^∞(B \ G)` of locally constant functions on `B \ G` by the sum of the
subspaces `C^∞(P \ G)` for the standard parabolic subgroups `P ⊋ B`, is
irreducible and square-integrable, with trivial central character (Casselman
§8.1). In the Grothendieck group it is the alternating sum
`∑_{P ⊇ B} (-1)^{r(P)} C^∞(P \ G)` over the standard parabolic subgroups,
where `r(P)` is the number of simple roots in the Levi component of `P` and
`C^∞(P \ G)` is the unnormalized smooth induction of the trivial character
of `P` (in normalized notation, the induction of `δ_P^{-1/2}`). The term for
`P = G` is the trivial representation, with sign `(-1)^(n-1)`. The character of
a representation induced from a proper parabolic subgroup vanishes at regular
elliptic elements (van Dijk's formula for induced characters: a regular
elliptic element fixes no proper flag over `F`), so the character of `St_n`
there equals `(-1)^(n-1)` times the trivial character. For `n = 1`,
`St_1` is the trivial representation of `Fˣ`, with character `1`.

Deligne–Kazhdan–Vignéras use this value in §B.1.h to fix the sign of the
correspondence between the trivial representation of `Dˣ` and the Steinberg
representation of `GL_n(F)`. In Badulescu's proof of Proposition 5.8, the split
automorphic representation has a Steinberg component on `GL_n(F_{v_i})` at
each auxiliary ramified place `v_i` for `1 ≤ i ≤ m`. Its character is
`(-1)^(n-1)` on the regular elliptic set, and its partner on the local
division unit group is trivial.

## Derived content and differences from the sources

- The proposition asserts the existence of an irreducible square-integrable
  representation with the given character on the regular elliptic set. It
  does not construct the Steinberg representation. Any irreducible
  square-integrable representation with this property is equivalent to the
  Steinberg representation, by the orthogonality relations of elliptic
  characters, but the statement does not say so.
- Character values are local values of distribution characters
  (`HasCharacterValue`), as in the Library's Jacquet–Langlands relation.
- The hypothesis `CharZero F` matches the use in the characteristic-zero
  Jacquet–Langlands statements of the Library; the source fact holds in every
  characteristic.

## Sources

- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres
  centrales simples p-adiques*, in J. N. Bernstein, P. Deligne, D. Kazhdan,
  M.-F. Vignéras, *Représentations des groupes réductifs sur un corps local*,
  Hermann, 1984, pp. 33–117. Registered as
  `bdkv-1984-representations-local-field` (printed page = PDF page − 4):
  - Introduction §c, printed p. 34. For `m = 1`, the signed character
    identity on matching regular elements reads
    `Θ_π(g) = (-1)^(n-1) Θ_{π'}(g')`.
  - §B.1.h, printed p. 82. The Steinberg representation of `GL_n(F)`
    corresponds to the trivial representation of `Dˣ`.
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux
  de caractéristique non nulle*, Ann. Sci. ÉNS 35 (2002). Registered as the
  folder `badulescu-2002-jl-char-p`; TeX source `math0201117.tex`, lines
  3130–3145, the end of the proof of Proposition 5.8 (published §5, pp.
  734–735): the Steinberg character equals `(-1)^(n-1)` on the regular
  elliptic elements of `GL_n(F_{v_i})` for every auxiliary ramified place
  `v_i`.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft, 1 May 1995. Registered as
  `casselman-1995-admissible-representations`: §8.1, p. 70 (the
  representations `C^∞(P_Θ \ G)`, the Steinberg quotient, its irreducibility
  and square-integrability).
