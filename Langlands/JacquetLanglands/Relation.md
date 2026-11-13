# The local Jacquet–Langlands relation

This module defines the predicate that relates a representation of
`GL_n(F)` to a representation of `D^×` by the Jacquet–Langlands
character identity. Here `F` is a nonarchimedean local field (the
Mathlib class `IsNonarchimedeanLocalField F`, any characteristic) and
`D` is a central division algebra of dimension `n²` over `F`. It does
not state that the relation is a bijection. That is a separate
theorem statement.

## Sources

- Deligne–Kazhdan–Vignéras 1984 (*Représentations des algèbres
  centrales simples p-adiques*, introduction, printed p. 34, PDF page
  38 of the registered readable original), "Théorème principal".
  There is a bijection `π' ↦ π` from `E²(G')` to `E²(G)`, with
  `G' = GL(m, D)` and `G = GL(n, F)`. It is characterized by the
  character relation `(-1)^m χ_{π'}(g') = (-1)^n χ_π(g)` on the
  regular elliptic sets, for corresponding `g'` and `g`. For `m = 1`,
  `G' = D^×`, this reads `χ_π(g) = (-1)^{n-1} χ_{π'}(g')`. DKV prove it
  in characteristic zero.
- Badulescu 2002 (`math0201117.tex`, Théorème 1.1, lines 197–203; the
  same statement as Théorème 5.1, lines 2789–2799). Let `D` have
  dimension `d²`, `n = rd`, `G = GL_n(F)` and `G' = GL_r(D)`. There is a
  unique bijection `C : E²(G) → E²(G')` with
  `χ_π(g) = (-1)^{n-r} χ_{C(π)}(g')` whenever `g ↔ g'`. Here `E²` is
  the set of equivalence classes of irreducible essentially
  square-integrable representations, and the field may have positive
  characteristic. For `r = 1` the sign is `(-1)^{n-1}`. Badulescu's
  relation `g ↔ g'` asks for `g` and `g'` regular semisimple with the
  same characteristic polynomial. `corresponds_iff` (in
  `Langlands.JacquetLanglands.RegularElliptic`) proves that for
  `G' = D^×` this is the module's `Corresponds F D g g'`, which asks
  for `g` regular elliptic as in DKV.

DKV's `E²` asks for square-integrable representations with unitary
central character. Badulescu's `E²` asks for essential
square-integrability, which allows a twist by a character. This module
follows Badulescu and Task 5443: `ρ` is essentially square-integrable.

## Conventions

`GL_n(F)` is the Library's `GeneralLinear n F` with the topology induced
from matrices. `D` has a topology with `IsModuleTopology F D`, that is,
the finest topology making it a topological `F`-module, and `D^×` has
the units topology. The theorems of
`Langlands.JacquetLanglands.DivisionUnits` (`generalLinear_t2Space`,
`generalLinear_locallyCompactSpace`,
`generalLinear_totallyDisconnectedSpace`, `units_isTopologicalGroup`,
`units_t2Space`, `units_locallyCompactSpace`,
`units_totallyDisconnectedSpace`) supply these properties of both groups.
The definitions install them locally with `haveI`, because the
character values below need them.

Characters are the Library's distribution characters
`Langlands.Character.distribution`. They are evaluated at a point
through `HasCharacterValue ρ hρ g c` from
`Langlands.JacquetLanglands.LocalCharacter`: for every Haar measure `μ`,
the character agrees near `g` with `c` times `μ`. This is the local,
pointwise form of Harish-Chandra's formula `trace π(φ) = ∫ χ_π φ` that
DKV recall (introduction, printed p. 33). It says `χ_π(g) = c`.

## The relation

`IsJacquetLanglandsPair F D n ρ ρ'`, for
`ρ : Representation ℂ (GeneralLinear n F) V` and
`ρ' : Representation ℂ Dˣ W`, is the conjunction of:

1. `Module.finrank F D = n ^ 2`;
2. `ρ` is irreducible (`Representation.IsIrreducible`);
3. `ρ` is essentially square-integrable (`IsEssentiallySquareIntegrable`
   from `Langlands.JacquetLanglands.EssentiallySquareIntegrable`);
4. `ρ'` is irreducible;
5. there are admissibility proofs `hρ` and `hρ'`, and for all
   `g : GeneralLinear n F` and `g' : Dˣ` with `Corresponds F D g g'`
   there is `c : ℂ` such that `HasCharacterValue ρ hρ g ((-1)^(n-1) * c)`
   and `HasCharacterValue ρ' hρ' g' c`.

So `Θ_ρ(g) = (-1)^{n-1} Θ_{ρ'}(g')` for corresponding `g` and `g'`.

Remarks on the formulation:

- The dimension condition keeps the relation from holding vacuously
  when `n` is not the reduced degree of `D`. Without it no `g` would
  correspond to any `g'` (`Corresponds.eq_reducedDegree`), and the
  character condition would hold for no reason. A division ring has
  positive dimension, so the relation never holds for `n = 0`. For
  `n ≥ 1`, the natural-number exponent `n - 1` is the source's `n - 1`.
- Item 5 asks for character values to exist at corresponding points.
  Harish-Chandra's theorem gives them for irreducible admissible
  representations of `GL_n(F)` at regular semisimple elements. DKV
  recall it, and Badulescu (lines 2774–2778) uses it in all
  characteristics. For `D^×`, irreducible smooth representations are
  finite-dimensional and their characters are `g' ↦ trace ρ'(g')`,
  which `hasCharacterValue_trace` provides. Neither theorem is proved or
  assumed here. Where those values exist, item 5 is exactly the
  character identity, by uniqueness of character values
  (`character_eq` below).
- Admissibility is existential. `ρ` is admissible anyway, by
  `IsEssentiallySquareIntegrable.isAdmissible`. For `ρ'` it follows from
  irreducibility, which is not proved here. `HasCharacterValue ρ hρ`
  depends on the proof `hρ` only up to proof irrelevance, so any
  admissibility proof gives the same predicate.

## Projections and the character identity

`IsJacquetLanglandsPair.finrank_eq`, `.isIrreducible`,
`.isEssentiallySquareIntegrable`, `.isIrreducible_right`,
`.isAdmissible` and `.isAdmissible_right` extract the conditions above.

`IsJacquetLanglandsPair.character_eq`: if the pair is related,
`Corresponds F D g g'`, and the characters have values `a` at `g` and `b`
at `g'`, then `a = (-1)^(n-1) * b`. This follows from
`exists_hasCharacterValue_mul_iff` in
`Langlands.JacquetLanglands.LocalCharacter`, which uses uniqueness of
character values.

## Invariance under equivalence

- `isIrreducible_of_equiv`: an equivalence of representations
  transports irreducibility. Irreducibility is simplicity of the
  associated module (`Representation.irreducible_iff_isSimpleModule_asModule`),
  and the equivalence gives a bijective linear map between the
  associated modules (`IntertwiningMap.equivLinearMapAsModule`).
- `IsJacquetLanglandsPair.of_equiv` and
  `isJacquetLanglandsPair_iff_of_equiv`: if `ρ ≃ σ` and `ρ' ≃ σ'` as
  representations, then `ρ, ρ'` are related exactly when `σ, σ'` are.
  The proof transports admissibility (`isAdmissible_of_equiv`),
  essential square-integrability
  (`isEssentiallySquareIntegrable_iff_of_equiv`) and character values
  (`hasCharacterValue_iff_of_equivariant`).

## Bundled versions

- `IsJacquetLanglandsSmoothPair F D n A B` is the relation for bundled
  smooth representations `A : SmoothRep ℂ (GeneralLinear n F)` and
  `B : SmoothRep ℂ Dˣ` (the Library's `SmoothRep` category), applied to
  their underlying representations.
- `isJacquetLanglandsSmoothPair_iff_of_iso`: isomorphic bundled
  representations are related together, through
  `SmoothRep.equivOfIso`.
- `IsJacquetLanglandsClassPair F D n π π'` is the relation on
  isomorphism classes `SmoothRep.IsoClass`, defined with
  `Quotient.lift₂` and well defined by the previous theorem. This is
  the form in which the correspondence is a bijection `E²(G) → E²(G')`.
  `isJacquetLanglandsClassPair_isoClass` says that the classes of `A`
  and `B` are related exactly when `A` and `B` are.

## Irreducibility of the trivial representation

`isIrreducible_trivial G`: the trivial representation of a monoid `G`
on `ℂ` is irreducible, since `ℂ` has only the subspaces `⊥` and `⊤`.

## Nonvacuity

`isJacquetLanglandsPair_trivial_one F`: for `n = 1` and `D = F`, the
trivial representations of `GL_1(F)` and `F^×` on `ℂ` are related. Here
`finrank F F = 1 = 1²`. Both representations are irreducible and
admissible, being smooth and finite-dimensional. The representation of
`GL_1(F)` is essentially square-integrable by
`isEssentiallySquareIntegrable_trivial_one`. Both characters have the
value `trace 1 = 1` everywhere by `hasCharacterValue_trace`, and the
sign is `(-1)^0 = 1`, so `c = 1` works for every pair of points. In the
sources, the correspondence for `n = 1` and `D = F` is the identity on
characters of `F^×`; the example is its simplest instance.
