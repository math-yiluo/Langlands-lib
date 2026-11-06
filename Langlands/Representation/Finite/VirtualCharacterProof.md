# Proof of the faithfulness and irreducible-basis conjuncts of finite Brauer theory

Author: Worker 84, who wrote the proof and this explanation.

This file proves two of the seven conjuncts of the Library proposition
`Langlands.FiniteRep.FiniteBrauerTheoryStatement` from
`Langlands.Representation.Finite.BrauerStatement`. The targets are unchanged
and keep their hypotheses: `G` is a group in universe `uG` with a `Fintype`
instance.

| Theorem in `Langlands.FiniteRep.VirtualCharacter` | Proves |
| --- | --- |
| `faithfulness` (implicit `G`) | `FiniteVirtualCharacterFaithfulnessStatement G` |
| `irreducibleBasis` (implicit `G`) | `FiniteIrreducibleBasisStatement G` |
| `faithfulnessAndBasis G` | the conjunction of these two, in that order |

`FiniteVirtualCharacterFaithfulnessStatement G` says that the integral
character map `virtualCharacter : VirtualRep ℂ G →ₗ[ℤ] (G → ℂ)` is injective.
`FiniteIrreducibleBasisStatement G` says that `irreducibleExpansion G`, the
map from finitely supported integer coefficient functions on
`IrreducibleClass G` to `VirtualRep ℂ G` that sends `Finsupp.single a n` to
`n • ofClass a.1`, is bijective. Here `VirtualRep ℂ G` is the group completion
of the direct-sum monoid `RepClass ℂ G` of isomorphism classes of actual
`FDRep ℂ G`, and `IrreducibleClass G` is the subtype of classes having an
irreducible representative.

The other five conjuncts (rank one, the induced character formula, the induced
degree, integral Brauer spanning and the character-lattice equality) are not
proved here, and neither is `FiniteBrauerTheoryStatement` itself. The proof
adds no hypotheses or axioms. The declaration checks of `irreducibleBasis` and
`faithfulnessAndBasis` report only `propext`, `Classical.choice` and
`Quot.sound`. The file defines two helpers, `pairing` and `rep`, described
below; no target statement uses them.

## Imports

The file imports the target module and
`Langlands.Representation.Finite.CharacterTheoryProof`, the proof of
`Langlands.FiniteCharacterTheoryStatement` (namespace
`Langlands.FiniteCharacter`). From that proof it uses these theorems, all for
finite-dimensional complex representations of `G` whose two carriers may lie
in different universes:

- `isomorphism`: two representations have equal characters if and only if
  they are equivalent;
- `orthogonality`: for irreducible `ρ` and `σ`,
  `(Fintype.card G)⁻¹ * ∑ g, ρ.character g⁻¹ * σ.character g` is `1` if they
  are equivalent and `0` otherwise;
- `normOne`: a representation is irreducible if and only if this number,
  for `σ = ρ`, is `1`;
- `exists_isAtom`: a nonzero representation has an atom in its lattice of
  subrepresentations;
- `prodEquivOfIsCompl`, `isCompl_toSubmodule`, `toSubmodule_ne_bot` and
  `neZero_card`: the equivalence of a representation with the product of two
  complementary subrepresentations, the corresponding facts about the
  underlying subspaces, and `(Nat.card G : ℂ) ≠ 0`.

From the public Library modules `Langlands.Representation.Finite.Classes` and
`Langlands.Representation.Finite.Virtual` it uses `classOf`, `classOf_eq_iff`,
`isoOfEquiv`, `equivOfIso`, `character_classOf`, `classOfRepresentation` with
its lemmas `classOfRepresentation_congr`, `classOfRepresentation_rho` and
`classOfRepresentation_prod`, `ofRepresentation`, `modelEquiv`, `zeroRep`,
`virtualRep_exists_difference` (every virtual class is `ofClass a - ofClass b`)
and `virtualCharacter_ofClass`. It also uses
`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom` (an atom
subrepresentation is irreducible), `irreducibleExpansion_single` from the
target module, Mathlib's complemented lattice of subrepresentations (Maschke's
theorem, which needs `(Nat.card G : ℂ) ≠ 0`), and Mathlib's
`Representation.char_iso`.

## Faithfulness

`classOf_eq_of_character_eq` turns equal characters of two `FDRep ℂ G` into
equal classes, through `isomorphism` and `isoOfEquiv`.
`eq_of_character_eq` lifts this to classes by quotient induction. In
`faithfulness`, the map `virtualCharacter` is additive, so it suffices to show
that its kernel is zero. Write a kernel element as `ofClass a - ofClass b`.
Its character is `character a - character b = 0`, so `a = b` and the element
is zero.

## Pairing and orthonormality

`pairing f` is the additive map `h ↦ (Fintype.card G)⁻¹ * ∑ g, f g⁻¹ * h g`.
`rep a` is a chosen irreducible representative of `a : IrreducibleClass G`;
`classOf_rep`, `isIrreducible_rep` and `character_val` record that its class
is `a.1`, that it is irreducible and that `character a.1` is its character.

`pairing_irreducible` proves that `pairing (character b.1) (character a.1)` is
`1` if `b = a` and `0` otherwise. Subtype extensionality and `classOf_eq_iff`
show that `b = a` if and only if `rep b` and `rep a` are equivalent, and
`orthogonality` gives the two values.

## Basis

Injectivity (`irreducibleExpansion_injective`). The characters
`character a.1` of the irreducible classes are linearly independent over `ℤ`:
apply `pairing (character b.1)` to a vanishing finite integer combination. By
`pairing_irreducible` only the term of `b` survives, so its coefficient,
cast to `ℂ`, is zero. Composing with `virtualCharacter`, which sends
`ofClass a.1` to `character a.1`, shows that the family `ofClass a.1` is
linearly independent over `ℤ` (`LinearIndependent.of_comp`). This is
injectivity of `irreducibleExpansion G`, since that map is its
`Finsupp.linearCombination`.

Invariance of irreducibility (`isIrreducible_of_equiv`). If `ρ` is
irreducible and equivalent to `σ`, then `σ` is irreducible: the two
characters are equal by `Representation.char_iso`, and `normOne` reads
irreducibility off the character.

Actual classes lie in the range (`ofClass_mem_range`). For every
finite-dimensional complex representation `ρ` on a carrier in `Type`,
`ofClass (classOfRepresentation ρ)` lies in the range of
`irreducibleExpansion G`. The proof is by strong induction on the dimension
`n`.

- If the dimension is zero, the carrier is a subsingleton, so `ρ` is
  equivalent to `zeroRep`. Its class is `0`, which is in the range.
- Otherwise `exists_isAtom` gives an atom `T`, which is irreducible, and
  Mathlib's complemented lattice gives a complement `C`. By
  `prodEquivOfIsCompl` and `classOfRepresentation_prod`, the class of `ρ` is
  the sum of the classes of `T` and `C`. The class of `T` is the irreducible
  class `a` represented by `ofRepresentation T.toRepresentation`, which is
  irreducible by `isIrreducible_of_equiv` applied to `modelEquiv`, so
  `ofClass a.1` is the image of `Finsupp.single a 1`. The dimensions of the
  underlying subspaces of `T` and `C` add up to `n` and that of `T` is
  nonzero, so `C` has smaller dimension and the induction hypothesis applies.

Surjectivity (`irreducibleExpansion_surjective`). Write a virtual class as
`ofClass a - ofClass b`. For a class represented by `V : FDRep ℂ G`,
`classOfRepresentation V.ρ = classOf V`, so `ofClass_mem_range` puts
`ofClass a` and `ofClass b` in the range, and so their difference too.

`irreducibleBasis` combines injectivity and surjectivity, and
`faithfulnessAndBasis` pairs it with `faithfulness`.
