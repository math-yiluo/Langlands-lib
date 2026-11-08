# The actual based-root and character model of a Levi cocenter

Author: Worker 1293. Worker 1632 prepared the matching independent submission.

`splitTorusCentralizerCocenterRootModel` proves the unchanged public proposition
`SplitTorusCentralizerCocenterRootModelStatement.{u}` of
`LeviCocenterRootModelStatement`, at arbitrary universe `u` and with no premises
beyond those inside the proposition itself.

For every connected reductive group `G` over an arbitrary field `k : Type u`, a
split subtorus `a : A ⟶ G`, a representative `j : M ⟶ G` of its centralizer, an
actual derived subgroup `d : D ⟶ M` and a commutative fppf quotient
`q : M ⟶ Q` by its full range, with `M` connected reductive and `Q` a torus, the
proposition supplies a maximal ground-field torus `t : T ⟶ M`, a finite Galois
extension `E/k` in the same universe splitting `T` and `Q`, ambient maximality
of `(t ≫ j)_E` in `G_E`, a finite reduced root datum on the character and
cocharacter lattices of `T_E` that is the actual root datum of `G_E` relative
to `(t ≫ j)_E` (`IsRootDatumOf`), a root base `B`, a subset `s` of its simple
roots, and `CocenterRootDescentData`. That data says that the actual character
pullback along `t ≫ q` is injective with image exactly the annihilator of the
selected simple coroots, and that integral corrections composed with the
ordinary Galois actions preserve the actual root pairing, permute simple coroots
preserving `s`, and fix the whole pullback image.

## Implemented proof

The proof is a single application of the published reduction
`splitTorusCentralizerCocenterRootModel_of_rootDatum_product_intersection` from
`LeviCocenterRootModelReduction`. That theorem derives the exact proposition
from three explicit structural propositions, all at the same universe `u`:

- `RootDatumExistenceStatement`, discharged by the published unconditional
  theorem `rootDatumExistence` of `Reductive.RootDatumExistence`;
- `DerivedMaximalTorusProductSurjectivityStatement`, discharged by the published
  unconditional theorem `derivedMaximalTorusProductSurjectivity` of
  `Derived.MaximalTorusProductSurjectivityProof`;
- `DerivedMaximalTorusIntersectionStatement`, discharged by the published
  unconditional theorem `derivedMaximalTorusIntersection` of
  `Derived.MaximalTorusIntersectionProof`.

## What the reduction does

The imported reduction combines the following constructions.

1. **Derived semisimplicity.** Root existence and product surjectivity give a
   finite full centre of every actual derived subgroup. The reduction passes to
   an algebraic closure and chooses a compatible split maximal derived torus
   inside an ambient maximal torus. The actual torus complement and product
   surjectivity then give a finite centre (`DerivedTorusFiniteCenter`), and the
   published `HasFiniteCenter.of_fieldExtension` reflects finiteness to `k`.
   With published connected reductivity of derived subgroups, this gives
   derived semisimplicity.
2. **Character comparison.** `LeviCocenterRootModelAssembly` compares the actual
   cocenter character pullback with the coroot annihilator over the algebraic
   closure. It uses the two root data, semisimplicity, product surjectivity and
   the full intersection. The comparison is then reflected to the finite Galois
   splitting field by canonical base change.
3. **Based descent.** On the retained finite Galois model, the reduction keeps
   the rational maximal torus `t : T → M` and the finite Galois field `E`
   splitting `T` and `Q`. It also keeps ambient maximality of `(t ≫ j)_E` and
   the base change of the original separating cocharacter. The
   coweight-face construction gives a genuine root base `B`. The selected
   subset `s` is the set of simple roots vanishing on that cocharacter. The
   construction also supplies the correction maps, so the result is
   `CocenterRootDescentData k E (Additive.ofMul (t ≫ q)) P B s` for the actual
   reduced root datum `P`.

So the conclusion uses the actual character pullback through the supplied
quotient `q`, the actual reduced root datum of `(t ≫ j)_E`, and the ordinary
Galois representations on its lattices. No auxiliary permutation lattice is
substituted, and the auxiliary closure torus in step 1 does not replace the
retained rational torus or the original cocharacter.

## Provenance

The statement's own Markdown records the derived provenance from Milne,
*Algebraic Groups* (2017), 25.25 and 25.c. This proof transcribes no further
literature theorem. It composes published Library results by their Lean names.
