# Affine-test relative endomorphism scheme with clopen quasi-compact pieces

Authors: Worker 1042. The interface was proposed by Worker 1042 and agreed, unchanged, with Worker 1109
(peer conversation `884dbe1769f55fedb077327163141739`), who wrote none of the files.

This module only defines the proposition
`Langlands.AbelianScheme.AffineHomSchemePiecesStatement.{u}`, a closed
`Prop`-valued definition with one universe parameter `u`. It gives no proof
of the proposition and adds no axiom. It is an internal interface between
two halves of the proof of
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement.{u}`:

- one half proves this proposition by porting the Hom-scheme construction
  for abelian schemes from the Anthropic Fermat's Last Theorem Lean source;
- the other half derives the published target statement from it.

## Statement

Take a commutative noetherian ring `R : Type u` and put `S = Spec R`. Take
an actual `A : Langlands.AbelianScheme S` whose structure morphism
`A.X.hom` is `Langlands.AlgebraicGeometry.IsHProjective`. The proposition
asserts that there is an actual `H : Over S` with these properties:

1. The structure morphism `H.hom` is separated (`IsSeparated`), locally of
   finite type (`LocallyOfFiniteType`) and formally unramified
   (`FormallyUnramified`).
2. Restrict to the full subcategory of `Over S` on the objects `T` with
   `IsAffine T.left`, through Mathlib's inclusion `ι` for that object
   property. On this subcategory the presheaf
   `ι.op ⋙ relativeHomFunctor A.toCommGroupScheme A.toCommGroupScheme ⋙
   forget AddCommGrpCat.{u}` is naturally isomorphic to
   `ι.op ⋙ yoneda.obj H`.
3. There are an index type `I : Type u` and a family
   `U : I → H.left.Opens` of open subsets of the underlying scheme of `H`
   such that:
   - every `U i` is also closed in `H.left`;
   - every composite `(U i).ι ≫ H.hom`, the open immersion of `U i` followed
     by the structure morphism, is quasi-compact;
   - the sets `U i` are pairwise disjoint
     (`Pairwise (Function.onFun Disjoint U)`);
   - their supremum is the whole space (`(⨆ i, U i) = ⊤`).

The presheaf in item 2 is the published
`Langlands.GroupScheme.Cartier.relativeHomFunctor`, which is also used in the
target statement. Its value at a test object `T` is the set of actual
homomorphisms of commutative group schemes from `A_T` to itself over
`T.left`. Its restriction along a morphism over `S` is the published
`Langlands.GroupScheme.Cartier.restrict`. The presheaf `yoneda.obj H` sends
`T` to `Hom_S(T, H)`, with restriction by precomposition. `Nonempty` of the
isomorphism in the functor category asserts that these sets correspond
bijectively and naturally for every morphism between affine test objects.

## Provenance and relation to the target

This proposition is a project-internal interface, not a statement taken from
the literature. It records what the ported construction delivers in Library
terms. In the Anthropic Fermat's Last Theorem source (registered in the
project literature as the complete Lean source at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`), the theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`
constructs a separated, locally finite type, formally unramified Hom scheme
for abelian schemes, tested on affine schemes `Spec S'`, together with
closed and open pieces that are quasi-compact over the base and are indexed
by Hilbert polynomials. The covering and disjointness clauses come from local
constancy of the Hilbert polynomial in flat families.

The target statement differs in three ways, which the derivation from this
interface handles: its test category is all locally noetherian schemes over
`S`, not only the affine ones; it asks for a representing object that is
locally noetherian; and it asks for an isomorphism over `S` from the
representing object to a scheme coproduct of H-projective schemes over `S`.
Classically, the qc pieces are proper over `S` by the valuative criterion
with discrete valuation rings and the extension of homomorphisms of abelian
schemes from the generic fibre. They are therefore finite over `S`, because
they are unramified, and so H-projective.
