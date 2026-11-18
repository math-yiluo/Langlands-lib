# Homomorphisms with commuting values kill fppf-local commutators

Namespace `Langlands.GroupScheme.CommutatorTriviality`. This internal module is the base case
(`B = A`) of the proof of `WeilAbelianImageTrivialityStatement`.

## Setting

`R` is a commutative ring, `K` and `M` are group schemes over `Spec R`, and `T` is an
`R`-algebra. `c` is a natural transformation from `Under.forget T ⋙ K.affinePointFunctor` to
`Under.forget T ⋙ M.affinePointFunctor`, that is, a homomorphism of group functors on
`T`-algebras. The hypothesis `hc` says that, over each `T`-algebra `X`, the values `c.app X x`
commute with each other.

## Contents

- `map_eq_one_of_mem_commutator`: a group homomorphism whose values commute with each other kills
  the commutator subgroup. Its range is commutative, so the image of `⁅G₁, G₁⁆` (which is
  `⁅range, range⁆`, by `map_commutator_eq`) is trivial.
- `app_eq_one_of_mem_commutator`: the same for `c.app X`.
- `affineRefinement 𝒰` (definition): for an fppf cover `𝒰` of a scheme `Y` (precoverage
  `Flat ⊓ LocallyOfFinitePresentation`), the cover by the members of the affine open covers of the
  members of `𝒰`. It is again an fppf cover, with affine members.
- `pieceAlg X f` and `pieceMap X f` (definitions): for a morphism `f : Spec S ⟶ Spec X`, the ring
  `S` as an `R`-algebra and the algebra map `X ⟶ S` with `Spec` of it equal to `f`
  (`algSpec_pieceMap_left`).
- `app_eq_one_of_locallyCommutator`: if a point `x` of `K` over `X` is fppf-locally a commutator
  (`RelativeDerived.LocallyCommutator x`), then `c.app X x = 1`. Proof: on each affine member
  `Spec S` of the refined cover, the image of `x` is a commutator
  (`RelativeDerived.commutator_precomp`), so `c` kills it; by naturality of `c` the image of
  `c.app X x` over `S` is `1`. The refined cover is an effective epimorphic family
  (`RelativeDerived.effectiveEpiFamily_fppfCover`), so `c.app X x = 1`.
- `app_eq_one_of_semisimple`: **base case.** If `K` is reductive with semisimple geometric fibres,
  then `c.app X x = 1` for all `X` and `x`. Every point of `K` is fppf-locally a commutator by
  `relativeSemisimpleFppfPerfect`.

## Provenance

Internal. The argument is the one sketched in the Markdown of
`WeilAbelianImageTrivialityStatement`: the values of `c` commute, so `c` kills commutators, and
the point functor of the scheme `M` is separated for the fppf topology. The perfectness input is
Conrad, *Reductive group schemes* (2014), Theorem 5.3.1 and its proof, pp.160–163, formalized as
`RelativeSemisimpleFppfPerfectStatement` and proved in the Library.
