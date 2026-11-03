# Rational conjugacy of torus lifts across a linear vector kernel

This is an internal combination of the actual difference cocycle in
`Rational.QuotientHomCocycle` and rational vector-cocycle vanishing in
`Rational.TorusVectorCocycle`.

Let `k` be any field in universe `u`. Let `n : N → G` be monic on the
underlying relative schemes and let `q : G → Q` be any actual group-scheme
homomorphism. Assume the all-test range of `n` equals the range of the actual
kernel inclusion of `q`. Assume `N` is affine over `k` and is supplied with
natural coordinates identifying its points on every relative test `T` with the
additive group of `Fin d → Γ(T, ⊤)`.

Let `i₀, i₁ : H → G` be actual homomorphisms with equal composites to `Q`, and
assume `IsTorus H`. Conjugation on `N` along `i₀` is the already constructed
action `QuotientHomCocycle.action`. The final input
`IsLinearVectorCoordinates (action n q hn i₀) e` requires this actual action
to be scalar-linear in the supplied coordinates over every ring of global
sections.

`QuotientHomCocycle.torusConjugator` is an actual `k`-point of `N`. It applies
the proved rational torus-cocycle construction to the actual difference cocycle
of `i₀` and `i₁`. The cocycle formula in `G` is
`c(h) = i₁(h) * i₀(h)⁻¹`. Its rational coboundary identity is equivalent to
`i₁(h) = v * i₀(h) * v⁻¹`. Accordingly,
`torusConjugator_conjugates` proves the equality of actual homomorphisms
`i₀ ≫ inner(v ≫ n) = i₁`. The proof applies the existing
`cocycle_eq_coboundary_iff` to the proved actual cocycle equality.
`torusConjugator_mem_kernel` records that the image of this rational point is
in the actual kernel range on the base test. `subgroupConjugate_of_isTorus`
uses it and the identity source isomorphism in the existing rational
`SubgroupConjugate` predicate.

The last two lemmas permit different source groups. For a supplied isomorphism
`f : H ≅ H'` and maps `i : H → G`, `i' : H' → G` whose quotient composites
agree after `f`, `exists_kernel_conjugator_of_isTorus_iso` applies the same
construction to `i` and `f.hom ≫ i'`. It returns an actual rational `N`-point
whose image conjugates these two homomorphisms.
`subgroupConjugate_of_isTorus_vector_kernel` then uses precisely `f` as the
source isomorphism in `SubgroupConjugate i i'`.

The provenance is internal: this module composes two established constructions
and their exact identities and introduces no external structural theorem.
It allows all characteristics, finite and imperfect fields, nonsplit tori and
dimension zero. It requires no smoothness or surjectivity of `q`, no injectivity
of either torus lift, and no maximality assumptions. It does not construct the
vector kernel, its scalar-linear coordinates or a quotient-compatible source
isomorphism; those are explicit inputs. The full maximal-torus conjugacy
statement remains a separate obligation.
