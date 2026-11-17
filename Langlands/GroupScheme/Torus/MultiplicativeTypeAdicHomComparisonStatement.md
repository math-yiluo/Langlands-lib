# Effectivity of compatible homomorphisms from an isotrivial group of multiplicative type

The proposition `Langlands.GroupScheme.MultiplicativeTypeAdicHomComparisonStatement`
encodes SGA 3, Exposé IX, Théorème 7.1 (Gille–Polo recomposed edition, 2009,
pp.56–59, original margins pp.68–72), registered source
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The theorem itself begins on recomposed p.56 (margin p.68); Lemme 7.2 and
the rest of the proof follow on pp.57–59.

Let `A` be a noetherian commutative ring, `I` an ideal, and suppose
`IsAdicComplete I A`. This condition includes separation. Let `H` and `G`
be group schemes over `S = Spec A`, with `G → S` affine. Suppose that
there is a finite étale surjective morphism `S' → S` over which `H` becomes
diagonalizable. Put `S_n = Spec(A/I^(n+1))`. The restriction map

`Hom_S(H,G) → {compatible families in Hom_(S_n)(H_(S_n),G_(S_n))}`

is bijective. Equivalently, every compatible family comes from a unique
homomorphism over `S`.

The codomain in Lean is the actual type
`HomScheme.Adic.System I H G`. Its `hom n` field is a group-scheme
homomorphism after base change along the actual quotient map `S_n → S`.
Compatibility uses `HomScheme.evaluate` along `S_n → S_(n+1)`, including
the canonical comparisons between iterated pullback objects. The map
`HomScheme.Adic.System.restrict` is the actual base change of a global
homomorphism at every level. Indexing at `n+1` discards only the
uninformative quotient by `I^0 = A`.

The splitting hypothesis is the isotrivial case stated in the source, and
matches the published `MultiplicativeTypeAdicLiftStatement` exactly.
`IsDiagonalizable` is the Library's finite-type diagonalizable-group
predicate, consistent with the relative multiplicative-type convention:
Brian Conrad, *Reductive group schemes* (2014), Definition B.1.1 (p.280)
and Corollary B.4.2(1) (p.299). This statement makes no smoothness, flatness,
finite-type, or finite-presentation assumption on `G` beyond affineness.
It assumes no locality condition on `A`.

The source proves the diagonalizable case using its finite-support
Lemme 7.2 on coordinate Hopf algebras, and then descends over the finite
étale splitting cover. The statement contains both injectivity and
surjectivity; the separately published
`MultiplicativeTypeAdicHomInjectivityStatement` names only its injectivity
part. This file supplies a proposition target and does not supply its
proof.
