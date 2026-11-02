# Intrinsic relative simple-root basis and rank targets

Author: Worker 1230.

`RelativeRankStatement` is the conjunction of the following two propositions, each universally quantified over an arbitrary universe and field, an actual connected reductive group scheme `G`, and an actual maximal split torus `i : T → G`. These are statement targets; this module supplies no proof of them.

`RelativeSimpleRootBasisStatement` also takes an actual cocharacter `ν` that is generic for the actual relative roots. It asserts finiteness of the published set `simpleRelativeRoots i ν`, existence of a rational basis of `relativeRootSpan i` indexed by exactly that set, and equality of every basis vector with `simpleRelativeRootVector i ν α`. Thus it gives independence and spanning for the actual characters `1 ⊗ α`. It also states `relativeRootRank i = Nat.card (simpleRelativeRoots i ν)`. The simple roots are defined using all positive relative roots and their indecomposability, retaining nonreduced systems. No nonemptiness or positive-rank assumption occurs.

`RelativeRankIdentityStatement` supplies finiteness of the full rationalized character lattice of `T`, the relative root span, and the rationalized rational-character module of `G`. It identifies the existing supremum-valued `splitRank G` with the natural-number `splitTorusRank T`, cast into `ℕ∞`, and states

`splitTorusRank T = relativeRootRank i + rationalCharacterRank G`.

For every actual split component `a : A → G`, it also supplies finiteness of the rationalized lattice of `A`, bijectivity of the actual scalar-extended restriction `rationalCharacterRestrictRat a`, and the identities

`rationalCharacterRank G = splitTorusRank A`,

`splitTorusRank T = relativeRootRank i + splitTorusRank A`.

The restriction map is defined on actual group-scheme Hom lattices; the commutative-group character lattice and rational-character module are definitionally the same here. Bijectivity is a conclusion, with no chosen equivalence supplied as an input. Finiteness is included explicitly because `Module.finrank` alone would not distinguish an infinite-dimensional space from dimension zero.

The structural premises are only connected reductivity, maximal splitness, and (for the basis) genericity. The affine instance is extracted from connected reductivity. There is no premise asserting a root system, reflection realization, Coxeter structure, simple-root basis, rank decomposition, or rational-character restriction theorem. Existing split-component and character-lattice theorem owners remain separate; their public results may be used in a future proof.

The source provenance is derived. Borel–Tits, *Groupes réductifs* (1965), §4.23 (printed p.93, PDF p.40), §4.27 (printed p.94, PDF p.41), and Theorem 5.3 with its proof (printed pp.96–97, PDF pp.43–44) give the arbitrary-field split-rank convention, additivity under almost direct products, and equality of the root rank with the semisimple split rank. In that proof, the common root-kernel identity component is the identity component of the intersection of the center with the maximal split torus. Corollary 5.8 (printed pp.98–99, PDF pp.45–46) places the possibly nonreduced root system in its actual rational root span.

Renard, French version dated 9 July 2026, V.2.5–6 (printed pp.107–108, PDF pp.113–114), gives injective finite-index restriction of rational characters to the split component; V.3.6–7 (printed p.111, PDF p.117) separates the central and semisimple summands; V.3.12–13 (printed p.112, PDF p.118) gives the simple-root basis and central annihilator. Renard works over a nonarchimedean local field. The arbitrary-field proposition here is the algebraic extension from Borel–Tits and rational tensor linear algebra, rather than an assertion that Renard literally uses arbitrary fields. Passing from the integral restriction of finite index to its rational bijectivity, and from the real simple-root basis to a rational basis of the rational span of those integral roots, are derived scalar-extension consequences.

The retained Renard 2010 errata, PDF pp.8–9, correct the character restriction diagram and semisimple-space notation in the earlier edition. The cited 2026 passages use the corrected restriction sequence and put the simple-root basis in the semisimple summand. This target likewise preserves the full central complement and asserts no spanning of the full character space by the roots.
