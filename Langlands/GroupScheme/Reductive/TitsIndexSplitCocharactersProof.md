# Proof of the maximal split cocharacter comparison

`Langlands.GroupScheme.titsIndexSplitCocharacters` proves
`Langlands.GroupScheme.TitsIndexSplitCocharactersStatement`: for Tits
index data `d` of a semisimple group \(G\) over an arbitrary field \(k\),
a cocharacter \(\mu\) of \(T_{k_s}\) is the base change of
\(\eta\gg\) `d.torusMap` for a unique cocharacter \(\eta\) of the
maximal split torus \(S\) if and only if \(\langle\alpha,\mu\rangle=0\)
for \(\alpha\in\Delta_0\) and
\(\langle\sigma*\beta,\mu\rangle=\langle\beta,\mu\rangle\) for every
\(\sigma\in\operatorname{Gal}(k_s/k)\) and every absolute simple root
\(\beta\). The equations are the integral form of the equations (1) in
Tits, *Classification of algebraic semisimple groups* (1966), §2.5.1.

## Forward direction

The private lemma `root'_baseChange` shows that the pairing of an
absolute root \(a\) with the base change of \(\eta\gg\) `d.torusMap` is
the pairing over \(k\) of `d.rootRestriction a` with \(\eta\). It
combines `FaceSimpleRootRestriction.latticePairing_baseChange_comp`,
`TitsIndexStarProof.baseChange_rootRestriction` and
`latticePairing_baseChange`. A simple root in `d.zeroVertices` has zero
restriction, so its pairing vanishes. The theorem
`TitsIndexStarProof.rootRestriction_star` says that a root and its image
under the star action have the same restriction, which gives the
equality of pairings along star orbits.

## Converse

Let \(\nu_K\) (`TitsIndexStarProof.nuK`) be the base change of the
generic cocharacter of the index composed with `d.torusMap`.

1. *Roots vanishing on \(\nu_K\).* By `TitsIndexStarProof.dominant`,
   \(\nu_K\) pairs nonnegatively with every absolute simple root, and by
   `TitsIndexStarProof.rootRestriction_eq_zero_iff` a root pairs to zero
   with \(\nu_K\) exactly when its restriction to \(S\) is zero. Every
   root is a nonnegative or a nonpositive integral combination of simple
   roots. If it vanishes on \(\nu_K\), then
   `RootDatumZeroFace.mem_closure_zero_of_mem_closure_nonneg` writes it,
   up to sign, as such a combination of the simple roots that vanish on
   \(\nu_K\), that is, of the roots of \(\Delta_0\). Hence the private
   lemma `zeroRoot_pairing_eq_zero` shows that a cocharacter \(\mu\)
   annihilating \(\Delta_0\) annihilates every root vanishing on
   \(\nu_K\).

2. *Star and ordinary Galois action agree on \(\mu\).* The theorem
   `TitsIndexStarProof.exists_star_correction` writes the star
   automorphism of \(\sigma\) as \(w\) times the ordinary Galois
   automorphism of the root datum, with \(w\) in the subgroup generated
   by the reflections in the roots vanishing on \(\nu_K\). By step 1
   this subgroup lies in the reflection subgroup of the roots vanishing
   on \(\mu\), and `RootDatumBasedCorrection.fixes_coweight` shows that
   \(w\) fixes \(\mu\). The private lemma `coweightEquiv_star_apply`
   concludes that the two automorphisms act on \(\mu\) in the same way.

3. *Simple-root pairings determine a cocharacter.* The base change of
   \(G\) to \(k_s\) is semisimple
   (`IsSemisimple.baseChange_of_algebraicExtension`), so the absolute
   root lattice has finite index in the character lattice
   (`IsSemisimple.finite_quotient_rootSpan`). The simple roots form a
   basis of the root lattice (`RootPairing.Base.toWeightBasisInt`), and
   `AdjointRootDatum.injective_fromRootDatum_coweightMap` shows that a
   cocharacter is determined by its pairings with the root lattice. This
   is the private lemma `coweight_eq_of_simple`.

4. *Galois invariance.* For the star automorphism \(\theta\) of
   \(\sigma\), the pairing of \(\theta\mu\) with a simple root
   \(\beta\) is the pairing of \(\mu\) with \(\sigma*\beta\). The
   orbit equations and step 3 therefore show that
   \(\mu\) is fixed by every star automorphism, and by step 2 by every
   ordinary Galois automorphism of the root datum. The coweight
   component of the Galois automorphism of \(\sigma\) is the Galois
   representation on cocharacters at \(\sigma^{-1}\), so the comparison
   at \(\sigma^{-1}\) shows that `cocharacterLattice.galoisRepresentation`
   fixes \(\mu\) at every \(\sigma\).

5. *Descent and factorization.* By `galoisInvariantLattices`, the
   invariant cocharacter \(\mu\) is the base change of a cocharacter
   \(\nu\) of the maximal \(k\)-torus \(T\). The composite of
   `d.torusMap` with the closed inclusion of \(T\) is the maximal split
   torus of \(G\), so `IsMaximalSplitTorus.of_comp` makes \(S\) a
   maximal split torus of \(T\). As \(T\) is affine and locally of finite
   type, `IsMaximalSplitTorus.isLargestSplitSubtorus` makes \(S\) its
   largest split subtorus, and \(\nu\) factors uniquely as
   \(\eta\gg\) `d.torusMap` (the private lemma `existsUnique_factor`).
   Base change of this factorization gives \(\mu\). For uniqueness, a
   second \(\eta'\) with the same base change gives the same cocharacter
   of \(T\) by `cocharacterLattice.algebraBaseChange_injective`, hence
   \(\eta'=\eta\).
