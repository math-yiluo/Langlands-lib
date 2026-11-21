# Labelled Hodge–Tate decomposition of the Harris middle-degree multiplicity

`HarrisCMLabelledMultiplicityStatement` is the coefficient-equivariant labelled
Hodge–Tate comparison on the actual family used by the Kottwitz bridge.

It is stated at the same arguments as the published
`CMHarrisKottwitzLambdaAdicStatement`:
- the CM datum `D` and the Harris signature charts `C`;
- the PEL inputs, the representability input `q` and the dual-scheme inputs;
- rigidity, a small level `U`, and the coefficient representation `ρ` of the
  similitude group over the number field `K`.

## Hypotheses

These are Kottwitz's hypotheses on `A`, `n`, `ρ`, the central weight `w` and the
admissible representation `πf` over `K` that is irreducible over `K̄`, plus
**concentration**. At every coefficient place where the actual fixed-vector
comparisons `CMHarrisLambdaTowerFixedVectorComparison` hold in all degrees, the
Hecke multiplicity space `cmHarrisLambdaTowerHeckeMultiplicity` of `πf ⊗_K K_λ`
at level `U` is zero in every degree `i ≠ n − 1`. This is verbatim a premise of
`HarrisKottwitzMiddleDegreeStatement`.

## Conclusion

Fix any coefficient place `λ` of `K` with:
- the fixed-vector comparisons in every degree;
- continuity of the level cohomology in every degree
  (`CMHarrisLambdaCohomologyContinuous`);
- finite dimensionality of the degree-`n − 1` Hecke multiplicity space.

Let `j : F → K` be any embedding of the CM field. Write `M_λ` for
`cmHarrisLambdaHeckeMultiplicityObjects` in degree `n − 1`, the actual Galois
representation of `F` on that Hecke multiplicity space. Then there are a
natural number `m` and pairwise distinct integers `k : Fin n → ℤ` such that:
- `n · m` is the dimension of the multiplicity space over `K_λ`;
- `HasLabelledHodgeTateAt λ M_λ (λ ∘ j) n m k`. That is, the local pullback of
  `M_λ` along the label `λ ∘ j : F → K_λ` has the actual semilinear
  decomposition with each exponent `k i` repeated `m` times.

No condition is put on the rational prime below `λ`; in particular it need not
split in the imaginary quadratic subfield.

Downstream, `m = |a|` for Kottwitz's integer `a`. This follows because the
Euler polynomial `reverse(Q_v^{|a|})` of the same object has degree `n|a|` at a
good place. The inverse twist by the scalar avatar then uses
`AlgebraicHeckeAvatarTateExponentStatement` and
`HarrisLabelledInverseTwistStatement`.

## Provenance

This is derived from Harris (1999), *Galois properties of cohomological
automorphic forms on GL(n)*, proof of 5.7(i), pp. 313–314. There Faltings's
comparison is applied to the cohomology of the proper smooth Shimura variety
with the algebraic coefficient system. The comparison is Faltings (1988),
*p-adic Hodge theory*, Chapter III, Theorem 4.1, p. 298. Harris–Taylor (2001),
VII.1.9, pp. 227–228, computes the graded pieces at a specified embedding in
their rank-`n` setting. Kottwitz (1992), Theorem 1, p. 657, and its proof give
the equality of the multiplicities of `πf ⊗ π_∞` over the discrete series
packet. That equality yields one common multiplicity for the `n` Hodge types.

## Boundary

Only the proposition is defined. The proof needs the following, with no
external sheaf library on the current pin:
- the coefficient-equivariant Faltings comparison on proper smooth powers of
  the universal abelian scheme, with the projector realizing `W`;
- compatibility of that comparison with the Hecke projector of `πf`;
- the Hodge types of the discrete series packet with coefficients `W` at the
  complex embedding corresponding to each label;
- the equal-multiplicity input above.

The published `CMHarrisLambdaCohomologyHodgeTateStatement` gives only the
underlying unlabelled decomposition of the whole level cohomology. It is not a
substitute for these coefficient-equivariant inputs.
