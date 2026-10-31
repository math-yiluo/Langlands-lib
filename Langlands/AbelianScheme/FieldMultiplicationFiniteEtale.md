# Multiplication by an integer nonzero in a field is a finite étale isogeny

Throughout, `K` is a field (not necessarily algebraically closed), `B` is an actual abelian
scheme over `Spec K`, and `n` is a natural number with `(n : K) ≠ 0`. All four results are
about `GroupScheme.multiplication B.toGrp n`, multiplication by `n` on `B`.

## Results

- `multiplication_isFinite_of_ne_zero`: the underlying scheme morphism of multiplication by
  `n` is finite.
- `multiplication_isIsogeny_of_ne_zero`: multiplication by `n` is a `GroupScheme.IsIsogeny`,
  that is finite, flat and surjective on underlying schemes.
- `multiplicationKernel_isFinite_of_ne_zero`: the structure morphism of the scheme-theoretic
  kernel `GroupScheme.kernel` of multiplication by `n` is finite.
- `multiplicationKernel_etale_of_ne_zero`: that structure morphism is étale.

The hypothesis `(n : K) ≠ 0` cannot be dropped from this module's route. The published
`Langlands.GroupScheme.FieldMultiplicationIsogenyStatement`, which asks for the isogeny
property for every positive `n` in every characteristic, is not proved here.

## Proofs

`multiplication_isFinite_of_ne_zero`. Multiplication by `n` is étale by the published
`multiplication_etale_of_field` (module `Langlands.AbelianScheme.AlgClosedPointDivisibility`).
Its composite with the structure morphism `B.X.hom` equals `B.X.hom` (`Over.w`), which is
proper. `IsProper.of_comp` therefore makes multiplication by `n` proper. The published
`Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale` (module
`Langlands.AbelianScheme.TorsionFiniteEtale`) makes it locally quasi-finite. A proper locally
quasi-finite morphism is finite (`IsFinite.of_isProper_of_locallyQuasiFinite`).

`multiplication_isIsogeny_of_ne_zero` combines this finiteness, flatness (an instance of an
étale morphism), and the published `multiplication_surjective_of_field` (same module as
`multiplication_etale_of_field`).

The two kernel lemmas use `kernel_isPullback_scheme`: the kernel's structure morphism is the
base change of multiplication by `n` along the unit section. Finite and étale morphisms are
stable under base change (`MorphismProperty.of_isPullback`).

## Provenance

This is derived infrastructure for the geometric-point nondegeneracy of the finite Weil
pairing (task c063e112), where it supplies the isogeny and the finite étale `n`-torsion
inputs over an algebraically closed field. It adapts Worker 989's draft module
`AlgClosedMultiplicationIsogeny` to the published étaleness and surjectivity results and drops
its algebraic-closure hypothesis. The mathematical content is the case "characteristic does
not divide `n`" of J. S. Milne, *Abelian Varieties* (1986 article, author revision January 2,
2022; registered source `milne-abelian-varieties-1986-author-2022`), Theorem 8.2, p.13:
multiplication by `n > 0` on an abelian variety is an isogeny, étale when the characteristic
does not divide `n`. Milne proves the isogeny property with ample symmetric sheaves. The
Lean proof instead uses étaleness and properness, which needs `(n : K) ≠ 0`. The kernel
statements are the base-change consequences.
