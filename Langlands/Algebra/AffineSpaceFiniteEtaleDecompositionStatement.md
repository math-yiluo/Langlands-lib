# Polynomial product decomposition for finite étale covers of affine space

`Langlands.Algebra.AffineSpaceFiniteEtalePolynomialProductStatement.{u}` is a
`Prop`-valued definition. It states a ring-theoretic consequence of the classification
of finite étale covers of affine space in characteristic zero. This module supplies
the statement; it does not prove it.

For a field `k : Type u` of characteristic zero, a natural number `n`, and a
commutative ring `A : Type u` with an algebra structure over
`MvPolynomial (Fin n) k`, assume that this algebra is étale and module-finite.
The conclusion supplies a type `ι : Type u` with `Finite ι`, a family of fields
`K i : Type u`, and a ring isomorphism

```text
A ≃+* ∀ i, MvPolynomial (Fin n) (K i).
```

The conclusion retains only the ring isomorphism. It does not give `k`-algebra
structures on the fields, assert their degrees, or identify the isomorphism with
a map over the polynomial base. These omissions weaken the usual classification
and suffice for the Picard-group application. The family may be empty, covering
the zero ring. The number of variables may be zero.

## Provenance and source comparison

This is a derived statement. It is not a verbatim proposition in Conrad and is
stronger than the Picard-group consequence used in his remark.

Brian Conrad, *Reductive group schemes* (2014), Remark 7.2.13, p.259,
registered source `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
identifies affine spaces over fields of characteristic zero as bases for which
every finite étale cover has trivial Picard group. This motivates the present
prerequisite for the published
`Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement`.
The decomposition itself uses the following standard geometric argument.

The source for the geometric inputs is SGA 1, *Revêtements étales et groupe
fondamental*, recomposed and annotated edition, arXiv math/0206203v2,
registered as `sga1-arxiv-math-0206203v2`, SHA-256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
Page references below use the recomposed printed pagination; the PDF page is
16 greater.

1. Over an algebraically closed field of characteristic zero, the affine line
   has trivial étale fundamental group. In SGA 1, XIII, Corollary 2.12 and its
   proof, pp.290–291 (PDF 306–307), set the smooth completed curve to
   the projective line, its genus to zero, and the number of removed points
   to one. The single inertia generator satisfies the relation that it is
   the identity. In characteristic zero every finite cover is tame, so this
   concerns the full étale fundamental group.
2. SGA 1, XIII, Proposition 4.6, pp.310–311 (PDF 326–327), gives the
   prime-to-characteristic Künneth isomorphism, under its stated strong
   desingularization hypotheses. In characteristic zero resolution of
   singularities supplies these hypotheses and all primes are permitted.
   Apply it repeatedly to products of affine lines. Thus affine `n`-space
   has no nontrivial connected finite étale covers over an algebraic
   closure. In dimension zero this follows directly for the spectrum of
   an algebraically closed field.
3. SGA 1, IX, Theorem 6.1 and Corollary 6.2, pp.195–196 (PDF 211–212),
   apply to the geometrically connected, quasi-compact scheme
   `X = 𝔸ⁿ_k` over `Spec k`. A finite étale cover that becomes completely
   decomposed over an algebraic closure is pulled back from a finite étale
   cover of `Spec k`. A finite étale `k`-algebra is a finite product of
   finite separable field extensions `K i`. The associated pullback has
   coordinate ring `∏ i, K i[x₁, …, xₙ]`. Forgetting its algebra
   compatibility gives precisely the asserted ring isomorphism.

These are explanations of the mathematical derivation, not implemented Lean
proofs of the geometric inputs. In particular, the desingularization and
finite-étale descent steps remain part of the proof obligation.
No additional hypotheses of the geometric source are silently required of
`A`: affine space satisfies the geometric-connectedness and finiteness
conditions, and the characteristic-zero assumption is explicit.

For universe size, the finite index set and the coefficient fields can be
realized in `Type u`: there are finitely many factors and each coefficient
field is a finite extension of `k : Type u`. The Lean statement asserts this
size-controlled form.

## Intended use

The companion module `Langlands.Algebra.AffineSpaceFiniteEtalePicardReduction`
proves that this statement implies the published Picard-group target. Its
algebraic steps use unique factorization for polynomial rings over fields,
the finite-product Picard lemma, and transport along a ring isomorphism.
The decomposition remains an explicit hypothesis in that reduction.
