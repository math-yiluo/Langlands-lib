# Statement: groups of multiplicative type over a field split over a finite Galois extension

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeFiniteGaloisSplittingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
`IsMultiplicativeType` and, through it, the diagonalizable groups
`Diagonalizable.groupScheme`, and Mathlib's `Mathlib.FieldTheory.Galois.Basic`, for
`IsGalois`.

## Lean statement

```lean
def MultiplicativeTypeFiniteGaloisSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k))), IsMultiplicativeType H →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
        Nonempty (((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) ≅
            (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
```

- `k` is an arbitrary field in universe `u`. It need not be perfect, infinite or of
  characteristic zero.
- `H` is a group scheme over `Spec k` (`GroupScheme S` is `Grp (Over S)`). The only
  hypothesis is `IsMultiplicativeType H` (module `Langlands.GroupScheme.Torus.MultiplicativeType`):
  there are a field `K₀ : Type u`, an algebra `k → K₀`, a finitely generated abelian group
  `Λ₀ : Type u` and an isomorphism of group schemes over `Spec K₀` from the base change of `H`
  along `Spec K₀ ⟶ Spec k` onto `Diagonalizable.groupScheme (CommRingCat.of K₀) Λ₀`, the
  diagonalizable group `D_{K₀}(Λ₀) = Spec K₀[Λ₀]`. The predicate puts no condition on
  `K₀ / k`, and does not assume that `H` is affine or of finite type.
- The conclusion gives a field `K : Type u` with an algebra `k → K` such that
  `FiniteDimensional k K` and `IsGalois k K` (Mathlib: separable and normal); together these
  say that `K / k` is a finite Galois extension. It also gives a finitely generated abelian
  group `Λ : Type u` and an isomorphism of group schemes over `Spec K` from the base change
  of `H` along `Spec K ⟶ Spec k` onto `D_K(Λ)`. The base change is the published functor
  `GroupScheme.baseChange`, the same one used in `IsMultiplicativeType`.
- The trivial group is covered with `Λ = 0`, and so are finite groups of multiplicative
  type such as `μ_n`, whose `Λ` has torsion.

## Sources

- James S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  file `Milne--Algebraic groups, the theory of group schemes of finite type over a field
  (book)--2017.pdf`. Page numbers are printed page numbers.
  - Definition 12.17 (p.236): "An algebraic group over k is of multiplicative type if it
    becomes diagonalizable over some field containing k."
  - Theorem 12.18 (p.237): (a) `G` is of multiplicative type is equivalent to (d) `G`
    becomes diagonalizable over `k_s`.
  - Corollary 12.19 (p.238): "If an algebraic group over k becomes diagonalizable over some
    extension of k, then it becomes diagonalizable over a finite separable extension of k."
- Brian Conrad, *Reductive group schemes* (2014), source ID
  `conrad-2014-reductive-group-schemes`, file
  `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Lemma B.1.5, p.283:
  "Let k be a field. A k-group H of multiplicative type splits over a finite separable
  extension of k." Conrad's multiplicative type is fppf-local diagonalizability over `Spec k`
  (Definition B.1.1, p.280), and "splits" means isomorphic to `D(M)` for a finitely generated
  abelian group `M`.
- SGA 3, Exposé X (Gille–Polo recomposed edition, 8 November 2009), source ID
  `sga3-expose-x-gille-polo-2009`, Proposition 1.4 (recomposed p.64, original margin p.79):
  over a field `k`, every group of multiplicative type and of finite type is split by a
  finite separable extension `k'` of `k`.

## Derivation from the sources

The statement is Milne's Corollary 12.19 (equivalently Conrad's Lemma B.1.5 or SGA 3 X 1.4)
in the Library's vocabulary, with two changes that need no new idea.

- **Hypothesis.** `IsMultiplicativeType H` is Milne's Definition 12.17 with the splitting
  over `K₀` made explicit, except that it does not assume `H` of finite type. A
  diagonalizable group `D_{K₀}(Λ₀)` with `Λ₀` finitely generated is affine and of finite
  type over `K₀`, and these properties descend along the fpqc morphism `Spec K₀ ⟶ Spec k`.
  So `H` is an algebraic group in Milne's sense and Corollary 12.19 applies. Conrad's
  fppf-local hypothesis implies `IsMultiplicativeType H`: an fppf cover of `Spec k`
  acquires a point over a finite extension of `k`, as noted in Conrad's proof.
- **Conclusion.** The sources give a finite separable extension `k'`. Its Galois closure
  `K`, taken inside an algebraic closure of `k` so that `K : Type u`, is finite Galois over
  `k`. Base change of `D_{k'}(Λ)` along `Spec K ⟶ Spec k'` is `D_K(Λ)`, and base change
  along `Spec k' ⟶ Spec k` followed by `Spec K ⟶ Spec k'` is base change along
  `Spec K ⟶ Spec k`. So `H` is diagonalizable over `K` with the same `Λ`. Conversely a
  finite Galois extension is finite separable, so the statement implies the sources' form.

## Related Library statements

- `TorusFiniteGaloisSplittingStatement`
  ([`Torus.FiniteGaloisSplittingStatement`](FiniteGaloisSplittingStatement.md)) is the
  special case of tori, with the conclusion `IsSplitTorus`.
- `MultiplicativeTypeGaloisExactnessStatement`
  ([`Torus.MultiplicativeTypeGaloisExactnessStatement`](MultiplicativeTypeGaloisExactnessStatement.md))
  and `MultiplicativeTypeGaloisFullFaithfulnessStatement`
  ([`Torus.MultiplicativeTypeGaloisFullFaithfulnessStatement`](MultiplicativeTypeGaloisFullFaithfulnessStatement.md))
  are about objects of `CommGroupScheme` with diagonalizable models over a given finite
  Galois extension. This statement says that every group of multiplicative type has such
  an extension; it does not relate `GroupScheme` and `CommGroupScheme` objects.
