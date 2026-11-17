# A common splitting field for two groups of multiplicative type

Author: Worker 3502.

`Langlands.GroupScheme.IsMultiplicativeType.HasCommonSplitting Q N` is a
proposition about two group schemes `Q` and `N` over a field `k : Type u`. It
asks for one field extension `K : Type u` of `k`, two finitely generated
abelian groups `Λ` and `Λ'` in `Type u`, and group-scheme isomorphisms
`Q_K ≅ Diagonalizable.groupScheme K Λ` and
`N_K ≅ Diagonalizable.groupScheme K Λ'`. Base change is along
`Spec K ⟶ Spec k`, exactly as in the published predicate
[`IsMultiplicativeType`](MultiplicativeType.md). The definition is the
conjunction of two such splittings with a shared extension field. It is an
internal, derived notion: Milne, *Algebraic Groups* (2017), Definition 12.17
(source `milne-2017-algebraic-groups`) splits each group separately, and the
common-field version is the standard consequence used when two groups of
multiplicative type are compared.

`IsMultiplicativeType.exists_common_splitting hQ hN` proves that if `Q` and
`N` are both of multiplicative type, then such a common field exists. Its
statement is the unfolded existential, so a caller can destructure it
directly. `IsMultiplicativeType.hasCommonSplitting` restates the same result
with the named predicate.

## Proof

Take splittings of `Q` over `K₁` and of `N` over `K₂` from the two hypotheses.
The published `TorusBaseChange.commonExtension k K₁ K₂` gives a field `E`, a
quotient of `K₁ ⊗[k] K₂` by a maximal ideal, with ring maps `K₁ →+* E` and
`K₂ →+* E` that agree on `k`. The `k`-algebra structure on `E` is the one
through `K₁`, so the first square commutes by definition. The second square
is the compatibility field of the common extension.

A private lemma moves a splitting along any further base change
`c : Spec R' ⟶ Spec R`. It composes three steps:
- the isomorphism between base change along `c ≫ b` and the iterated base
  change, `Functor.mapGrpNatIso (Over.pullbackComp c b)` followed by
  `Functor.mapGrpCompIso`;
- the base change of the given splitting along `c`;
- the published comparison `Diagonalizable.baseChangeIso c Λ`, which
  identifies the base change of a diagonalizable group with the
  diagonalizable group over the new base.

A second private lemma states this for a field map `f : K →+* E` with
`f ∘ (k → K) = (k → E)`. It rewrites `Spec (k → E)` as
`Spec f ≫ Spec (k → K)` using `Spec.map_comp`, `CommRingCat.ofHom_comp` and
that equation. Applying it to `K₁ → E` and `K₂ → E` gives both isomorphisms
over `E`. The character groups `Λ`, `Λ'` and their finite generation are
the ones from the original splittings.

No separability, Galois, connectedness or smoothness condition is used or
asserted. The extension field `E` is not claimed to be finite over `k`.
