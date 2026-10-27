# Proof of ordinary eigenvector extraction for generalized normalized Jacquet exponents

Author: Worker 219.

The theorem `Langlands.glJacquetExponentEigenvector` has the complete
unapplied type `Langlands.GLJacquetExponentEigenvectorStatement.{uF,uV}`,
imported from `Langlands.Representation.Exponents.JacquetEigenvectorStatement`.
It adds no hypotheses, and the field universe `uF` and the carrier universe
`uV` stay independent. The module also imports
`Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof` for
the published theorem `Langlands.Parabolic.normalizedJacquetAdmissibility`.

The proof is project-internal linear algebra. It follows the route sketched in
the "Original source and derived provenance" section of the statement's
Markdown, with one simplification described below: the eigencharacter is
`χ` by construction, so no comparison between an auxiliary eigencharacter
`λ` and `χ` is needed. The literature context, Waldspurger 2003, §I.2–I.3 and
the proof of Proposition III.2.2, is recorded in the statement's Markdown.
This proof does not use that source directly.

## Generic linear algebra

The section `Generic` works over an arbitrary field `K`, a commutative monoid
`A`, a `K`-vector space `W` and a representation `π : Representation K A W`.
It uses the published `Langlands.characterSpace π χ k`: the vectors killed by
`(π a - χ a • 1) ^ k` for every `a`.

- `commute_sub_smul_one`: each shifted operator `π a - c • 1` commutes with
  every `π b`, because `π a * π b = π (a * b) = π (b * a) = π b * π a`.
- `map_mem_characterSpace`: every `π a` maps `characterSpace π χ k` into
  itself. By the previous lemma, `π a` commutes with each power
  `(π b - χ b • 1) ^ k`.
- `exists_mem_ker_of_pow_eq_zero`: let an operator `N` map a submodule `U`
  into itself, and let `N ^ k` kill `U`. If `U` contains a nonzero vector,
  then `U` contains a nonzero vector killed by `N`. Suppose no such vector
  exists. Induction on `j` then shows that every `w ∈ U` with
  `(N ^ j) w = 0` is zero. For `j + 1`, apply the induction hypothesis to
  `N w ∈ U`; this gives `N w = 0`, so `w = 0` by the assumption. The case
  `j = k` contradicts the nonzero vector of `U`.
- `exists_eigenvector_of_mem_characterSpace`: let a finite-dimensional
  subspace `S` be stable under every `π a`, and let it contain a nonzero
  vector `v` of `characterSpace π χ k`. Then some nonzero `w` satisfies
  `π a w = χ a • w` for every `a`.

  Proof. Consider the nonzero submodules `U ≤ S ⊓ characterSpace π χ k` that
  are stable under every `π a`. The subspace `S ⊓ characterSpace π χ k` is
  one of them. It contains `v`, and it is stable by the hypothesis on `S`
  and `map_mem_characterSpace`. Choose such a `U` of least `finrank`
  (`Nat.find`); `U` is finite-dimensional since `U ≤ S`. Fix `a` and put
  `N = π a - χ a • 1`. Then `N` maps `U` into itself, and `N ^ k` kills `U`
  because `U ≤ characterSpace π χ k`. By `exists_mem_ker_of_pow_eq_zero`,
  the submodule `U' = U ⊓ ker N` is nonzero. It is stable under every `π b`,
  because `N` commutes with `π b`. Suppose `U ≰ ker N`. Then `U' < U`, so
  `finrank U' < finrank U` (`Submodule.finrank_lt_finrank_of_lt`). This
  contradicts minimality. Hence `U ≤ ker (π a - χ a • 1)` for every `a`.
  Any nonzero vector of `U` is the required common eigenvector.

  One minimal `U` serves for all `a` simultaneously. The eigencharacter is
  `χ` itself, because `U` lies in the kernel of each `π a - χ a • 1`.

## The normalized Jacquet module

The namespace `Langlands.Parabolic` contains four lemmas for a prime `p`, a
field `F : PadicField.{uF} p`, data `T : F.TopologicalData`, a block shape
`B` and a representation `ρ` of `GL_n(F)` on `V`.

- `twist_inverseHalfCharacter_leviCoinvariants_apply` and
  `twist_inverseHalfCharacter_leviCoinvariants`: the representation
  `twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
  (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype))` equals
  `T.normalizedJacquet B ρ`. The proof does not use a definitional
  identification of the two presentations. It compares their values on each
  class `B.jacquetMk ρ v`, which suffices by `B.jacquetMk_surjective`. The
  right side is rewritten by `T.normalizedJacquet_mk`. On the left side,
  the twist contributes the scalar factor from `Jacquet.inverseHalfCharacter_apply`,
  and `leviCoinvariants_mk` computes the coinvariant action on the class.
  The two resulting expressions then agree by `rfl`. Extensionality
  (`MonoidHom.ext`, `LinearMap.ext`) gives the equality of representations.
- `isAdmissible_normalizedJacquet`: with the topology `T.topology`, if `ρ`
  is admissible, then so is `T.normalizedJacquet B ρ`. The published
  `normalizedJacquetAdmissibility F T B V ρ` proves admissibility of the
  inverse-half twist of the coinvariants; rewriting by the previous equality
  gives the claim.
- `splitCentreJacquet_mem_fixedVectors`: for every subgroup `L` of the Levi,
  the split-centre operator `T.splitCentreJacquet B ρ a` maps
  `fixedVectors (T.normalizedJacquet B ρ) L` into itself. The element
  `B.blockScalarLevi F.Carrier a` is central in the Levi
  (`blockScalarLevi_mem_center`). For `l ∈ L` and a fixed vector `w`, the
  action of `l` on the image of `w` equals the image of the action of `l` on
  `w`, which is the image of `w`.

## The main theorem

`Langlands.glJacquetExponentEigenvector` introduces the telescope and sets
the local topology `T.topology`. Let `ρ` be admissible and let `χ` satisfy
`T.IsJacquetExponent B ρ χ`. Only the generalized-eigencharacter part of that
predicate is used; the open-kernel part is not needed.
`isGeneralizedEigencharacter_iff` gives a power `k` and a nonzero vector `v`
of `characterSpace (T.splitCentreJacquet B ρ) χ k`.

By `isAdmissible_normalizedJacquet`, the normalized Jacquet representation is
admissible. Its smoothness part gives an open subgroup `L` of the Levi fixing
`v`. Its finiteness part shows that
`S = fixedVectors (T.normalizedJacquet B ρ) L.toSubgroup` is
finite-dimensional. `S` is stable under the split centre by
`splitCentreJacquet_mem_fixedVectors`. Then
`exists_eigenvector_of_mem_characterSpace`, applied to
`π = T.splitCentreJacquet B ρ`, `S` and `v`, gives a nonzero
`w : B.JacquetModule ρ` with `T.splitCentreJacquet B ρ a w = χ a • w` for
every block-scalar tuple `a`. This is the conclusion of the statement.

Only the fixed space `S` is finite-dimensional; the Jacquet module itself may
be infinite-dimensional. Zero carriers need no separate case, since they
admit no nonzero generalized-character witness.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
