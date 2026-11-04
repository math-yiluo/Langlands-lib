# Central extensions of split tori by split tori are split tori

Worker 1395 wrote this module. It proves the split, affine case of
`CentralTorusExtensionStatement`. The general case is in
[`CentralExtensionProof`](CentralExtensionProof.md).

## Contents

* `RelativeRoot.IsFppfQuotient.comp_iso h e`: if `q : H ⟶ Q` is an fppf
  quotient map with kernel `N` and `e : Q ≅ Q'`, then `q ≫ e.hom` is an fppf
  quotient map with kernel `N`. Flatness, surjectivity and local finite
  presentation are preserved by composing with an isomorphism
  (`MorphismProperty.cancel_right_of_respectsIso`). The kernel is unchanged
  because `e` induces group isomorphisms on points (`isoPointsEquiv`).
* `CentralExtensionHopfSpec.isSplitTorus_of_split`: let `K` be a field and `E`,
  `Z`, `T` group schemes over `Spec K` with `E` affine. Let `I`, `J` be finite
  types with `Z ≅ splitTorus _ J` and `T ≅ splitTorus _ I`. Let `z : Z ⟶ E`
  satisfy `IsClosedSubgroup z` and `IsCentral z`, and let `p : E ⟶ T` satisfy
  `IsFppfQuotient (SubgroupFunctor.range z) p`. Then `IsSplitTorus E`, with
  index type `I ⊕ J`.

## Proof of `isSplitTorus_of_split`

1. Identify `E` with the spectrum of its coordinate Hopf algebra
   `A = AffineCoordinates.hopfAlgebra E` (`AffineCoordinates.hopfSpecIso`), and
   `Z`, `T` with the spectra of `K[ℤ^J]`, `K[ℤ^I]`
   (`Diagonalizable.hopfSpecIso`, `Diagonalizable.splitIso`).
2. `hopfSpec` is fully faithful, so the transported `z` and `p` are spectra of
   Hopf algebra maps `π : A ⟶ K[ℤ^J]` and `φ : K[ℤ^I] ⟶ A`.
3. The hypotheses transport along these isomorphisms: `IsClosedSubgroup.iso_comp`
   and `comp_iso`, `IsCentral.comp_iso` and `comp`, `IsFppfQuotient.comapIso`,
   `IsFppfQuotient.comp_iso`, and `SubgroupFunctor.range_iso_comp` and
   `range_comp_iso`.
4. [`CentralExtensionHopfSpec.isCentralExtension`](CentralExtensionHopfSpec.md)
   gives `IsCentralExtension φ π`. Then
   [`CentralTorusExtensionHopf`](../../Algebra/CentralTorusExtensionHopf.md)
   gives that the group-like elements span `A` and form a group
   `≃ ℤ^(I ⊕ J)` (`groupLikeEquiv`).
5. A Hopf algebra spanned by its group-like elements is the group algebra of
   those elements (`Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike`, from
   the Library). `AffineCoordinates.isoOfBialgEquiv` turns this bialgebra
   equivalence into an isomorphism of `E` with the spectrum of
   `K[GroupLike K A]`. Composed with `Diagonalizable.splitIso` along
   `groupLikeEquiv`, this is an isomorphism `E ≅ splitTorus _ (I ⊕ J)`.

## Source

The geometric statement is the split case of the result discussed in
[`CentralTorusExtensionStatement`](CentralExtensionStatement.md) (Milne,
*Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Corollaries 12.41 and 12.22, printed pp.244 and 239, one-based PDF pp.260 and
255). Step 5 is Milne's Theorem 12.8 (printed p.233, one-based PDF p.249): an
algebraic group whose coordinate ring is spanned by group-like elements is
diagonalizable. The Lean route through Hopf algebras is internal to this
project.
