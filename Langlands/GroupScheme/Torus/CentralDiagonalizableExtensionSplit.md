# Central extensions of split tori by diagonalizable groups are diagonalizable

Worker 603 wrote this module for Task 6776, part 2 of
[`MultiplicativeTypeFieldExtensionStatement`](MultiplicativeTypeFieldExtensionStatement.md)
(SGA 3, Exposé IX, Proposition 8.2 (ii), over a field).

It generalizes [`CentralExtensionSplit`](CentralExtensionSplit.md) (Worker
1395) from a split-torus kernel to a diagonalizable kernel `D_k(Λ)`, with `Λ`
finitely generated and torsion allowed. It then removes the auxiliary
hypotheses: affineness of the middle group and closedness of the kernel are
derived from the target's hypotheses. Centrality remains a hypothesis, and the
last theorem obtains it from part 1 of the target.

## Contents

### Hopf-algebra translation (`Langlands.GroupScheme.CentralExtensionHopfSpec`)

* `isCentralExtension_diagonalizable φ π hz hc hq`: let
  `φ : K[ℤ^I] ⟶ A` and `π : A ⟶ K[Λ]` be maps of commutative Hopf algebras
  over a field `K`. Suppose `Spec π` is a central closed subgroup of `Spec A`,
  and `Spec φ` is an fppf quotient map with kernel the range of `Spec π`. Then
  `φ` and `π` satisfy
  [`CentralDiagonalizableExtensionHopf.IsCentralExtension`](../../Algebra/CentralDiagonalizableExtensionHopf.md).
  The proof is that of the Library's `CentralExtensionHopfSpec.isCentralExtension`,
  with `K[ℤ^J]` replaced by `K[Λ]`. The general lemmas of
  [`CentralExtensionHopfSpec`](CentralExtensionHopfSpec.md) do not depend on
  the target group algebra:
  - `faithfullyFlat_of_isFppfQuotient`: `φ` is injective.
  - `surjective_of_isClosedSubgroup`: `π` is surjective.
  - `comp_eq_of_range_kernelι`: `π ∘ φ` is trivial.
  - `rTensor_comul_eq_of_isCentral`: `π` is central.
  - `exists_eq_of_lTensor_comul_eq`: the invariants are the image of `φ`.
* `exists_iso_diagonalizable_of_split`: let `E` be a group scheme over a
  field `K` with affine total space, `z : Z ⟶ E` a central closed subgroup,
  and `p : E ⟶ T` an fppf quotient map with kernel the range of `z`. Assume
  `Z ≅ D_K(Λ)` with `Λ` finitely generated, and `T ≅ 𝔾_m^I` with `I` finite.
  Then `E ≅ D_K(Λ')` with `Λ' = Additive (GroupLike K A)` finitely generated,
  where `A` is the coordinate Hopf algebra of `E`. The proof follows
  `CentralExtensionHopfSpec.isSplitTorus_of_split`:
  1. Identify `E` with `Spec A` (`AffineCoordinates.hopfSpecIso`), `Z` with
     the spectrum of `K[Λ]` (`Diagonalizable.hopfSpecIso`), and `T` with the
     spectrum of `K[ℤ^I]` (`Diagonalizable.hopfSpecIso`,
     `Diagonalizable.splitIso`).
  2. Full faithfulness of `hopfSpec` turns `z` and `p` into Hopf algebra maps
     `π` and `φ`. The hypotheses transport along these isomorphisms.
  3. `isCentralExtension_diagonalizable` and
     `CentralDiagonalizableExtensionHopf.span_isGroupLikeElem` show that the
     group-like elements span `A`.
  4. `Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` and
     `AffineCoordinates.isoOfBialgEquiv` give
     `E ≅ Spec K[GroupLike K A] ≅ D_K(Additive (GroupLike K A))`.
  5. `CentralDiagonalizableExtensionHopf.addGroupFG` gives finite generation.

### Hypotheses from the extension (`Langlands.GroupScheme.RelativeRoot.IsFppfQuotient`)

* `isAffineHom_of_isAffineHom_kernel i hq`: let `i : H ⟶ G` be a monomorphism
  and `p : G ⟶ K` an fppf quotient map with kernel the range of `i`. If `H` is
  affine over the base, then `p` is an affine morphism. The quotient pullback
  `G ×_K G` is `G × H` (`QuotientCell.multiplication_isPullback`), whose first
  projection is affine. Affineness descends along the fppf cover `p` (fpqc
  descent `affine_descendsAlong_fpqc` from
  [`SchemeFlatPropertyDescent`](../../AlgebraicGeometry/SchemeFlatPropertyDescent.md),
  upgraded to fppf descent by Mathlib's `FlatDescent`). This repeats the proof
  of `isAffineHom_of_kernel` in Worker 312's helper module
  `MultiplicativeTypeExtensionHelpers` (staged for the same task, not yet
  published when this module was written).
* `isClosedSubgroup_of_field i hq`: over a field, such an `i` is a closed
  subgroup. By `IsFppfQuotient.kernelIso_hom_comp`, `i` is an isomorphism onto
  the actual kernel followed by `kernelι p`. The latter is a closed immersion
  because `K` is separated over the field (`fieldSeparated`).

### Part 2 (`Langlands.GroupScheme`)

* `exists_iso_diagonalizable_of_isCentral i p hq hc hH hK`: over a field `k`,
  let `i : H ⟶ G` be a monomorphism and `p : G ⟶ K` an fppf quotient map with
  kernel the range of `i`. Assume:
  - `i` is central;
  - `H ≅ D_k(Λ)` with `Λ` finitely generated;
  - `K` is a split torus.

  Then `G ≅ D_k(Λ')` for a finitely generated `Λ'`. The group `G` is affine:
  `p` is affine by `isAffineHom_of_isAffineHom_kernel`, since diagonalizable
  groups are affine (`Diagonalizable.isAffineHom`), and so are split tori
  (`IsSplitTorus.isAffineHom`). The subgroup `i` is closed by
  `isClosedSubgroup_of_field`. Then apply
  `exists_iso_diagonalizable_of_split`.
* `exists_iso_diagonalizable_of_isCommMonObj`: the same with `G` commutative
  instead of `i` central. Commutativity makes every subgroup central.
* `isMultiplicativeType_of_iso_diagonalizable`: a group isomorphic to `D_k(Λ)`
  with `Λ` finitely generated is of multiplicative type. The trivial extension
  `k / k` splits it (`Diagonalizable.baseChangeIso`,
  `IsMultiplicativeType.of_iso`).
* `exists_iso_diagonalizable_of_part_one i p hq h1 hH hK`: part 2 of the
  target, with the conclusion of part 1 for this extension as the hypothesis
  `h1`. The group `H` is of multiplicative type
  (`isMultiplicativeType_of_iso_diagonalizable`). So is `K`, by
  `IsSplitTorus.isTorus` and `IsTorus.isMultiplicativeType`, and `K` is
  connected (`IsSplitTorus.connectedSpace`). Then `h1` makes `G` of
  multiplicative type, hence commutative
  (`IsMultiplicativeType.isCommMonObj`), and
  `exists_iso_diagonalizable_of_isCommMonObj` applies.

  The full target then follows from a proof `part1` of part 1 as
  `⟨part1 …, fun hH hK => exists_iso_diagonalizable_of_part_one i p hq (part1 …) hH hK⟩`.

## Provenance

Internal to this project. The geometric statement is SGA 3, Exposé IX,
Proposition 8.2 (ii), over a field (see the target statement's Markdown). The
source classifies the Galois twists of the split extension. This module
instead uses centrality, which follows from part 1, and the Hopf-algebra
argument of [`CentralDiagonalizableExtensionHopf`](../../Algebra/CentralDiagonalizableExtensionHopf.md).
That argument works over `k` itself: the Picard group of `k[ℤ^I]` is trivial
and the units of `k[ℤ^I ⊕ ℤ^I]` are scalar multiples of monomials.
