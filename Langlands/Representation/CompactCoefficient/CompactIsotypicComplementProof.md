# The compact-isotypic decomposition: proof

Author: Worker 141. Module `Langlands.Representation.CompactCoefficient.CompactIsotypicComplementProof`, namespace `Langlands.Renard.CompactRepresentation`.

`compactIsotypicComplement` proves exactly the published proposition `CompactIsotypicComplementStatement.{u, v}`. The group universe `u` and the common representation-carrier universe `v` remain independent. All hypotheses and objects are those of the published statement.

## Source and correspondence

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, IV.1.4, Theorem, printed p.90 / PDF p.96, and IV.1.5, Proposition (iii) and Remark 1, printed pp.93–94 / PDF pp.99–100. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The theorem supplies the three conclusions in that proposition: an independent family of images of injective intertwiners from `τ` spanning its isotypic part, exactly one invariant complement, and exclusion of every subquotient of the complement that is isomorphic to `τ`. The last conclusion uses the actual `SmoothRep.IsSubquotient` relation from the statement, with no finite-length premise.

The implementation obtains the projector from the published intrinsic compact-coefficient splitting. Renard constructs it through formal degree and coefficient convolution on pp.91–93. The algebraic steps below implement the direct-sum, uniqueness and subquotient arguments once that splitting is available.

## Independent images

The private lemma `independent_atoms_subset` selects, from any specified set of atoms of a compactly generated modular lattice, an independent subset with the same supremum. Zorn's lemma applies because unions of chains of independent sets remain independent. If an atom is not below the supremum of a maximal independent subset, its intersection with that supremum is zero; modularity then allows it to be adjoined, contradicting maximality.

This argument adapts Mathlib's `exists_sSupIndep_disjoint_sSup_atoms` in `Mathlib/Order/CompactlyGenerated/Basic.lean` (Apache 2.0), with the atom family restricted to a supplied set. It is an internal algebraic lemma supporting the appeal to Lemma A.VII in Renard's proof of IV.1.5(iii).

The private lemma `independent_isotypic_ranges` applies it to the nonzero images of intertwiners from an irreducible representation. The order isomorphism `Subrepresentation.subrepresentationSubmoduleOrderIso` identifies the invariant-subspace lattice with the lattice of submodules over the monoid algebra. Schur's injectivity alternative makes each nonzero image a simple submodule, hence an atom. Choosing one intertwiner for each selected image gives the required set of injective maps. Independence transports back through the order isomorphism, and the zero intertwiner contributes only the bottom subrepresentation. Thus the chosen images have exactly the supremum of all intertwiner images.

## The unique invariant complement

The compact-open cofinality needed by the published splitting follows from `Hecke.TestFunction.commonCompactOpenBiInvariance`, applied to the empty family. Package `τ`, its irreducibility and its compact-coefficient hypothesis as an `IrreducibleCompactCoefficientRep`, and let `c` be its class.

`CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation` gives complementary intrinsic isotypic and annihilator subspaces in every smooth representation. The resulting `isotypicProjectorOfIsCompl` is idempotent and natural. Its published range theorem and the representative formula `isotypicSubrepresentation_eq_iSup_range` identify its range with the exact supremum in the target. Its kernel is the intrinsic annihilator. The range and kernel of this idempotent supply the required complement `K`.

For any invariant complement `S` of the isotypic part `I`, naturality for the inclusion `S → V` shows that the projector maps `S` into `S`. Its image also lies in `I`, so it vanishes on `S`. Consequently `S ≤ K`. The modular-lattice equality criterion on the underlying submodules, together with the two complement identities, gives `S = K`. This proves the existence-and-uniqueness clause, matching IV.1.5, Remark 1.

## Exclusion of subquotients

Apply the published `CompactCoefficientClass.not_isSubquotient_of_range_le_selectedAnnihilator` to the singleton selected set `{c}` and the inclusion of `K` into `V`. The kernel identification places this inclusion's range in the singleton annihilator. The intrinsic splitting already obtained supplies that lemma's complement hypotheses on every intermediate smooth representation.

That published lemma uses naturality to make the projector zero on the annihilator, then on an injected subrepresentation and its surjective image. It fixes `τ`, whose irreducibility makes it nonzero, so `τ` cannot be such a subquotient. These are the zero-descent and identity arguments in Renard's proof after (IV.1.5.1).

Finally, replace any invariant complement by `K` using uniqueness. If an actual subquotient `B` were isomorphic to `τ`, compose the inverse of that isomorphism with the isomorphism in the subquotient presentation. This would exhibit `τ` itself as a subquotient of `K`, a contradiction. This supplies `IsEmpty (B ≅ τ)` exactly as stated.
