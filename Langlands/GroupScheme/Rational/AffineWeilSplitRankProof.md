# Split rank and affine Weil restriction

Author: Worker 117.

## Exact result

`Langlands.GroupScheme.affineWeilSplitRank.{u}` proves exactly the published
`Langlands.GroupScheme.AffineWeilSplitRankStatement.{u}`. For fields `k K : Type u`,
an algebra structure `k → K`, a finite-dimensional separable extension, and a
group scheme `G` over `Spec K` satisfying `IsConnectedReductive G`, it gives

```text
splitRank (AffineWeil.groupScheme k K G) = splitRank G
```

in `ℕ∞`. The theorem obtains affineness and local finite type from the given
connected reductive hypothesis exactly as in the target definition. It adds
no premise or datum and imposes no restriction on the characteristic. Its
universe parameter is arbitrary.

The target pair and every file in its import closure are preserved. The new
module imports existing constructions by their Lean names.

## Implemented proof

Write `D_k(Λ)` for the character functor `latticeFunctor (CommRingCat.of k) Λ`.
The internal helpers in `AffineWeil.Rank` apply the published image-lattice
construction to homomorphisms out of this functor.

1. **Detecting a proper image lattice.** For a subgroup `M ⊆ Λ`,
   `quotientChar k M` is the character with values in `k[Λ/M]ˣ` sending `m`
   to the monomial of its quotient class. Its restriction to `M` is trivial.
   If this whole character is trivial, the linear independence of the
   monomials, with `1 ≠ 0` in `k`, forces `M = ⊤`.

   The published `imageSubgroup`, `imageHom`, and
   `latticeMap_comp_imageHom` factor any natural homomorphism through its
   image lattice. Consequently a character trivial on the image lattice
   maps to the identity. An injective natural homomorphism therefore has
   full image lattice: test it on `quotientChar`. The published
   `mem_range_iff` then makes its classifying algebra map surjective. This
   is `classify_surjective_of_injective`.

2. **The adjunction identity.** `rightInclusion` is the algebra map
   `C → K ⊗[k] C`, `c ↦ 1 ⊗ c`, with the restricted scalar structure.
   Tensoring this inclusion and then applying the multiplication map is
   the identity on `K ⊗[k] C`. Naturality gives
   `unitTrans k G (counitTrans k G α) = α` for a natural homomorphism
   `α : D_k(Λ) ⟶ AffineWeil.pointFunctor k K G`.

3. **A closed split torus in the restriction.** Suppose `α` is injective
   on every algebra test. Apply the image-lattice construction over `K`
   to its counit followed by the coordinate comparison of `G`. Let `M`
   be that image lattice. The scalar extension of `quotientChar k M`
   remains trivial on `M`, so the counit maps it to the identity.
   The adjunction identity implies that `α` kills `quotientChar k M`.
   Injectivity of `α` forces `M = ⊤`. Thus the counit's classifying map
   is surjective (`counit_classify_surjective`).

   A closed embedding of `splitTorus k I` in the restriction gives such
   an injective `α` by cancellation of the underlying monomorphism.
   `isClosedSubgroup_groupSchemeMap` turns the surjective classifying
   map into a closed embedding over `K`. `torusIso` and
   `AffineCoordinates.groupSchemeIso` identify its source and target
   with the actual published split torus and `G`. This proves
   `exists_embedding_of_weil`, with the same finite index type `I`.

4. **A closed split torus in the original group.** A closed embedding
   of `splitTorus K I` in `G` gives an injective natural homomorphism
   `β : D_K(FreeAbelianGroup I) ⟶ G.affinePointFunctor`. The unit map
   on characters is injective because `C → K ⊗[k] C` is injective:
   `C` is flat over the field `k` and `k → K` is injective.
   Hence `unitTrans k G β` is injective. Step 1 makes its classifying
   map surjective, and the same closed-subgroup bridge and `torusIso`
   produce `exists_weil_embedding`, again with the same `I`.

5. **Taking suprema.** For each finite `I`, these two constructions
   transport every closed split-torus embedding. Apply
   `card_le_splitRank` to the resulting embedding. The four nested
   supremum bounds in the definition of `splitRank` give the two
   inequalities; `le_antisymm` gives the claimed equality.

The image-lattice and adjunction helpers are derived content supplied for this
proof. They work without a separability hypothesis. The two embedding lemmas
require the affine finite-type Weil restriction construction; the final theorem
retains all the hypotheses of the published target. No maximal-torus existence,
conjugacy, or rank-finiteness comparison is needed for the supremum argument.
Neither `LocalKneserTitsStatement` nor its planned consumers occurs in the proof.

## Original sources and comparison

Armand Borel and Jacques Tits, *Groupes réductifs* (1965), registered
`borel-tits-1965-groupes-reductifs`: 6.17–6.21, printed pp.111–112 /
PDF pp.58–59. Section 6.17 sets up the finite separable restriction and
its adjunction; 6.19 treats maximal tori; 6.20 compares character groups
and the dimensions of split parts; 6.21(i) states equality of split ranks
for connected reductive groups. This is the source of the target.

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*,
second edition (2015), registered
`conrad-gabber-prasad-2015-pseudo-reductive`: (A.5.1), printed p.504 /
PDF p.530, and Proposition A.5.15(2) with its proof, printed pp.520–523 /
PDF pp.546–549. These passages give the adjunction and the correspondence
of maximal split tori via the canonical scalar-extension map to the
original group.

The Lean implementation supplies a direct group-algebra kernel argument for
closed split-torus embeddings and then compares the defining suprema.
It does not reproduce the sources' proofs through maximal tori, and does
not assert an additional identification of the supremum with the classical
dimension definition of rank.
