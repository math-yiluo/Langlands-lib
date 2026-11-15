# Big-cell gluing from simple-root generator relations

This internal derived criterion sharpens the generator-relation gluing criterion of
`Langlands.GroupScheme.Reductive.LocalSplitGeneratorRelations` for root families
built from simple-root data by Weyl conjugation (`LocalSplitCell.weylFamily`, module
`Langlands.GroupScheme.Reductive.LocalSplitWeylFamily`). The base ring is arbitrary
and may have nilpotents. Two kinds of right-translation relations remain as
hypotheses: those for the simple-root points `u_a(c)` and those for the points
`u_{-a}(-1)`. The criterion does not require relations for the points of the other
roots, and it does not require torus relations.

## Statement

`LocalSplitSimpleRootRelationIsomorphismStatement.{u}` concerns:

- a commutative ring `R`, a finite type `I` with decidable equality, and a type `J`,
  all in universe `u`;
- reductive group schemes `G`, `H` over `Spec R`. The statement also takes instance
  binders `IsAffineHom` for their structure morphisms, which the definition of
  `IsFibrewiseRootDatumOf` needs. Reductivity already includes this property;
- coordinate split tori `i : T_I → G` and `i' : T_I → H`, both maximal on every
  residue-field fibre (`IsFibrewiseMaximalTorus`);
- one coordinate root datum `P : RootDatum J (I → ℤ) (I → ℤ)` that is a fibrewise
  root datum (`IsFibrewiseRootDatumOf`) both for `i` in `G` and for `i'` in `H`;
- a base `b` of `P` and a choice `W` of a `SimpleWord P b α` for every root `α`
  (a simple root and a word in simple reflections carrying it to `α`);
- families `u : J → (𝔾ₐ ⟶ G)` and `u' : J → (𝔾ₐ ⟶ H)`. For every simple root `a`,
  `u a` is a root parametrization of `i` for `P.root a` (`IsRootParametrization`).
  Also, `rootWeylPoint P u a = u_{-a}(-1) u_a(1) u_{-a}(-1)` is a Weyl point of `i`
  acting by the reflection `P.reflection a` (`IsWeylPoint`). Here `u_{-a}` means
  `u (P.reflectionPerm a a)`, the member of `u` at the index of the root `-P.root a`.
  The same conditions hold for `u'` and `i'`. The members of `u` at the other indices
  are not constrained. The members at the negative simple roots enter only through
  the Weyl points;
- enumerations `neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}`
  of the non-positive and the positive roots.

Let `Ω = cellMap i (weylFamily P W u) neg pos` and
`Ω' = cellMap i' (weylFamily P W u') neg pos` be the big-cell maps of the two Weyl
families, with common source `𝔾ₐᵐ × T_I × 𝔾ₐⁿ`. The statement has two hypotheses.
Each concerns every commutative local ring `A : Type u` with separably closed residue
field, every structure map `s : Spec A → Spec R`, all cell-source points `x`, `y`
over `s`, and every simple root `a ∈ b.support`:

- **simple-root relations:** for every global function `c` on `Spec A`, if
  `Ω(x) · u_a(c) = Ω(y)` in `G`, then `Ω'(x) · u'_a(c) = Ω'(y)` in `H`;
- **negative simple relations:** if `Ω(x) · u_{-a}(-1) = Ω(y)` in `G`, then
  `Ω'(x) · u'_{-a}(-1) = Ω'(y)` in `H`.

The conclusion is an isomorphism `ψ : G ≅ H` with `Ω ≫ ψ = Ω'`. The module proves
this proposition at full universe as `localSplitSimpleRootRelationIsomorphism`.

The section `LocalSplitCell.WeylGenerators` contains the general results:

- `SimpleRootRelations` and `NegSimpleRelations` are the two hypotheses above, for
  arbitrary maps `Ω`, `Ω'` from the cell source;
- `rootRelations_weylFamily`: these two hypotheses imply the root relations
  `RootRelations Ω Ω' (weylFamily P W u) (weylFamily P W u')` of
  `LocalSplitGeneratorRelations`, for every root;
- `exists_iso_of_simpleRootRelations`: the same conclusion as the proposition for any
  enumerations `neg`, `pos` whose two cell maps are open immersions, without the
  fibrewise torus and root-datum hypotheses.

## Proof

All right-goodness statements refer to `RightGood Ω Ω'` of the imported module
`LocalSplitGeneratorRelations`. A pair `(g, h)` of points over a test object `Z` is
right-good if, after every pullback to a local test ring with separably closed
residue field, it carries relations `Ω(x) · g = Ω(y)` to `Ω'(x) · h = Ω'(y)`. The
imported module proves closure under products (`RightGood.mul`, which needs `H`
affine, `Ω` an open immersion and the factorization property `HasCellFactors Ω`) and
under inverses (`RightGood.inv`).

**Conjugates and Weyl points.** `RightGood.conj` combines these two closure lemmas:
if `(g₁, h₁)` and `(g₂, h₂)` are right-good, so is `(g₁ g₂ g₁⁻¹, h₁ h₂ h₁⁻¹)`.
The imported lemma `constantPoint_weylPoint` writes the pullback of a Weyl point to
`Z` as `u_{-a}(-1) · u_a(1) · u_{-a}(-1)`. So if the pairs `(u_a(1), u'_a(1))` and
`(u_{-a}(-1), u'_{-a}(-1))` are right-good on every `Z`, then so are the pulled-back
Weyl points (`rightGood_constantPoint_weylPoint`).

**Words.** `rightGood_rootPoint_wordConj` is an induction on the word. The
parametrization `wordConj P u (j :: l) w` is `wordConj P u l w` followed by the inner
automorphism of `N_j = rootWeylPoint P u j`. By `rootPoint_comp` and
`GroupScheme.comp_innerIso_hom`, its value at `c` on `Z` is the conjugate
`N_j · (wordConj P u l w)(c) · N_j⁻¹`, with `N_j` pulled back to `Z`. Do the same in `H`.
Conjugation preserves right-goodness, and `N_j` and its partner form a right-good
pair. So the step follows from the induction hypothesis.

**Weyl families.** Every letter of a chosen word and its starting root are simple.
So `rightGood_rootPoint_weylFamily` follows from the two previous steps: the pairs of
values of `weylFamily P W u α` and `weylFamily P W u' α` at every `c` are right-good,
if the simple-root points at all arguments and the points `u_{-a}(-1)` are
right-good.

**Root relations.** The two hypotheses say exactly that these generator pairs are
right-good (`rightGood_simpleRootPoint`, `rightGood_negSimpleRootPoint`). These two
proofs rewrite pulled-back points with `comp_rootPoint`; pullback of global
functions preserves `-1`. Evaluating right-goodness of the Weyl-family point over
`Spec A` along the identity gives `rootRelations_weylFamily`.

**Gluing.** Assume the simple data hypotheses. The imported
`isRootParametrization_weylFamily` makes every `weylFamily P W u α` a root
parametrization of `i` for `P.root α`. Its equivariance field is the torus
equivariance required by the imported `exists_iso_of_rootRelations`, with common
exponent characters `ch α = P.root α` for `G` and `H`. Reductivity makes `H` affine
over the affine scheme `Spec R`, so the total space of `H` is affine
(`isAffine_of_isAffineHom`). `HasCellFactors Ω` is the imported
`hasCellFactors_cellMap`. `exists_iso_of_rootRelations` then gives the isomorphism;
this is `exists_iso_of_simpleRootRelations`. For the proposition, the open-immersion
hypotheses come from the imported `LocalSplitBigCell.isOpenImmersion_cellMap`. It
applies to the Weyl families because their members are root parametrizations for
all roots and `i`, `i'` are fibrewise maximal with fibrewise root datum `P`.

## Provenance and scope

This is an internal derived criterion for the Isomorphism Theorem over an arbitrary
local ring. Its reduction to generators attached to simple roots follows the
strategy of the proofs of the Isomorphism Theorem: a homomorphism is determined by
simple-root data, and every root group is a Weyl conjugate of a simple one
(B. Conrad, *Reductive group schemes*, §6.2; SGA 3, Exp. XXIII). The argument above is
an explicit construction of this module, not a transcription of a published proof.

The criterion does not construct Weyl-normalized simple-root data. It does not verify
the simple-root relations or the negative simple relations for any pair of groups.
The first kind needs commutator relations between positive root groups. The second
needs rank-one relations, including the Bruhat decomposition of `u_{-a}(-1)`. The
criterion also does not prove the local split Isomorphism Theorem.
