# Proof: characterizations of groups of multiplicative type over a field

`Langlands.GroupScheme.multiplicativeTypeCharacterization` proves exactly
`Langlands.GroupScheme.MultiplicativeTypeCharacterizationStatement.{u}`, imported unchanged
from `Langlands.GroupScheme.Torus.MultiplicativeTypeCharacterizationStatement`, for every
universe `u`. For every field `k : Type u`, every group scheme `G` over `Spec k` with
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`, and every `Ks : Type u` with
`[Field Ks] [Algebra k Ks] [IsSepClosure k Ks]`, the four conditions of the statement are
equivalent (`List.TFAE`):

- (a) `IsMultiplicativeType G`;
- (b) `IsCommMonObj G.X` and `Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)`;
- (c) `IsCommMonObj G.X`, and every `c : AffineCoordinates.hopfAlgebra G` lies in a
  subcoalgebra `D` with `FiniteDimensional k D`, `Coalgebra.IsCocomm k D` and
  `Algebra.Etale k (WithConv (D →ₗ[k] k))`;
- (d) the base change of `G` along `Spec.map (CommRingCat.ofHom (algebraMap k Ks))` is
  isomorphic to `(Diagonalizable.groupScheme (CommRingCat.of Ks) Λ).toGrp` for some
  finitely generated `Λ : Type u`.

There are no hypotheses beyond the statement's. No perfectness, characteristic,
smoothness or connectedness assumption is added; finite non-smooth groups such as `μ_p`
in characteristic `p` are included. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Files

The proof consists of four modules. Only the entry module is described in detail here;
each helper module has its own paired Markdown.

- `Langlands/RingTheory/Coalgebra/PrimitiveGroupLike.lean` (namespace
  `Langlands.CoetaleHopf`): primitive elements in group-like spans vanish; skew-primitive
  elements vanish in Hopf algebras without primitive elements; primitive-freeness passes
  to scalar extensions; over an algebraically closed field, a finite-dimensional
  cocommutative coalgebra without nonzero elements `b` with `Δ b = a ⊗ b + b ⊗ a`
  (`a` group-like) is spanned by group-like elements.
- `Langlands/RingTheory/Coalgebra/CoetaleHopf.lean` (namespace `Langlands.CoetaleHopf`):
  coalgebra forms of (b) ⇒ (c) and (c) ⇒ (d), cocommutativity of subcoalgebras, and
  primitive-freeness of a bialgebra whose scalar extension is spanned by group-likes.
- `Langlands/GroupScheme/Torus/MultiplicativeTypeAdditiveHom.lean` (namespace
  `Langlands.GroupScheme.MultiplicativeTypeCharacterization`): `Hom(G, 𝔾ₐ)` is trivial
  if and only if `AffineCoordinates.hopfAlgebra G` has no nonzero primitive element.
- `Langlands/GroupScheme/Torus/MultiplicativeTypeCharacterizationProof.lean` (this file).

## Helper declarations in this file

In namespace `Langlands.GroupScheme.MultiplicativeTypeCharacterization`:

- `isCommMonObj_of_iso`: if `G ≅ H` as group schemes over any base and `H` is
  commutative, so is `G`. The proof compares points through the Library's
  `isoPointsEquiv` and uses Mathlib's `isCommMonObj_iff_isMulCommutative`.
- `isCommMonObj_of_diagonalizable`: if, for some field `K` over `k`, the base change of
  `G` is isomorphic to `(Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp`, then `G`
  is commutative. The diagonalizable group is commutative, the previous lemma transports
  this to the base change, and the Library's `isCommMonObj_of_baseChange` together with
  `fieldExtension_fpqc k K` (the base change along a field extension is surjective, flat
  and quasi-compact) descends it to `G`.
- `span_of_diagonalizable`: the same hypothesis gives that the group-like elements span
  `K ⊗[k] AffineCoordinates.hopfAlgebra G` over `K`. The argument is the one used in the
  published `MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`: the Library's
  `SplittingAssembly.scalarExtensionCoordinatesIso`, the given isomorphism and
  `Diagonalizable.hopfSpecIso` identify the Hopf spectra of `K ⊗[k] A` and `K[Λ]`, and
  `SplittingAssembly.span_of_hopfSpecIso` transports Mathlib's
  `AddMonoidAlgebra.span_isGroupLikeElem`.
- `diagonalizable_of_span`: if `G` is affine of finite type and the group-like elements
  span `K ⊗[k] A` (`A = AffineCoordinates.hopfAlgebra G`), then condition (d) holds over
  `K`, with `Λ = Additive (GroupLike K (K ⊗[k] A))`. The Library's
  `Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` gives a bialgebra equivalence
  `K ⊗[k] A ≃ K[GroupLike]`, and Mathlib's `MonoidAlgebra.toAdditiveBialgEquiv` rewrites it
  additively. `CommHopfAlgCat.isoMk` turns it into an isomorphism of Hopf algebras, and the
  group-scheme isomorphism is
  `scalarExtensionCoordinatesIso⁻¹ ≫ (hopfSpec.mapIso _)⁻¹ ≫ Diagonalizable.hopfSpecIso`.
  Finite generation: `A` is a finitely generated `k`-algebra by the Library's
  `AffineCoordinates.algebraFiniteType` (from `LocallyOfFiniteType`), so `K ⊗[k] A` is
  finitely generated over `K` (Mathlib's base-change instance), hence so is
  `AddMonoidAlgebra K Λ` (`Algebra.FiniteType.equiv`), and Mathlib's
  `AddMonoidAlgebra.finiteType_iff_group_fg` gives `AddGroup.FG Λ`.

## Main theorem

After introducing the variables, the proof records `IsAffine G.X.left`
(`isAffine_of_isAffineHom`, the same instance the statement's `haveI` supplies),
`IsSepClosed Ks` and `Algebra.IsAlgebraic k Ks` (from `IsSepClosure`), and proves the
implications `1 → 4`, `4 → 1`, `4 → 2`, `2 → 3`, `3 → 4`, which `tfae_finish` combines.

- (a) ⇒ (d): the published `MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic`
  shows the base change of `G` to the algebraic extension `Ks` is of multiplicative type,
  and the published `MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`
  (whose predicate `IsFGDiagonalizable` is exactly the form of (d)) makes it diagonalizable
  with finitely generated `Λ` over the separably closed field `Ks`.
- (d) ⇒ (a): take the field `K = Ks` in the definition of `IsMultiplicativeType`.
- (d) ⇒ (b): commutativity is `isCommMonObj_of_diagonalizable`. Group-like spanning of
  `Ks ⊗[k] A` (`span_of_diagonalizable`) and
  `CoetaleHopf.eq_zero_of_isPrimitiveElem_of_span_baseChange` show `A` has no nonzero
  primitive element, and `subsingleton_of_noPrimitive` gives
  `Subsingleton (G ⟶ 𝔾ₐ)`.
- (b) ⇒ (c): commutativity is kept. Since `G` is commutative, `A` is cocommutative (the
  Library's `AffineCoordinates.hopfAlgebra_isCocomm`). Given `c`, the Library's
  `Subcoalgebra.localFiniteness` provides a finite-dimensional subcoalgebra `D ∋ c`; it is
  cocommutative by `CoetaleHopf.isCocomm_subcoalgebra`. The subsingleton hypothesis gives
  primitive-freeness of `A` (`eq_zero_of_isPrimitiveElem_of_subsingleton`), and
  `CoetaleHopf.etale_of_noPrimitive` gives `Algebra.Etale k (WithConv (D →ₗ[k] k))`, with
  the convolution ring structure coming from the cocommutativity just proved, as in the
  statement's existential.
- (c) ⇒ (d): `CoetaleHopf.span_baseChange_of_coetale`, applied to the hypothesis of (c)
  verbatim, shows that the group-like elements span `Ks ⊗[k] A`, and
  `diagonalizable_of_span` gives (d). The commutativity part of (c) is not needed here.

## Relation to the source

Milne, *Algebraic Groups* (2017), Theorem 12.18 and its proof (printed pp. 237–238;
registered source `milne-2017-algebraic-groups`), proves (a) ⇒ (b) ⇒ (c) ⇒ (d) ⇒ (a). The
Lean proof uses the cycle (d) ⇒ (b) ⇒ (c) ⇒ (d) together with (a) ⇔ (d), which the
published finite-Galois splitting helpers already provide. The individual steps follow the
route in the statement's Markdown section "For the later proof":

- for (d) ⇒ (b), primitive elements of `A` stay primitive in `Ks ⊗ A ≅ Ks[Λ]`, which has
  none (Milne instead argues with Theorem 12.12);
- for (b) ⇒ (c), the passage to an algebraic closure and the elements `a, b` with
  `Δ a = a ⊗ a`, `Δ b = a ⊗ b + b ⊗ a`, `S(a) b` primitive. Milne's surjection onto the
  dual numbers is replaced by an equivalent derivation at a maximal ideal of the dual, and
  his reduction to local factors by idempotent maximal ideals (see the paired Markdown of
  `PrimitiveGroupLike`). Étaleness is descended to `k` through formal unramifiedness;
- for (c) ⇒ (d), group-like spanning over `Ks` and the reconstruction of the group from
  the group algebra of its group-like elements.

The implemented proof differs in route but not in scope from the source; Milne's
standing conventions (affine group schemes of finite type over a field) are exactly the
statement's hypotheses.
