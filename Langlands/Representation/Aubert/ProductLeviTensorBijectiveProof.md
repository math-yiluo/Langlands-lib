# Bijectivity of the actual product-Levi tensor comparison

Author: Worker 981 (proof implementation and submission).

The theorem `Langlands.Aubert.productLeviTensorBijective` proves the published
proposition `Langlands.Aubert.ProductLeviTensorBijectiveStatement.{uF, uV}`
from `Langlands.Representation.Aubert.ProductLeviGrothendieck`. It applies to
every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData`, all ranks `a b` with positivity witnesses `ha` and
`hb`, and every explicitly supplied prerequisite proof
`hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb`. Its
conclusion is that the published map

`productLeviTensorMap F T ha hb hp :
  K0(GL_a) ⊗[ℤ] K0(GL_b) →ₗ[ℤ] K0((BlockShape.binary a b ha hb).Levi F.Carrier)`

is bijective. Here each `K0` is the actual finite-length exact Grothendieck
group (`GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF}`,
`BlockShape.FiniteLengthGrothendieckGroup.{uV, uF}`). These groups are
quotients by every actual short exact sequence of finite-length smooth
complex representations, including nonsplit ones, with carriers in
`Type (max uF uV)`. The universes `uF` and `uV` stay independent. The
theorem has no premise besides `hp`. The statement pair and every pair it
imports are unchanged.

Write `Φ = binaryProductLeviTensorFunctor F T ha hb`, the published functor
`T.binaryPairFamilyFunctor ha hb ⋙ FiniteTensor.externalFunctor`, and
`M = (BlockShape.binary a b ha hb).Levi F.Carrier`. The tensor-specific helper results are in
the namespace `Langlands.Aubert.ProductLeviTensorBijectiveProof`; the generic
irreducible-subquotient lemma is reused from the shared subquotient module.

## Strategy

The published theorems `GeneralLinear.irreducibleGrothendieckStatement` and
`GeneralLinear.BlockShape.irreducibleGrothendieckStatement` say that the actual
irreducible realization `realizeIrreducibles` is bijective. It is the
integer-linear map from finitely supported integer functions on genuine
isomorphism classes of irreducible smooth representations to the exact
Grothendieck group, and it sends the generator of a class to the class of the
representation. So each of the three Grothendieck groups is free on its
irreducible labels. The proof builds a bijection of labels
`Irr(GL_a) × Irr(GL_b) → Irr(M)`, `([A], [B]) ↦ [Φ(A, B)]`. It then shows that
the actual map `productLeviTensorMap` equals the resulting composite of linear
equivalences, pointwise.

## An irreducible subquotient of an irreducible representation

The existing `Langlands.CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient`,
imported from [WeylBranchPiecesSubquotient](../Exponents/WeylBranchPiecesSubquotient.md),
concerns complex representations `A` and `Y`
of a group, both irreducible. If `Y` is an actual subquotient of `A`, in the
sense of the published `WeylBranchPieces.IsSubquotient A Y` (a subrepresentation
`U` of `A` and a surjective intertwiner `q : U → Y`), then `A` and `Y` are
equivalent. The proof takes a nonzero vector `y` of `Y`, which exists because a
simple module is nontrivial. By simplicity `U` is `⊥` or `⊤`.

- If `U = ⊥`, the preimage of `y` under `q` would be `0`, contradicting `y ≠ 0`.
- If `U = ⊤`, composing `q` with the inclusion `A → ⊤` gives a surjective
  intertwiner `f : A → Y`. Mathlib's Schur lemma
  `Representation.IsIrreducible.bijective_or_eq_zero` says that `f` is either
  bijective or zero. It is nonzero because `y` is in its image, so it gives an
  actual equivalence.

## Irreducibility of external tensors (`isIrreducible_obj`)

Let `A` and `B` be irreducible smooth representations of `GL_a(F)` and `GL_b(F)`.
Then `Φ(A, B)` is irreducible. The factor family
`(T.binaryPairFamilyFunctor ha hb).obj (A, B)` has `A` at index `0` and `B` at
index `1` (by `Fin.cases`, definitionally). Each factor is:

- **irreducible**, by hypothesis;
- **admissible**, by the published `glFiniteLengthAdmissibility` (every
  finite-length smooth representation of `GL_n(F)` is admissible). It applies
  because an irreducible representation has finite length
  (`SmoothRep.hasFiniteLength_of_isIrreducible`);
- **Schur-scalar**: every self-intertwiner is a scalar, by the existence part of
  the published `admissibleSchur_scalarEndomorphism`.

The published `FiniteTensor.isIrreducible_external` then makes the external
tensor of the family irreducible. That tensor is `Φ(A, B)` by definition.

## Surjectivity of labels (`exists_iso_obj`)

Every irreducible smooth representation `σ` of `M` is isomorphic to `Φ(A, B)`
for some irreducible `A` of `GL_a(F)` and `B` of `GL_b(F)`. The steps are:

1. The published `CuspidalSupport.irreducibleLeviAdmissibility`, at rank
   `a + b` and shape `BlockShape.binary a b ha hb`, makes `σ` admissible.
2. The published `CuspidalSupport.padicLeviAdmissibleFactorization` needs the
   positive rank `0 < a + b`, which follows from `ha` by `omega`. It supplies a
   family `C i` of irreducible smooth representations of `GL_(size i)(F)`,
   indexed by `i : Fin (binary a b ha hb).length`, together with an actual
   equivalence from `σ` to their block tensor. The admissibility of the factors
   that it also provides is not used.
3. Take `A = C 0` and `B = C 1`. For the binary shape, `length = 2`,
   `size 0 = a` and `size 1 = b` hold definitionally. The family `C` is equal
   to `(T.binaryPairFamilyFunctor ha hb).obj (C 0, C 1)` by function
   extensionality over `Fin 2`: index `0` holds by `rfl`, and a successor index
   `j.succ` with `j : Fin 1` reduces to `j = 0` and then `rfl`.
4. The isomorphism is `SmoothRep.mkIso` of the equivalence, followed by
   `FiniteTensor.externalFunctor.mapIso (eqToIso hC)`.

## Injectivity of labels (`nonempty_iso_of_iso_obj`)

Let `A, A'` be irreducible for `GL_a(F)` and `B, B'` irreducible for `GL_b(F)`.
If `Φ(A, B) ≅ Φ(A', B')`, then `A ≅ A'` and `B ≅ B'`. The steps are:

1. The isomorphism gives an actual equivalence (`SmoothRep.equivOfIso`). By
   `WeylBranchPieces.IsSubquotient.of_equiv`, the external tensor of the primed
   factors is then an actual subquotient of the external tensor of the
   unprimed ones.
2. The published `FiniteTensor.isSubquotient_factor_of_external` needs only the
   irreducibility of the primed factors. At indices `0` and `1` it shows that
   `A'` is an actual subquotient of `A` and `B'` an actual subquotient of `B`.
3. The subquotient lemma above, using irreducibility of all four
   representations, gives equivalences `A ≃ A'` and `B ≃ B'`. These become
   isomorphisms by `SmoothRep.mkIso`.

## The label bijection (`pairLabel`, `pairLabel_bijective`)

`pairLabel` is the map

`IrreducibleIsoClass(GL_a) × IrreducibleIsoClass(GL_b) → IrreducibleIsoClass(M)`.

It is defined by `Quotient.liftOn₂`, with `(A, B) ↦ irreducibleIsoClass (Φ(A, B))`
and irreducibility from `isIrreducible_obj`. It is well defined because
isomorphisms `A ≅ A'` and `B ≅ B'` give `Φ.mapIso (Iso.prod e f)`.
`pairLabel_mk` records its value on actual representatives, by `rfl`.

`pairLabel_bijective` proves both halves:

- **Injectivity.** By induction on the four labels, equal labels give
  `Φ(A, B) ≅ Φ(A', B')` (`irreducibleIsoClass_eq_iff`). `nonempty_iso_of_iso_obj`
  then gives equal factor labels.
- **Surjectivity.** By induction on a Levi label `[σ]`, `exists_iso_obj` gives a
  preimage `([A], [B])`.

## Comparison with the actual map (`productLeviTensorBijective`)

The main proof defines the following linear equivalences:

- `eA`, `eB`, `eL` are `LinearEquiv.ofBijective` of the actual irreducible
  realizations for `GL_a`, `GL_b` and `M`. Bijectivity comes from the published
  `GeneralLinear.irreducibleGrothendieckStatement` (twice) and
  `GeneralLinear.BlockShape.irreducibleGrothendieckStatement`;
- `μ = Equiv.ofBijective pairLabel pairLabel_bijective`;
- `C = TensorProduct.congr eA eB`, from the tensor product of the two
  irreducible lattices to the source of `productLeviTensorMap`;
- `N = finsuppTensorFinsupp' ℤ _ _ ≫ Finsupp.domLCongr μ ≫ eL`, from the same
  tensor product to the Levi Grothendieck group. Mathlib's
  `finsuppTensorFinsupp'` identifies the tensor product of two free lattices
  with the free lattice on pairs.

**Generators.** Fix labels `c = [A]` and `d = [B]`, obtained by induction on the
quotients. The proof shows that `productLeviTensorMap (C (single c 1 ⊗ single d 1))`
and `N (single c 1 ⊗ single d 1)` agree:

- **Left side.** `realizeIrreducibles_generator_irreducibleIsoClass` gives
  `eA (single c 1) = [A]` and `eB (single d 1) = [B]` as actual exact classes.
  The published `productLeviTensorMap_classes` gives
  `productLeviTensorMap ([A] ⊗ [B]) = [Φ(A, B)]`, the actual external tensor
  class. Its finite-length witness is `hp.1 _ _ hfA hfB`.
- **Right side.** `finsuppTensorFinsupp'_single_tmul_single` and
  `Finsupp.domLCongr_single` reduce `N` on this element to
  `eL (single (pairLabel (c, d)) 1)`. By `pairLabel_mk` and the same
  realization formula for `M`, this is the class of `Φ(A, B)`, with the same
  finite-length witness.

**All elements.** `TensorProduct.inductionOn` and `Finsupp.induction_linear` on
both factors reduce an arbitrary element to sums of elementary tensors
`single c m ⊗ single d n`. This element equals `(m • single c 1) ⊗ (n • single d 1)`
(`Finsupp.smul_single_one`), which is `(m * n) • (single c 1 ⊗ single d 1)`
(`TensorProduct.smul_tmul_smul`). Additivity and `map_zsmul` of the three maps
then reduce everything to the generator case. The comparison is stated pointwise
rather than as an equality of composed linear maps. This avoids a mismatch
between the two `Module ℤ` structures on the tensor product (the canonical
`AddCommGroup.toIntModule` and `TensorProduct.instModule`). The result is that
`productLeviTensorMap (C x) = N x` for every `x`.

**Conclusion.** Applying this to `C.symm x` gives the function equality
`⇑(productLeviTensorMap F T ha hb hp) = ⇑N ∘ ⇑C.symm`. A composite of two linear
equivalences is bijective, so both injectivity and surjectivity of the actual
map follow together.

## Use of `hp`, rank and universe transports

- `hp` is used only through `productLeviTensorMap_classes`, which holds for the
  given proof, and through its first component, which serves as the
  finite-length witness of `Φ(A, B)`. Witnesses are compared by proof
  irrelevance. So the theorem holds for the supplied `hp`, not for a chosen
  proof. The short-exactness components of `hp` enter only through the
  published definition of `productLeviTensorMap`.
- **Ranks.** The GL ranks of the two factors are definitionally the block sizes
  `(binary a b ha hb).size 0 = a` and `size 1 = b`, with `length = 2`. Indices
  are the literals `(0 : Fin 2)` and `(1 : Fin 2)`. The Levi results are
  applied at rank `a + b`, with positivity from `ha`.
- **Universes.** All carriers lie in `Type (max uF uV)`, the saturated carrier
  universe of the published Grothendieck groups. The published results are
  instantiated there: `glFiniteLengthAdmissibility.{uF, max uF uV}`,
  `CuspidalSupport.irreducibleLeviAdmissibility.{uF, max uF uV}` and
  `CuspidalSupport.padicLeviAdmissibleFactorization.{uF, max uF uV}`. The
  Grothendieck basis theorems are used as `irreducibleGrothendieckStatement.{uV, uF}`,
  which unfolds to the generic theorem at `.{0, uF, max uF uV}`. The factors
  produced by the factorization theorem therefore lie in the same carrier
  universe as `σ`, and no universe lifting is needed.

## Representation-theoretic dependencies

The proof directly uses these published results:

- `SmoothRep.irreducibleGrothendieckStatement`, through the GL and product-Levi
  specializations, and `realizeIrreducibles_generator_irreducibleIsoClass`;
- `glFiniteLengthAdmissibility` (Smooth.Admissibility.FiniteLengthProof);
- `admissibleSchur_scalarEndomorphism` (Smooth.Schur.Proof);
- `FiniteTensor.isIrreducible_external` (Tensor.FiniteProperties) and
  `FiniteTensor.isSubquotient_factor_of_external` (Tensor.ExternalSubquotient);
- `CuspidalSupport.irreducibleLeviAdmissibility` and
  `CuspidalSupport.padicLeviAdmissibleFactorization`;
- `productLeviTensorMap_classes`, `WeylBranchPieces.IsSubquotient.of_equiv`,
  `SmoothRep.mkIso` and `SmoothRep.equivOfIso`.

A private declaration-level audit computed the transitive constant closure of
`Langlands.Aubert.productLeviTensorBijective`: 58,400 constants. Its Langlands
part includes:

- the cuspidal-support development: `CuspidalSupport.cuspidalEmbedding`,
  quasicuspidal and refined quasicuspidal embeddings, minimal Jacquet modules,
  Levi admissibility and the Levi factorization;
- parabolic induction, Jacquet modules, compact-group averaging, Hecke test
  functions, the countable-dimension Schur lemma, filtrations and multiplicity
  theory.

Exactly one constant comes from a module under `Representation.Classification`:
the group-theoretic lemma
`GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` in
`Classification.SupercuspidalTwist`. No classification theorem about
representations is in the closure. The audit shows which constants actually
occur. It does not claim that classification-free proofs exist for the
published results used.

## Development validation

`lean_check` of the module, with declaration inspection, reported no errors or
warnings, kind `theorem`, level parameters `[uF, uV]` and axioms `propext`,
`Classical.choice` and `Quot.sound`. The proof uses no `sorry` and adds no
axioms.
