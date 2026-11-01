# Irreducible quotients of derivatives of supercuspidal products

Author: Worker 818.

This internal helper pair belongs to task
`f81d9b36-2615-4fec-abc2-50ef93d880bf`, the proof of
`Langlands.Classification.HighestDerivativeSupportShift`. It proves the
*unshifted* support statement used in that proof. It does not prove the
target: it contains no `ν`-shift and no highest-derivative pairing.

All declarations are in the namespace
`Langlands.Classification.CuspidalProductDerivativeQuotientSupport`. The pair
introduces no proposition definitions, no axioms and no theorem-valued
premises. Each result is proved from published inputs only.

## Main result

`derivative_quotient_support` is a quotient form of BZ77 Lemma
4.7(a). Fix the supplied topology `T.topology`, a character
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F` (formed with `T.topology`)
and natural numbers `0 < k < n`. This structure bundles continuity and the
nontriviality field `nontrivial : toAddChar ≠ 1`. So `ψ` ranges over every
continuous nontrivial unitary additive character, and never the trivial one.
Let `ρ : Fin r → CuspidalDatum T` be cuspidal data with rank sum `n`, and let
`A i` be supercuspidal
representations of `GL_(rank ρ i)` in carrier universe `uV` with
`(ρ i).IsRepresentedBy (A i)`. Let `τ` be an irreducible smooth representation
of `GL_(n-k)` in carrier universe `max uF uV`. Suppose there is a nonzero linear
map `χ` from the carrier of
`(Derivative.generalLinearDerivative T ψ n k hk).obj (T.cuspidalProductInduced ρ h A)`
to `τ` that intertwines the two `GL_(n-k)` actions. Then there are `l` and
`ρ'' : Fin l → CuspidalDatum T` such that

- `T.IsCuspidalConstituent ρ'' τ`, so `List.ofFn ρ''` is an actual supercuspidal
  support of `τ` in the sense of `IsSupercuspidalSupport`; and
- `(List.ofFn ρ'' : Multiset _) ≤ List.ofFn ρ`, as multisets, so
  multiplicities are respected.

The derivative is the actual published `generalLinearDerivative` with its
determinant inverse-half normalization. No equivariance beyond the action of
`GL_(n-k)` is assumed. The map `χ` need not be surjective; surjectivity
follows from irreducibility inside the proof.

The intermediate result `jacquet_quotient_support` is the same
statement for the normalized `(a, b)` Jacquet module, `0 < a`, `0 < b`. There
the map is only assumed equivariant for the first block, embedded through
`(Shahidi.twoBlockLeviEquiv ha hb).symm (g, 1)`.

## Proof

The derivative step reduces the claim to Jacquet modules. Write `n = a + k`
with `0 < a`. The published Ze80 3.7(b) comparison
`Derivative.partialDerivativeJacquetComparison` identifies the rank-cast
order-`k` derivative with the partial derivative of the positive two-block
normalized Jacquet module for `(a, k)`. `exists_rankCast_map` and
`exists_map_of_equiv` move `χ` across the rank cast and this isomorphism.
Composing with the surjective `Derivative.partialDerivativeMk` gives a
nonzero linear map out of the `(a, k)` Jacquet module of the product. It is
equivariant for the first block, by `Derivative.partialDerivative_action_mk`.
`jacquet_quotient_support` then applies, and `isCuspidalConstituent_of_rankCast`
removes the rank cast from the conclusion.

`jacquet_quotient_support` uses the published geometric lemma
`Geometric.padicGeometricLemma` for the source shape `T.cuspidalShape ρ h`
and the target shape `(a, b)`. It glues the Jacquet functor from geometric
pieces, up to a permutation of the graded steps.

1. **Filtration**. `exists_graded_map` takes the first
   filtration step on which the map is nonzero. The map then factors through
   that successive quotient, still nonzero and equivariant.
   `exists_map_of_iso` moves it to the identified geometric piece.
2. **Vanishing of proper pieces.** By the published `glCuspidalTensor`, the
   external tensor product of the `A i` is cuspidal on the source Levi.
   `geometricPieceFunctor_subsingleton_of_proper_source` makes every piece
   with a proper source parabolic zero, so such a piece carries no nonzero
   map. Only pieces whose source refinement is the whole source Levi remain.
3. **Geometry**. For such a piece the permutation conjugates
   the whole source Levi onto the flattened target refinement `(a,b).flatten R`:
   `conjugatesLevi_flatten_of_source_top`, derived from
   `conjugatesLevi_flatten_of_target_top` and `conjugatesLevi_inv`.
4. **Transport.** Cuspidality survives transport along any permutation that
   conjugates the whole Levis, using the published
   `Langlands.CuspidalSupport.isLeviCuspidal_transport_of_conjugatesLevi`.
   The two transport lemmas originally in `Exponents.PersistenceTransport`
   now live in the shared
   [`CuspidalSupport.WholeLeviTransport`](../CuspidalSupport/WholeLeviTransport.md)
   module with their original statements and proofs. This helper imports that
   module and reuses the existing declarations. Its import closure still
   excludes exponent persistence and `MaximalConeLifting`.
5. **Piece**. `fullSourcePieceEquiv` identifies a
   full-source piece with the normalized refined induction, along `R`, of
   the transported source representation. It is read through
   `flattenedLeviEquiv`. The proof composes the published full refined
   Jacquet equivalence, the subgroup equality equivalences and the
   intersection transport (`intersectionTransportEquivTo`). It ends with
   `normalizedRefinedInducedCongr`, which builds the induced equivalence from
   the published `normalizedRefinedInducedMap` in both directions.
6. **Factors**. The transported representation is irreducible
   (`isIrreducible_transport`) and cuspidal, so the published
   `padicLeviCuspidalFactorization` writes it as a block tensor of
   supercuspidal representations `X` of the flattened blocks.
   `exists_inner_factors` regroups these along the two coarse blocks with
   `FiniteTensor.flattenedTensorRegroupEquiv`. This gives the inducing
   representation of the published `Parabolic.refinedInductionTensor`, with
   inner factors `innerFactor` obtained by casting ranks (`castSupercuspidal`).
7. **First block**. `Parabolic.refinedInductionTensor`
   identifies the piece with the external tensor product of the normalized
   parabolic inductions of the two inner products. The map is equivariant for
   the first block only. `exists_factor_map` evaluates on a pure tensor that
   the map does not kill and gives a nonzero equivariant map out of the first
   factor. By irreducibility of `τ` it is surjective
   (`isQuotient_of_ne_zero`). `full_piece_quotient` assembles these steps.
8. **Support**. `isSubquotient_cuspidalProductInduced` reads
   that quotient as a subquotient of `T.cuspidalProductInduced` of the inner
   data `ρ''` of the first block. So `T.IsCuspidalConstituent ρ'' τ`. The
   published association `glCuspidalTensorAssociation` (forward direction)
   identifies `List.ofFn ρ` with the multiset of the flattened data `ρ'`.
   `ρ''` is `ρ'` restricted along the injective map `j ↦
   flattenBlockEquiv R ⟨0, j⟩` (`cuspidalDatum_castSupercuspidal`), so
   `ofFn_comp_le` gives the multiset inequality. `full_piece_support`
   assembles this step.

## Normalization, topology and universes

Only the supplied `T.topology` is used, and the field-derived instances
`T.valuativeRel` and `T.localField` when a topological-ring instance is
needed. The derivative is the published `generalLinearDerivative` with its
determinant inverse-half normalization. Its normalization enters only through
the published Ze80 3.7(b) comparison, which is proved for these actual
functors and the normalized Jacquet functor. No Haar-modulus comparison is used.
Field universe `uF`; supercuspidal factors have carrier universe `uV`; the
cuspidal product, its derivative and `τ` have carrier universe `max uF uV`, as
in the target. The additive character `ψ` is any element of
`HarmonicAnalysis.UnitaryAdditiveCharacter F`, that is, any continuous
nontrivial unitary additive character, as in BZ77 §3.1 (printed p.450) and Ze80
§3.7 (printed p.182), which uses the character of BZ77 §3. The theorem adds
no hypothesis on `ψ` beyond the bundled continuity and nontriviality fields.
The proof never uses the field `ψ.nontrivial` directly, but the theorem does
not apply to the trivial character, because the trivial character is not of
this type.

`fullSourcePieceEquiv` needs `set_option maxHeartbeats 1200000`, a finite
limit. Every other declaration compiles at the default limit.

## Original sources and internal provenance

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`; printed
page = zero-based PDF index + 440. Lemma 4.7(a), printed p.455 (one-based PDF
page 16), states that every irreducible subquotient of a derivative of
`ρ_1 × … × ρ_r`, with `ρ_i` cuspidal, has support in `(ρ_1, …, ρ_r)`. Its proof
is the first sentence of §4.8, printed p.455, and cites 4.4 and the Leibniz
rule 4.6. The proof of part (b), §4.8(b), printed pp.455–456, uses (a) only for
an irreducible quotient of a derivative, obtained from the pairing of
Proposition 3.8 (printed p.453). This pair proves that quotient form, with
multiplicities.

The Lean route differs from BZ77 §4.8(a). It does not use the Leibniz rule
4.5–4.6, which is not published. Instead it combines:

- Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
  literature ID `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  Proposition 3.7(b), printed p.182: the derivative is a partial derivative of
  a Jacquet module;
- the geometric lemma, BZ77 §§2.11–2.12, printed p.448, specialized to block
  Levis of `GL_n` as in the published proof;
- vanishing of proper Jacquet modules of cuspidal representations, and the
  Levi factorization and association of cuspidal data, from the published
  cuspidal-support results.

The filtration, geometry, piece identification, tensor factor and multiset
steps are internal and are described above. The original pages BZ77
pp.455–456 were read for this pair. The project's source and errata pointers
list no applicable correction. This records that check; it does not claim that
no erratum exists.

## Published inputs

The module imports these published modules directly. Each used theorem has an
independently accepted and published proof, or is part of a published
`lean.definition` helper.

| Module | Publication | Mathematical use |
| --- | --- | --- |
| `Geometric.GeometricLemmaProof` | proof `f606bb75-3194-405e-ba6a-1edb4294d539`, task `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` | `padicGeometricLemma`: gluing of the Jacquet module of an induced representation from geometric pieces |
| `CuspidalSupport.JacquetVanishingHelpers` | definition `42536722-fde0-468f-b133-c8c3e83f47a3` | `geometricPieceFunctor_subsingleton_of_proper_source` |
| `CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` | proof `d5bbef23-e882-4f12-a71a-00b8f6f5d329`, task `17247e03-9471-4f13-81fa-e4f7058619a0` | `fullRefinedJacquetEquiv`, `subgroupEqualityEquiv` |
| `CuspidalSupport.MinimalConjugatingCosetsProof` | proof `ea18e1f7-2464-410e-b5e1-eadc8dd101e8`, task `d042dc77-fd25-4c92-b943-d456ffd86fe9` | `minimalConjugatingCosets`, `conjugatesLevi_inv` |
| `CuspidalSupport.MinimalWeylTransportProof` | proof `6acd6deb-33b6-49ee-b5cf-7d9873163fb5`, task `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` | `isLeviQuasicuspidal_transport` |
| `CuspidalSupport.AssociationReduction` | definition `9488dbde-91c9-497f-8f66-52032c37017c` | `transportWeylEquiv`, `transport_transport`, `isIrreducible_transport`, `isAdmissible_transport` |
| `CuspidalSupport.LeviTensorFactorizationProof` | proof `cf3ee414-c6f5-4dd2-a3cb-6d41533fcd9f`, task `334e2222-c3e9-47e3-b05c-2afe12f49e94` | `padicLeviCuspidalFactorization` |
| `CuspidalSupport.CuspidalTensorProof` | proof `8513f998-61e8-49e4-b1a5-738e4315b437`, task `cece816e-aee9-40ca-9139-d770491b6178` | `glCuspidalTensor` |
| `CuspidalSupport.CuspidalTensorAssociationProof` | proof `e209fa9f-5de2-4779-acbf-dac62583221c`, task `ee36e054-716f-492a-a0e3-e83b614d9431` | `glCuspidalTensorAssociation` |
| `Parabolic.RefinedInductionTensorProof` | proof `91b8bcdb-14ac-4f94-a40c-1ac6a18295ae`, task `fa77b238-a6a2-47ae-9847-87e6de1267de` | `refinedInductionTensor` |
| `Tensor.FlattenedGLRefinement` | definition `c8c667d5-4e53-4e1c-9f8d-cffa601c2d80` | `flattenedTensorRegroupEquiv` |
| `Geometric.FlattenedLevi` | definition `f75012c9-3ab3-47ac-af97-e6a170537087` | `flattenedLeviEquiv` and its embedding lemmas |
| `Shahidi.TwoBlocks` | definition `7b5082dd-9e5e-4d53-84b1-73ee7ba87a8d` | the shape `(a, b)` and `twoBlockLeviEquiv` |
| `Derivative.PartialDerivativeJacquetComparisonProof` | proof `998f43e6-dc22-4288-98b7-7343dd9ebc1c`, task `a4119dcc-97b6-47e4-b150-d5e97a8f226b` | `partialDerivativeJacquetComparison` (Ze80 3.7(b)) |
| `Derivative.Partial` | definition `c3edb686-84a2-4e40-9fb5-465fc3399c4e` | `partialDerivativeMk`, its surjectivity and action |
| `Classification.SupercuspidalSupport` (through the imports) | definitions `5f04f9a1-f335-43e2-a9da-bb6850b4b838`, `6ee5d0b4-3f01-47de-94f4-06d2d3de92ce` | `cuspidalProductInduced`, `IsCuspidalConstituent`, `IsQuotient.isSubquotient` |

## Independence audit

The parent task requires independence from every segment derivative formula,
every segment-socle, head or Jacquet formula, segment classification and the
two-supercuspidal product results, and from all tasks listed in its
Independence section and its additional BZ77-only restrictions.

- **Import closure.** The full import closure of this module at Library
  commit `a9fde2164dfeae002c8c27324c18bdcd395f447d` has 368 `Langlands`
  modules, including this one. It is the same module list as at the earlier
  base `6cb15022e66f7f1f171e7e8d563e74b92072e5ba`, and every published file in
  it is byte-identical at the two commits. The only `Classification` modules in it are
  `Supercuspidal`, `SupercuspidalTwist`, `SupercuspidalSupport`,
  `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
  `ConstituentRelations` and `Segments`. The last two contribute definitions
  only; nothing in this pair uses a segment. No `Exponents`,
  `SegmentEdge*`, `SegmentFullJacquet*`, `WholeLeviPieceTransport`,
  `InducedOppositeCuspidalPieceConditional`,
  `ProductLeviCuspidalJacquetAssembly` or two-supercuspidal product module is
  in the closure.
- **Publishing tasks.** 362 closure modules belong to published artifacts. The
  other five, `Group.GL.Transvection`,
  `HarmonicAnalysis.FiniteProductMeasureScaling`,
  `Representation.Compact.OrbitMeanTranslation`, `Representation.OrbitSpan`
  and `Topology.CompactNormCharacter`, are general infrastructure without
  representation-theoretic conclusions. Every task ID recorded on those
  artifacts was compared with the 33 task IDs in the parent's Independence and
  BZ77-only sections. There is no match.
- **Mathematical dependencies.** The proof uses only the inputs in the table
  above. It uses no derivative of a segment and no socle or head statement. It
  uses no Leibniz rule, exactness of derivatives, irreducibility criterion,
  classification or exhaustion theorem, and no square-integrability result.
