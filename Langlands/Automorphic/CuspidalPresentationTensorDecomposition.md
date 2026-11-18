# Tensor decomposition for a supplied cuspidal spectral presentation

This internal unit connects the exact finite spectral presentation supplied in
the Rankin–Selberg task to the full carrier and all actual infinite source
models. Its provenance is the Library's local admissible Schur theorem, actual
finite-factor evaluation and actual infinite-place density models, together with
the included restricted-tensor and finite-family tensor helper results. It is
an algebraic ingredient toward Cogdell's factorization argument, not a claim
that the global Whittaker factorization is already proved.

The entry proposition is
`Langlands.Automorphic.CuspidalSpectralPresentation.PresentationPlaceTensorStatement`.
The theorem `presentationPlaceTensor` proves it. Fix a number field `F`,
compactness of its additive adelic quotient, a rank `r + 1`, an actual cuspidal
operator realization `T`, and the supplied
`P : CuspidalSpectralPresentation.{u, uQ} T`. Assume every actual embedded
`P.localComponent v` is irreducible and admissible. These are precisely the
local conditions on the spectral presentation used by the parent task; no
finite-slice irreducibility or admissibility is added as a premise.

The supplied finite slice is irreducible and admissible. There is also a
complex linear equivalence

`e : (RestrictedTensor.Space ℂ (fun v => P.localFactor v)`
`       P.tensorExceptional P.reference)`
`      ⊗[ℂ] (⨂[ℂ] i, T.placeDensityModels.subspace i) ≃ₗ[ℂ] T.Space`.

Thus the finite factor of this equivalence is the exact restricted tensor of
`P`, with its specified reference vectors and exceptional set. It is not a
replacement presentation chosen in another universe. Both field universe `u`
and supplied local-carrier universe `uQ` remain free; rank `r = 0` is included.

`IsPlaceTensorEquivalence` records three genuine covariance properties. A finite
adelic element acts on the first tensor factor by
`P.finiteTensorRepresentation`, and its image transforms by
`T.realization.finiteRepresentation`. Changing a single infinite source
component by its compact representation transforms the image by the actual
place compact action. The corresponding identity holds for the actual Lie
actions. The latter two identities use tuples which agree away from the
chosen index, as in the finite-family construction. They do not assert
covariance for arbitrary infinite group elements.

The implementation first establishes the finite-slice comparison.

1. The published local-component equivalences transport the supplied
   irreducibility and admissibility assumptions to `(P.localFactor v)`.
   `admissibleSchur_scalarEndomorphism` gives scalar self-intertwiners on each
   factor. The proved restricted-tensor irreducibility theorem therefore
   applies to the actual restricted product action. Pulling it back along
   `restrictedProductEquiv` and then transporting through
   `P.presentation.equiv` proves `finiteSlice_isIrreducible`.
2. `fullFiniteSliceInclusion` composes the supplied slice inclusion with the
   inverse finite-image equivalence. This is an injective finite intertwiner
   into the actual full carrier.
3. Write the full finite representation as the actual chosen irreducible
   finite factor tensored with its full multiplicity space, using
   `finiteMultiplicityEvaluation_finite`. Composing the supplied slice's
   inclusion with the inverse tensor equivalence gives a nonzero intertwiner
   into this tensor representation. Some basis coefficient in the trivial
   multiplicity factor detects its nonzero value; the published
   `TensorMultiplicity.coefficient` is equivariant. Hence there is a nonzero
   intertwiner from the supplied irreducible slice to the chosen irreducible
   finite factor. Irreducibility on both sides makes it bijective.
4. This proves `nonempty_finiteSliceEquiv`. The choice `finiteSliceEquiv`
   retains the resulting finite representation equivalence. Its inverse
   transports admissibility of the actual finite factor back to the supplied
   slice, proving `finiteSlice_isAdmissible`.
5. Compose `P.presentation.equiv` with this finite equivalence to obtain
   `finiteTensorEquiv`. Tensor it with the identity on all infinite source
   factors and compose with `T.allPlaceTensorEquiv`. This defines
   `P.allPlaceTensorEquiv`. Finite covariance follows by the finite
   intertwining identity and actual finite evaluation. Compact and Lie
   covariance follow by the corresponding proved actual-model tensor
   identities.

The supporting vector lemmas retain the prescribed finite data.
`finitePure S hPS a` inserts arbitrary vectors `a v` of the supplied factors
at `v ∈ S`, whenever `P.exceptional ⊆ S`. The supplied tensor exceptional set
is also contained in `S` by `P.unramified.exceptional_subset`. Every component
outside `S` remains the exact reference vector of `P`.

`finitePure_ne_zero` proves that this finite tensor is nonzero if every
prescribed component is nonzero: the finite pure tensor is nonzero, and its
stage map into the actual direct limit is injective because the references
outside the exceptional set are nonzero. `finitePure_fixed` proves that
integral subgroup elements at a place outside `S` fix it. The actual local
projection at each place of `S` is then the identity, while the action formula
is valid on that same finite stage.

`allPlaceTensorEquiv_pure_ne_zero` proves that any nonzero finite tensor and
any tuple of nonzero infinite source vectors have nonzero global image. The
finite equivalence preserves nonzeroness, and the earlier actual-model
nonzero-pure-tensor result applies. Finally
`allPlaceTensorEquiv_finitePure_sphericalOutside` transports the finite fixed
vector identity through the full equivalence. Its conclusion is the exact
published `RankinSelbergGlobal.IsSphericalOutside` predicate.

The argument uses no equality between the resulting global vector and the
original slice's particular embedded vector. It preserves the finite
representation and its supplied tensor coordinates through an actual
intertwining equivalence, which is what the prescribed-vector construction
asserts. It does not choose local test data on the embedded local components
or compare the global Whittaker functional with their local functionals.

Three earlier pending helper pairs are included unchanged for coordinated
integration: `FiniteFamilyGKTensor`, `CuspidalPlaceTensorDecomposition`, and
`RestrictedTensor/Irreducibility`. Their independent review and publication
are separate from this candidate's review. The global Whittaker functional's
ordinary and dual product formulas with one scalar, the smooth comparison for
all infinite group elements, and archimedean integral nonvanishing remain
open. This unit does not complete `ArchimedeanFactorizationStatement`.
