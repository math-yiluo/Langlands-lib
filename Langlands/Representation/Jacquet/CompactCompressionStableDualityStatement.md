# Evaluation duality between compact compression stable images

This module states that, when the space of `K`-fixed vectors is finite
dimensional, evaluation identifies the stable image of compression by `g⁻¹` on
the actual smooth contragredient with the full algebraic dual of the stable
image of compression by `g` on the representation. It contains proposition
definitions, not proofs of those propositions.

## Data and existing constructions

Let `G : Type uG` be a topological group and `V : Type uV` a complex module.
The universes `uG` and `uV` are independent. Fix a representation
`ρ : Representation ℂ G V`, its smoothness witness `hρ : Langlands.IsSmooth ρ`,
an open subgroup `K : OpenSubgroup G`, a compactness witness
`hK : IsCompact (K : Set G)`, and an arbitrary `g : G`. Every carrier,
operator and inclusion below is an existing Library construction:

- `Ṽ = Langlands.SmoothDual ρ`, the smooth vectors of the full algebraic dual
  of `V`, with `ρ̃ = Langlands.smoothContragredient ρ` acting on it
  (`Langlands.Representation.Smooth.Contragredient.Definitions`).
- `hρ̃ = Langlands.isSmooth_smoothContragredient ρ`, the published proof that
  `ρ̃` is smooth (namespace `Langlands`, module
  `Langlands.Representation.Smooth.Contragredient.LawsProof`). It is a proof
  term used to form the carriers on the dual side, not a hypothesis.
- `⟨ℓ, v⟩ = Langlands.smoothDualPairing ρ ℓ v`, evaluation of a smooth
  functional `ℓ : Ṽ` at `v : V`.
- `C = Langlands.Jacquet.compressedAction ρ hρ K hK g`: on
  `Langlands.fixedVectors ρ K.toSubgroup`, act by `g` and then apply the
  normalized compact average over `K`
  (`Langlands.Representation.Jacquet.CanonicalLiftDefinitions`).
- `S = Langlands.Jacquet.stableImage ρ hρ K hK g = ⨅ r : ℕ, range (C ^ r)`, a
  submodule of the `K`-fixed vectors of `V`.
- `C̃ = Langlands.Jacquet.compressedAction ρ̃ hρ̃ K hK g⁻¹`, compression by the
  inverse `g⁻¹` on the `K`-fixed smooth functionals, and
  `S̃ = Langlands.Jacquet.stableImage ρ̃ hρ̃ K hK g⁻¹ = ⨅ r : ℕ, range (C̃ ^ r)`.
- `Langlands.Jacquet.stableImageToRepresentation`, the existing inclusion of a
  stable image into its representation carrier, used as
  `stableImageToRepresentation ρ̃ hρ̃ K hK g⁻¹ : S̃ →ₗ[ℂ] Ṽ` and
  `stableImageToRepresentation ρ hρ K hK g : S →ₗ[ℂ] V`.

No new data carrier, operator or equivalence is constructed.

## Declarations

Both declarations are in the namespace `Langlands.Jacquet`.

| Declaration | Proposition |
| --- | --- |
| `CompactCompressionStableEvaluationDuality ρ hρ K hK g` | There exists a complex linear equivalence `E : S̃ ≃ₗ[ℂ] Module.Dual ℂ S` such that for every `ℓ : S̃` and every `v : S`, `E ℓ v = smoothDualPairing ρ (stableImageToRepresentation ρ̃ hρ̃ K hK g⁻¹ ℓ) (stableImageToRepresentation ρ hρ K hK g v)`. |
| `CompactCompressionStableDualityStatement` | Universally quantifies over `G : Type uG`, its `Group`, `TopologicalSpace` and `IsTopologicalGroup` structures, `V : Type uV`, its `AddCommGroup` and complex `Module` structures, and all of `ρ`, `hρ`, `K`, `hK`, `g`; assumes `FiniteDimensional ℂ (Langlands.fixedVectors ρ K.toSubgroup)`; concludes `CompactCompressionStableEvaluationDuality ρ hρ K hK g`. |

The first declaration is a Prop-valued clause for fixed data, without a
finite-dimensional premise. The second is the selected main target
`Langlands.Jacquet.CompactCompressionStableDualityStatement.{uG,uV}`; it binds
all data internally.

The evaluation identity is required on every pair `ℓ, v` of stable-image
vectors and fixes `E` completely: two linear functionals on `S` agreeing at
every `v` are equal, so `E ℓ` must be the evaluation functional
`v ↦ ⟨ℓ, v⟩`. The statement therefore says precisely that the
evaluation-induced linear map from `S̃` to the full dual of `S` is bijective;
it is neither an unspecified perfect pairing nor an abstract isomorphism.
Only `S`, `S̃`, `Module.Dual ℂ S` and `Ṽ` are involved: no `K`-fixed
functional outside `S̃` and no vector outside `S` is paired.

## Scope of the hypotheses

The only premise is finite dimensionality of the `K`-fixed vectors of `V`. The
statement does not assume admissibility, finite dimensionality of `V` or of
the dual-side fixed vectors, any duality or adjointness, a Fitting splitting,
or the conclusion. There is no p-adic field, general linear group, Iwahori
factorization, parabolic subgroup, contraction or Jacquet-module hypothesis.
The element `g` is arbitrary, including `g = 1`; then `C` and `C̃` are the
identity (`compressedAction_one`), so `S` and `S̃` are all fixed vectors on
each side and the statement specializes to compact fixed-vector duality.
Zero carriers and zero fixed-vector spaces are allowed; there is no
`Nontrivial` assumption.

The operator on the smooth dual uses `g⁻¹` deliberately. For a `K`-fixed
smooth functional `ℓ` and a `K`-fixed vector `v`, the normalized average does
not change the value at `v`, so `⟨C̃ ℓ, v⟩ = ⟨ρ̃(g⁻¹) ℓ, v⟩ = ⟨ℓ, ρ(g) v⟩`;
because `ℓ` is `K`-fixed, this also equals `⟨ℓ, C v⟩`. Thus `C̃` is the
adjoint of `C` for the evaluation pairing, which is why the two stable images
are paired. Using `g` instead of `g⁻¹` on the dual side would pair `S` with
the stable image of the transpose of compression by `g⁻¹`, which is a
different statement and is not asserted here.

## Derived provenance

This is an internal, derived statement: a finite-dimensional adjoint
consequence used as a prerequisite for the published
`Langlands.Parabolic.OppositeDualityStatement`. The exact generic formulation
is not taken from a source. Its expected derivation, given for provenance
only, combines two published results, neither of which is a premise here:

1. `Langlands.smoothDualFixedRestriction_bijective`
   (`Langlands.Representation.Smooth.Contragredient.CompactDualityProof`):
   restriction identifies the `K`-fixed smooth functionals with
   `Module.Dual ℂ (fixedVectors ρ K.toSubgroup)`. By the adjointness above it
   carries `C̃` to the transpose of `C`.
2. `Langlands.Jacquet.compactCompression_stabilization`,
   `powerKernelSup_isCompl_stableImage` and `stableImageAction_bijective`
   (`Langlands.Representation.Jacquet.CompressionStabilizationProof`): when
   the fixed vectors are finite dimensional, `C` has a Fitting decomposition
   with the power-kernel supremum `T` complementary to `S`.

The stable image of the transpose of `C` is then the annihilator of `T`, and
restriction to the complement `S` identifies that annihilator with
`Module.Dual ℂ S`.

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
Section 6, pages 7–8 (registered source `casselman-2019-jacquet-module`,
SHA256 `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`).
The proof of Lemma III.6.1 moves his operator `τ_a` across the pairing of
`V` with `Ṽ` as the operator for `a⁻¹`, and the nondegeneracy argument in the
proof of Corollary III.6.3 transfers `τ_a` across the pairing in the same way.
His canonical pairing of Theorem III.6.2 is defined on the canonical
`K₀`-fixed subspaces of Section 5, page 6, on which these operators are
invertible. Casselman works with an admissible representation,
a compact open subgroup with Iwahori factorization, an element `a` of
`A_P^{--}` and an unnormalized sum over cosets; he does not state the generic
result above. The normalized operator for arbitrary `g`, the stable image as
an intersection of all power ranges, and the formulation as a linear
equivalence with the full dual are this project's.

The statement does not assert the canonical pairing on Jacquet modules, any
compatibility with Jacquet quotients or opposite unipotent radicals, any
equivariance, independence of `K` or `g`, or a chosen canonical equivalence.
Those belong to separate tasks.
