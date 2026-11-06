# Uniqueness of the actual common-closure reciprocity family

Worker 1237 and Worker 706 wrote this proof module. Worker 706 contributed the
injectivity section (`abelianizationMap_injective_of_compact_commutator`,
`weilGaloisProjection_denseRange`, `weilFixing_closedCommutator_isCompact`,
`weilGaloisAbelianProjection_injective`). Worker 1237 wrote the rest and the
final assembly.

## Target

`Langlands.LocalClassField.commonClosureReciprocityUniqueness` has type exactly
the published proposition `CommonClosureReciprocityUniqueness.{u}` from
`Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.lean`. The
statement module is unchanged. The theorem covers every prime `p`, every
`F : PadicField.{u} p` with unrestricted universe `u`, and every base datum
`T`. It uses the canonical extension data `CommonClosure.canonicalData F` and
the degree map `Weil.Local.localResidueDegree F`. Any two candidate families
satisfying `CommonClosure.NormalizedSystemRelation` are equal, at every finite
intermediate field of the chosen algebraic closure. This includes nonnormal
fields. The theorem has no hypotheses beyond the two relations in the target.

## What the proof uses

From each relation only two parts are used: the norm relation
(`NormRelation`, condition 1) and the normalization relation
(`NormalizationRelation`, condition 6). The transfer, conjugation, density and
completion conditions are not needed. The generic lemma
`eq_of_norm_normalization` holds for arbitrary extension data `S` and an
arbitrary degree map `φ`. Its one extra hypothesis says that every map
`E.weilGaloisAbelianProjection φ` is injective. For the actual
`localResidueDegree F`, that hypothesis is proved by
`weilGaloisAbelianProjection_injective`, so the final theorem has no
hypotheses.

## Implemented proof

Fix a finite intermediate field `E` and two families `e₁, e₂`. Write
`g_i(x) = E.weilGaloisAbelianProjection φ ((e_i E).symm x)`; this is
`CommonClosure.galoisHom` at `E`. The target group
`A = TopologicalAbelianization E.field.fixingSubgroup` is compact
(`fixingSubgroup_compact`, since fixing subgroups are closed by
`InfiniteGalois.fixingSubgroup_isClosed`). It is also Hausdorff
(`abelianizationHausdorff`) and nonarchimedean (`quotientNonarchimedean` with
`fixingSubgroup_nonarchimedean`).

1. **Abstract separation** (`eq_of_forall_openSubgroup`). Let `A` be a compact
   Hausdorff nonarchimedean commutative group and `a₁, a₂ ∈ A`. Suppose every
   open subgroup containing `a₁` contains `a₂`. Suppose also that for every
   `N ≠ 0` there is a homomorphism `δ : A → ℤ/N` with open kernel sending both
   elements to the class of one fixed integer `d ≠ 0`. Then `a₁ = a₂`. Proof:
   if not, choose an open subgroup `U` that misses `a₂ a₁⁻¹`. It has finite
   index `n` by compactness. Take `N = n·|d|` and the open subgroup
   `H = (U ∩ ker δ)·⟨a₁⟩`. Then `a₂ = v a₁^k` with `v ∈ U ∩ ker δ`. Applying
   `δ` gives `n·d ∣ (k-1)·d`, so `n ∣ k-1`. Since `a₁^n ∈ U`, this puts
   `a₂ a₁⁻¹ = v a₁^(k-1)` in `U`, a contradiction.

2. **Open subgroups are norm groups.** `exists_field_of_isOpen` takes an open
   subgroup `H` of `A`. It pulls `H` back to the fixing subgroup of `E`, pushes
   it into the absolute Galois group, where it is open and therefore closed,
   and takes its fixed field `M`. By `InfiniteGalois.fixingSubgroup_fixedField`
   and `InfiniteGalois.isOpen_iff_finite`, `M` is a finite extension containing
   `E`. An element `s` of the fixing subgroup of `E` has class in `H` exactly
   when `s` fixes `M`. `weilGaloisAbelianProjection_mem_iff` then shows that
   the Galois image of an abelianized Weil element lies in `H` exactly when the
   element lies in the range of `E.weilAbelianInclusion M h φ`. Finally,
   `symm_mem_range_iff` uses the norm relation for `E ≤ M`: `(e E).symm x` lies
   in that range exactly when `x` lies in the range of the actual
   `E.unitsNorm M h`. Hence `g_i(x) ∈ H` if and only if `x` is a norm from `M`.
   This condition does not depend on `i`, which gives the first hypothesis of
   step 1.

3. **Degrees modulo `N`.** `profiniteIntegerMod N` is the continuous reduction
   of the actual profinite completion of `ℤ` to `ℤ/N`. It is built from the
   published `degreeModHom`, `degreeModSubgroup` and `profiniteModProjection`.
   It sends the Frobenius image of `m` to `m mod N`. `galoisDegreeMod φ E N` is
   the continuous lift to `A` (via `abelianizationLift`) of `φ` restricted to
   the fixing subgroup, followed by this reduction. Its kernel is open because
   `ℤ/N` is discrete. `galoisDegreeMod_weilGaloisAbelianProjection` shows that
   on the Galois image of an abelianized Weil element `w` it gives the base
   degree `E.weilDegree φ w` modulo `N`. This uses the pullback equation
   `φ g = frobenius d`.

4. **Equal nonzero degrees.** By the normalization relation for each family,
   `|x|_E = q^(-deg((e_i E).symm x))` with `q = T.residueCardinality > 1`. So
   the two degrees are equal (`zpow_right_injective₀`). If `|x|_E ≠ 1`, the
   common degree is nonzero. Steps 1-3 then give `g₁(x) = g₂(x)`
   (`galoisHom_eq_of_normalizedAbs_ne_one`).

5. **All units.** For the chosen uniformizer `π` of `(S E)`
   (`LocalFactor.PadicAbelian.uniformizerUnit`), `|π|_E = q_E^(-1) ≠ 1`. If
   `|x|_E = 1` then `|xπ|_E ≠ 1`. Multiplicativity of `g_i` and cancellation
   then give `g₁(x) = g₂(x)` for every `x`.

6. **Injectivity and conclusion** (Worker 706's section).
   `abelianizationMap_injective_of_compact_commutator`: let `f` be an injective
   continuous homomorphism with dense range into a Hausdorff group, whose
   source has compact closed commutator subgroup. Then `f` is injective on
   topological abelianizations. Indeed, the image of the closed commutator is
   compact and so closed. By density and continuity of the commutator map it
   contains every target commutator, and hence the target's closed commutator.
   For the actual degree map, the restricted Weil projection is injective
   (`Weil.Local.localProjection_injective`). It has dense range: the range is
   the preimage of the dense range of `Weil.Local.localProjection` under the
   open inclusion of the fixing subgroup (`weilGaloisProjection_denseRange`).
   The source's closed commutator lies in the kernel of the restricted degree
   map. That kernel is compact, as a closed preimage of the compact local
   inertia `Weil.Local.localInertia_isCompact`
   (`weilFixing_closedCommutator_isCompact`). Hence
   `weilGaloisAbelianProjection_injective`. With step 5 this gives
   `(e₁ E).symm = (e₂ E).symm` pointwise, so `e₁ E = e₂ E`
   (`ContinuousMulEquiv.ext`). Function extensionality over `E` concludes
   `eq_of_norm_normalization`, and the final theorem applies it to the norm
   and normalization components of the two relations.

## Provenance and relation to the literature

The statement Markdown records the original sources: Tate, *Number theoretic
background*, Sections 1.1 and 1.4, and Serre, *Local Fields*, XI.3-5, XIII.4
and XIV.6. It also records a uniqueness route supplied by Worker 21. This Lean
proof is a derived route that differs from that one. The norm diagram still
identifies the open subgroups of the Galois abelianization with norm groups,
as in Serre XI.3-5 and XIV.6. The proof does not compare Frobenius
restrictions on unramified and totally ramified pieces. Instead, step 1
separates points using open subgroups together with degree reductions modulo
every `N`. The normalization fixes those degree reductions. The final lift
uses the direct injectivity of step 6 in place of the multiplicative
completion comparison. The abstract lemmas in steps 1 and 6 are elementary
topological-group arguments written for this module; they are not quoted from
the sources.

## Dependencies and check status

Imports: the unchanged statement module; the published
`UnramifiedExtensionDegreeProof` (reduction modulo `N` of profinite integers);
`Weil.Local.AssemblyProof` (local Weil projection injectivity, density and
compact inertia); `LocalField.Normalization.Proof` and `LocalField.Uniformizer`
(absolute-value multiplicativity, residue cardinality `> 1`, the uniformizer
unit); and Mathlib's `FieldTheory.Galois.Infinite`, `Topology.DenseEmbedding`
and `Topology.Instances.ZMod`. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The development Lake build of
the module had zero errors and warnings. The theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`, and has the single
universe parameter `u`. Independent review and publication are separate
requirements.
