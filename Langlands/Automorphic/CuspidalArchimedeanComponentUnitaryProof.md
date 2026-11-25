# Proof that archimedean standard-module components are unitarizable

Module `Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof` proves

```lean
theorem Langlands.Automorphic.cuspidalArchimedeanStandardUnitarizable :
    CuspidalArchimedeanStandardUnitarizableStatement.{u}
```

The target is the published proposition
`Langlands.Automorphic.CuspidalArchimedeanStandardUnitarizableStatement` of
module `Langlands.Automorphic.CuspidalArchimedeanComponentStatement`. The module
imports that module and `Langlands.Automorphic.CuspidalUnitaryForm`. The proof
uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

## The statement

Let `F : Type u` be a number field with `CompactSpace (AdeleQuotient F)`, and
let `T : CuspidalOperatorRealization F r` be an actual cuspidal realization of
`GL_{r+1}` with `HasUnitaryCentralCharacter T`. The statement has two parts.

- If `T.realization.HasRealPlaceParameter v ds` at a real place `v`, then
  `Archimedean.IsRealUnitarizableGKModule (r + 1) (realStandardRep (r + 1) ds)
  (realStandardLie (r + 1) ds)`.
- If `T.realization.HasComplexPlaceParameter v ds` at a complex place `v`, then
  `Archimedean.IsComplexUnitarizableGKModule (r + 1)
  (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds)`.

The two unitarizability predicates (module
`Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement`)
ask for an `InvariantPositiveForm` of the compact representation, that is, a
positive definite Hermitian form invariant under `O(n)` (resp. `U(n)`), under
which every `π (1 ⊗ₜ X)` is skew, for `X` a real (resp. complex) matrix.

## Inputs from the Library

- `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
  (module `Langlands.Automorphic.CuspidalUnitaryForm`) gives
  `T.realization.IsUnitarizable`, which is `Nonempty T.realization.UnitaryForm`.
- `OperatorRealization.UnitaryForm` (module
  `Langlands.Automorphic.OperatorUnitaryForm`) is a structure with three fields.
  `finiteForm` is an `InvariantPositiveForm` of the finite adelic
  representation. `compact_invariant` gives invariance under
  `compactRepresentation k` for every `k` in the standard compact subgroup at
  infinity. `real_skew` gives skewness of
  `envelopingAction (envelopingGenerator F n (complexify F n X))` for every
  `X : ArchimedeanGL.RealLieAlgebra F n`.
- The place actions are restrictions of the global ones.
  `realPlaceCompactRepresentation v` is `compactRepresentation` composed with
  `realPlaceCompactInclusion F n v` (module
  `Langlands.Automorphic.PlaceCompactAction`). `realPlaceLieAction v X` is
  `envelopingAction (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X))`
  (`realPlaceLieAction_apply`, module `Langlands.Automorphic.PlaceLieAction`).
  By the `rfl` lemma `realPlaceComplexLieInclusion_tmul` (module
  `Langlands.Global.ArchimedeanPlaceLie`), the inclusion sends `1 ⊗ₜ X` to
  `1 ⊗ₜ realPlaceLieInclusion F n v X`. That is
  `complexify F n (realPlaceLieInclusion F n v X)` by the definition of
  `complexify` (module `Langlands.Global.ArchimedeanLieAlgebra`). Complex places
  use the `complexPlace…` versions of the same definitions.
- `InvariantPositiveForm.comap` (module `Langlands.Representation.Unitary.Basic`)
  pulls an invariant form back along an injective intertwining map, with
  `(b.comap f hf).inner v w = b.inner (f v) (f w)` by definition.
- `realStandardRep_apply_coe` and `realStandardLie_one_tmul_apply_coe` (module
  `Langlands.Representation.Archimedean.RealStandardModuleGKModule`) compute the
  standard actions on underlying functions: right translation by
  `Unitary.toUnits k`, and the right derivative along `X`. For complex places
  the standard actions are abbreviations of `principalSeriesRep` and
  `principalSeriesLie`, and the lemmas are `principalSeriesRep_apply_coe` and
  `principalSeriesLie_one_tmul_apply_coe` (module
  `Langlands.Representation.Archimedean.PrincipalSeriesGKModule`).

## The proof

Write `S` for an operator realization of `GL_n` and `b : S.UnitaryForm`. All
declarations below except the last are in namespace
`Langlands.Automorphic.OperatorRealization`.

1. **The form at a place.** `UnitaryForm.realPlaceCompactForm b v` is the
   `InvariantPositiveForm` of `S.realPlaceCompactRepresentation v` with the
   inner product of `b.finiteForm`. Its invariance is `b.compact_invariant` at
   `realPlaceCompactInclusion F n v k`. `UnitaryForm.complexPlaceCompactForm`
   is the same at a complex place. The `simp` lemmas
   `realPlaceCompactForm_inner` and `complexPlaceCompactForm_inner` say that the
   inner product is unchanged.
2. **Skewness at a place.** `UnitaryForm.realPlace_skew` states
   `b.inner (S.realPlaceLieAction v (1 ⊗ₜ X) f) g +
   b.inner f (S.realPlaceLieAction v (1 ⊗ₜ X) g) = 0` for every real matrix
   `X`. Its proof is the term `b.real_skew (realPlaceLieInclusion F n v X) f g`,
   which the elaborator accepts by definitional unfolding of the restrictions
   listed above. `UnitaryForm.complexPlace_skew` is the same at a complex
   place, for every complex matrix `X` regarded as a real direction.
3. **The compact clause of a parameter.** The place parameter states the
   compact equivariance of its map `A` for `k ∈ unitaryCompact ℝ n`, a subgroup
   of `GL_n(ℝ)`, acting on `S` through the matrix
   `⟨(k : Matrix _ _ ℝ), k.2⟩ ∈ Matrix.unitaryGroup`. The theorem
   `realPlaceParameter_compact` restates it for every
   `k ∈ Matrix.unitaryGroup (Fin n) ℝ`, the group of `realStandardRep`:
   `A (realStandardRep n ds k f) = S.realPlaceCompactRepresentation v k (A f)`.
   Apply the parameter at `⟨Unitary.toUnits k, k.2⟩`. The element
   `realStandardRep n ds k f` equals the translated function supplied by the
   parameter, by `Subtype.ext` and `realStandardRep_apply_coe`. The matrix
   attached to `⟨Unitary.toUnits k, k.2⟩` is `k`, by `Subtype.ext rfl`.
   `complexPlaceParameter_compact` is the same with
   `principalSeriesRep_apply_coe`.
4. **The Lie clause of a parameter.** `realPlaceParameter_lie` states
   `A (realStandardLie n ds (1 ⊗ₜ X) f) = S.realPlaceLieAction v (1 ⊗ₜ X) (A f)`.
   The parameter gives this for the derived function, and
   `realStandardLie_one_tmul_apply_coe` identifies `realStandardLie n ds (1 ⊗ₜ X) f`
   with it. `complexPlaceParameter_lie` is the same with
   `principalSeriesLie_one_tmul_apply_coe`.
5. **Pulling back.** `UnitaryForm.isRealUnitarizable_of_hasRealPlaceParameter`
   takes `b` and `S.HasRealPlaceParameter v ds` with map `A`, injectivity `hA`
   and the two clauses. Step 3 makes `A` an intertwining map `B` from
   `realStandardRep n ds` to `S.realPlaceCompactRepresentation v`
   (`LinearMap.intertwiningMap_of_isIntertwiningMap`). The witness of
   `IsRealUnitarizableGKModule` is `(b.realPlaceCompactForm v).comap B hA`, a
   positive definite invariant form because `A` is injective. Its value at
   `(f, g)` is `b.inner (A f) (A g)` by definition. Skewness under
   `realStandardLie n ds (1 ⊗ₜ X)` follows from step 4, applied to `f` and to
   `g`, and step 2 at `A f`, `A g`. The complex theorem
   `UnitaryForm.isComplexUnitarizable_of_hasComplexPlaceParameter` is the same.
6. **The statement.** `Langlands.Automorphic.cuspidalArchimedeanStandardUnitarizable`
   obtains `b` from `isUnitarizable_of_hasUnitaryCentralCharacter` and applies
   step 5 at `n = r + 1` to both parts.

The rank conditions `realRank ds = n` and `ds.length = n` of the parameters are
not used.

Steps 3 to 5 avoid `rw` on equations whose left side is `A (…)`. With `rw`,
locating the pattern makes Lean compare `A g` with `A (realStandardLie … f)`,
and the resulting unfolding of the Lie action exceeds the heartbeat limit. The
proofs use `congrArg`, `congrArg₂` and `Eq.trans` instead.

## Provenance

This is step 4 ("Unitarizability") of "Why the statements are true" in the
statement Markdown (`Langlands/Automorphic/CuspidalArchimedeanComponentStatement.md`).

The mathematics is from J. R. Getz and H. Hahn (2024), *An introduction to
automorphic representations*. The registered source is
`getz-hahn-2024-automorphic-representations` (SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). In §11.4,
pp.300–301 (PDF pp.311–312), a globally generic cuspidal representation
`(π, V)` is "realized on a closed subspace `V ≤ L²_cusp([G])`". After display
(11.14), in the number field case, `V_∞ ≅ ⊗̂_{v|∞} V_v` "for some irreducible
unitary representations `(π_v, V_v)`", where "the `V_v` are Hilbert spaces"
(p.301, before display (11.15)). The unitarity of the local factor is thus
inherited from the inner product on `L²_cusp`. Here the inner product is the form
`b`. It is the determinant-band `L²` form of
`isUnitarizable_of_hasUnitaryCentralCharacter`, which its Markdown describes
as the standard unitarity of the Petersson inner product, proved by an internal
route.

The following are derived content, not in the source:

- The local component is the standard module of the place parameter. It is
  embedded in the realization by the injective map `A`, not obtained as a tensor
  factor. The statement Markdown explains this choice (Notation, "Components").
- The form on the standard module is the restriction of `b` along `A`.
- Unitarity is infinitesimal: an invariant form of the compact group with skew
  real Lie directions, as in Knapp–Vogan (1995), display (0.5), printed p.6. This
  is the notion of the published unitarizability predicates.
- The hypothesis is `HasUnitaryCentralCharacter`. Getz–Hahn instead normalize
  the representation to be trivial on `A_{GL_n}` (p.309). The statement Markdown
  explains this choice (Notation, "Unitarity hypothesis").

## Scope

The module proves only `CuspidalArchimedeanStandardUnitarizableStatement`. The
companion `CuspidalArchimedeanPairRegularityReductionStatement`
is proved in module
`Langlands.Automorphic.CuspidalArchimedeanPairRegularityReductionProof`, which
takes the present statement as a hypothesis.
