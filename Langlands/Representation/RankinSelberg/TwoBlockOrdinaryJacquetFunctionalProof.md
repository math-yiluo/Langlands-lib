# Proof of the ordinary two-block Jacquet functional realization

Module `Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalProof`.

Author: Worker 1133.

The module proves

```lean
theorem Langlands.RankinSelberg.twoBlockOrdinaryJacquetFunctional :
    TwoBlockOrdinaryJacquetFunctionalStatement.{uF, uW}
```

for the published closed proposition
`Langlands.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`
(module `Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`).
The statement's Lean/Markdown pair and everything it imports are unchanged.
The theorem's universe parameters are `uF, uW`, in the statement's order. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

The proof keeps every binder of the statement: every prime `p` and
`F : PadicField.{uF} p` with its canonical topology and Borel σ-algebra, every
`ψ : UnitaryAdditiveCharacter F.Carrier`, every supplied self-dual Haar measure
`ν`, every `t`, `m`, `h : ∑ i, (m i + 1) = t + 1` (rank-one blocks included),
every dependent family of complex carriers `W : Fin 2 → Type uW`, blocks `τ i`
of full standard Whittaker type (reducible blocks included), and supplied
`ell i : glInverseFunctionals ψ (m i) (τ i)` with `(ell i).val ≠ 0`. It adds no
premise. For these data it gives one real `C` such that for every real `u > C`,
writing `σ_u = twoBlockOppositeTwistBlocks F m τ u` and
`μ = rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)`:

1. every section `f` of `TwoBlockJacquet.Sections F h σ_u` satisfies
   `TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val) μ f`, so the raw
   integrand of JPSS (4.6.2) is Mathlib-`Integrable` at every ambient `g`;
2. the functional `J(f) = jacquetFunction ψ (fun i => (ell i).val) μ f 1` lies in
   `glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ_u)` and is
   nonzero, and for every section `f` and every `g : GL_(t+1)(F)`,
   `J(inducedRep F h σ_u g f) = jacquetFunction ψ (fun i => (ell i).val) μ f g`.

The bound `C` is exactly the bound of the published convergence theorem. It
does not depend on `u`, `f` or `g`.

## Route and provenance

JPSS 1983 (source ID `jpss-1983-rankin-selberg`), Section (4.6), printed pages
410–411, prove that (4.6.2) converges for `u ≫ 0` and say that the resulting
function of `g` "evidently" belongs to `W(σ_u; ψ̄)`; Whittaker type and the
coefficient spaces are in Section (2.1), printed pages 385–386. As the
statement's Markdown explains, the target is only the realization half of that
assertion. Its content is: `J(f) := (4.6.2)` at `g = 1` is a well-defined
linear functional, it is `ψ̄`-equivariant, it is nonzero, and its coefficients
`g ↦ J(σ_u(g) f)` are the integrals. The Lean proof assembles exactly these four
facts from published results, as below. It contains no new analysis.

## Helper declarations

Namespace `Langlands.RankinSelberg.TwoBlockOrdinaryJacquet` holds the helpers.
They are stated for arbitrary blocks
`σ : ∀ i, Representation ℂ (GL_(m i + 1)(F)) (W i)`, arbitrary linear maps
`ell : ∀ i, W i →ₗ[ℂ] ℂ`, an arbitrary measurable structure on `F.Carrier` and an
arbitrary measure `μ` on the rectangle `M((m 0 + 1) × (m 1 + 1))(F)`, together
with the hypothesis

```lean
hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1
```

that every section's integrand is absolutely integrable at the identity.

- `ordinaryJacquetFunctional F h ψ σ ell μ hint : Sections F h σ →ₗ[ℂ] ℂ` is
  the map `f ↦ jacquetFunction ψ ell μ f 1`. Additivity is
  `TwoBlockJacquet.jacquetFunction_add`, applied with `hint f` and `hint f'`.
  `hint` is needed here because the Bochner integral is additive only for
  integrable integrands. Homogeneity is `TwoBlockJacquet.jacquetFunction_smul`,
  which needs no integrability.
- `ordinaryJacquetFunctional_apply`: its value at `f` is
  `jacquetFunction ψ ell μ f 1` (by `rfl`).
- `ordinaryJacquetFunctional_inducedRep`: for every `g` and `f`,
  `ordinaryJacquetFunctional … (inducedRep F h σ g f) = jacquetFunction ψ ell μ f g`.
  This rewrites with `_apply`, then with the right-translation identity
  `TwoBlockJacquet.jacquetFunction_inducedRep`
  (`J(f')(1)` for `f' = σ(g) f` becomes `jacquetFunction … f (1 * g)`), then
  with `one_mul`. The step is an identity of Bochner integrals and needs no
  integrability.
- `ordinaryJacquetFunctional_mem`: if each `ell i` lies in
  `glInverseFunctionals ψ (m i) (σ i)`, then for every Borel structure on the
  rectangle and every additive Haar measure `μ`, the functional lies in
  `glInverseFunctionals ψ t (inducedRep F h σ)`. Membership unfolds to
  `J(σ(n) f) = ψ̄(n) J(f)` for upper unipotent `n` and
  `ψ̄ = inverseStandardCharacter ψ t`. This is exactly
  `TwoBlockDeformation.jacquetFunction_inducedRep_upperUnipotent`, a change of
  variables in the rectangle that holds for every section with no
  integrability. The section variables of that lemma need `MeasurableAdd₂` and
  `MeasurableMul` on `F.Carrier`, so the helper requires them too.
- `ordinaryJacquetFunctional_ne_zero`: if every `σ i` is smooth and every
  `ell i ≠ 0`, then for every Borel structure on the rectangle and every
  additive Haar measure `μ`, the functional is nonzero.
  `TwoBlockDeformation.exists_section_jacquetFunction_one_ne_zero` supplies a
  section `f` with `jacquetFunction ψ ell μ f 1 ≠ 0`. If the functional were
  zero, `_apply` would make this value zero.

## Assembly of the main theorem

`twoBlockOrdinaryJacquetFunctional` introduces the statement's binders and then:

1. It installs the canonical topological data of `F`: the topology, the
   valuative relation and the local-field structure, together with
   `SecondCountableTopology F.Carrier` from
   `F.canonicalTopologicalData.secondCountableTopology`. It sets the measurable
   space to `borel F.Carrier`, the statement's own σ-algebra, so `BorelSpace F.Carrier`
   holds by `rfl`. It also gives the rectangle
   `Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier` its product Borel
   structure (`inferInstanceAs` of the `BorelSpace` instance on iterated
   functions). Instance search then finds
   `(rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)).IsAddHaarMeasure` through
   `rectangularMeasure_isAddHaar`.
2. It obtains `⟨C, hC⟩` from the published
   `Langlands.RankinSelberg.twoBlockJacquetConvergence p F ψ ν t m h τ hτ ell hell`.
   It uses this `C`, and for `u > C` the first clause is `hC u hu`.
3. For the second clause it puts `σ = twoBlockOppositeTwistBlocks F m τ u`,
   `ell' i = (ell i).val` and `μ = rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)`,
   and records three facts:
   - `hint f := hC u hu f 1`: integrability at the identity, from clause 1;
   - `hmem i`: `ell' i ∈ glInverseFunctionals ψ (m i) (σ i)`. This is the
     property of the published `twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)`,
     whose underlying linear map is `(ell i).val`;
   - `hsmooth i`: `σ i` is smooth. `twoBlockOppositeTwistBlocks_isOfWhittakerType_iff`
     (with `θ = standardCharacter ψ (m i)`) transfers `hτ i` to the twisted
     block, and the first component of `IsOfWhittakerType` is `IsAdmissible`,
     whose first component is `IsSmooth`.
4. It takes `J = ⟨ordinaryJacquetFunctional F h ψ σ ell' μ hint,
   ordinaryJacquetFunctional_mem F h ψ σ ell' hmem μ hint⟩`. Nonvanishing is
   `ordinaryJacquetFunctional_ne_zero F h ψ σ ell' hsmooth hell μ hint`, which
   uses the statement's hypothesis `(ell i).val ≠ 0`. The coefficient identity
   for `f` and `g` is `ordinaryJacquetFunctional_inducedRep F h ψ σ ell' μ hint g f`.

## Remarks on the integral

`TwoBlockJacquet.jacquetFunction` is a Bochner integral, which Mathlib sets
to `0` for non-integrable integrands. Clause 1, which the proof takes directly
from the convergence theorem, makes the integrand integrable at every `g`
for `u > C`. So `J(f)` and every coefficient `J(σ_u(g) f)` in the conclusion
are genuine absolutely convergent integrals. The proof itself uses
integrability only at `g = 1`, and only for additivity of `J`. Equivariance,
the coefficient identity and nonvanishing are proved for the Bochner integral
without integrability hypotheses.

## Not proved

This module proves only the target proposition and the helper lemmas above. It
does not show that the coefficient image of `J` equals that of any other
nonzero `ψ̄`-functional of `σ_u` (the comparison half of the JPSS sentence), nor
that `σ_u` has Whittaker type. It proves no uniqueness of functionals, stable
integrals, analytic continuation in `u`, or functional equations.
