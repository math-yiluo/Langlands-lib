# Conditional assembly of tempered scalar layers of the opposite Jacquet module

This module reduces the published proposition
`Langlands.GLTemperedOppositeJacquetScalarLayerStatement.{uF,uV,uW}` of
[TemperedOppositeJacquetScalarLayerStatement](TemperedOppositeJacquetScalarLayerStatement.md)
to a single bound on the upper Jacquet exponents of irreducible tempered
representations of `GL_n(F)`, the proposition
`Langlands.ScalarLayer.TemperedUpperExponentBound.{uF,uV}` defined below. That
bound is proved from **either** of two published statements:

- the forward direction of the `GL_n` exponent criterion
  `Langlands.GLTemperedExponentCriterionStatement.{uF,uV}` of
  [TemperedExponentStatement](TemperedExponentStatement.md), or
- the product-Levi necessity statement
  `Langlands.GLProductLeviTemperedExponentNecessityStatement.{uF,uV}` of
  [ProductLeviTemperedExponentNecessityStatement](ProductLeviTemperedExponentNecessityStatement.md),
  applied to the single-block Levi `GL_n`. Its proof is supplied by
  [ProductLeviTemperedExponentNecessityProof](ProductLeviTemperedExponentNecessityProof.md).

Its main results are

```text
glTemperedOppositeJacquetScalarLayer_of_upperBound
  (hup : ScalarLayer.TemperedUpperExponentBound.{uF,uV})
  (hinh : GLOppositeJacquetSubquotientExponentInheritanceStatement.{uF,uV,uW}) :
  GLTemperedOppositeJacquetScalarLayerStatement.{uF,uV,uW}

glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound
  (hup : ScalarLayer.TemperedUpperExponentBound.{uF,uV}) :
  GLTemperedOppositeJacquetScalarLayerStatement.{uF,uV,uW}

glTemperedOppositeJacquetScalarLayer_of
  (hcrit : GLTemperedExponentCriterionStatement.{uF,uV})
  (hinh : GLOppositeJacquetSubquotientExponentInheritanceStatement.{uF,uV,uW}) :
  GLTemperedOppositeJacquetScalarLayerStatement.{uF,uV,uW}

glTemperedOppositeJacquetScalarLayer_of_criterion
  (hcrit : GLTemperedExponentCriterionStatement.{uF,uV}) :
  GLTemperedOppositeJacquetScalarLayerStatement.{uF,uV,uW}

glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity
  (hnec : GLProductLeviTemperedExponentNecessityStatement.{uF,uV}) :
  GLTemperedOppositeJacquetScalarLayerStatement.{uF,uV,uW}
```

The theorems without `hinh` supply it by the published proof
`Langlands.glOppositeJacquetSubquotientExponentInheritance`. This module keeps
the criterion or necessity proof as an explicit hypothesis and does **not**
export an unconditional scalar-layer theorem. The product-Levi necessity
proof is available in its separate proof module; applying the adapter to
that proof remains a separate assembly step. The theorems
`glTemperedOppositeJacquetScalarLayer_of` and
`glTemperedOppositeJacquetScalarLayer_of_criterion` keep the types they had
when this module was first published.

The five theorems above are in namespace `Langlands`; every other result
below is in `Langlands.ScalarLayer`. The module introduces no axioms and uses
only `propext`, `Classical.choice` and `Quot.sound`.

## The definition `blockScalarCharacter`

Let `B : BlockShape n`, `R` a commutative ring, and give the product Levi
`B.Levi R = ∏ i, GL_(B.size i)(R)` any topology. For a complex representation
`ρ` of `B.Levi R` and a unitary central character datum
`c : UnitaryCentralCharacter ρ`,

```text
blockScalarCharacter B c := c.character.comp (B.blockScalarToCenter R)
  : (Fin B.length → Rˣ) →* ℂˣ.
```

Here `B.blockScalarToCenter R` is the published homomorphism sending
`a = (a_i)` to the block-scalar element `(a_i · 1)_i` of the centre of the Levi,
from [ProductLeviCentralCharacter](ProductLeviCentralCharacter.md). So
`blockScalarCharacter B c a` is the value of the central character on the block
scalar `diag(a_1 I, …, a_r I)`. Two lemmas record what it is used for:

- `hasScalarCharacter_blockScalarCharacter`: the block scalars act on `ρ`
  through this character, i.e.
  `Classification.HasScalarCharacter ρ (B.blockScalarLevi R) (blockScalarCharacter B c)`;
  this is `c.acts` at the central element `B.blockScalarToCenter R a`.
- `norm_blockScalarCharacter`: every value has complex norm `1`; this is
  `c.norm_eq_one`.

This is an internal restriction of a given character, introduced so that the
main proof can feed the unitary scalar action of `ρ` to the published lemma
`sum_fibre_eq_zero_of_unitary`.

## Accompanying lemmas

### Sufficiency for an arbitrary admissible representation

`tempered_of_upperExponentHypothesis T C`: for every block shape `C`, every
admissible complex representation `ρ` of `C.Levi F.Carrier`, every
`c : UnitaryCentralCharacter ρ` satisfying the published
`ProductLeviChamber.UpperExponentHypothesis T C ρ`, every Borel measurable
structure on `Q = C.Levi F.Carrier / Z` and every Haar measure `μ` on `Q`,
`IsTemperedModCenter ρ μ` holds, with `c` itself as the witness.

`UpperExponentHypothesis T C ρ` says: for every refinement `D` of `C` and every
open-kernel generalized eigencharacter `ψ` of the flattened block scalars on
the normalized refined upper Jacquet module of `ρ`, `‖ψ a‖ ≤ 1` whenever the
absolute values of `a` are monotone inside each outer block.

The Lean proof is the proof of the published
`ProductLeviTempered.tempered_of_cellCount` with its irreducible-specific steps
removed: that theorem builds its central character from an irreducible `S`
and a block-scalar character, while here `c` is given and `ρ` is arbitrary.
For a smooth functional `ℓ`, vector `v` and `ε > 0`, it puts
`η = ε / (4(2+ε))` and uses the published chamber estimate
`cell_coefficient_bound` (coefficient on a Cartan cell bounded by
`cb · ∏ δ^(1/2 - η)`), the cell measure bound `measure_cellQ_le` with the
published Cartan cell count `CartanQuotient.cartanCellCount`, and the fact that
cells indexed by the fundamental lattice `latticeTuple C m` cover `Q`. On each
cell the `L^(2+ε)` contribution is at most a constant times `∏ x_s^(m_s)` with
`x_s = fundWeight_s^((1/2-η)(2+ε) - 1) = fundWeight_s^(ε/4) < 1`. The published
lattice estimate `finiteNatLatticeENNRealSummability` makes the sum over `m`
finite, and the published `countableCellLpUpper` converts the cell bound into
`MemLp (c.coefficientNorm ℓ v) (2+ε) μ`.

### Dual exponents are exponents of the opposite Jacquet module

`pow_sub_smul_apply_of_eigen`: if `L x = μ • x` then
`(L - c • 1)^k x = (μ - c)^k • x`; proved by induction on `k`.

`isGeneralizedEigencharacter_of_isDualJacquetExponent`: let `A` be an
irreducible admissible representation of `GL_n(F)` and `ψ` a full-dual
exponent, `T.IsDualJacquetExponent B A ψ`, i.e. `ψ` has open kernel and the
transposed block-scalar action on the full algebraic dual of the opposite
Jacquet module has a nonzero `ψ`-eigenvector. Then `ψ` is a generalized
eigencharacter of the block scalars on the opposite Jacquet module itself,
`IsGeneralizedEigencharacter (T.splitCentreOppositeJacquet B A).ρ ψ`.

Proof: the opposite Jacquet module is admissible
(`Parabolic.isAdmissible_standardOppositeJacquet`) and finitely generated
(`Parabolic.oppositeJacquetFiniteGeneration`, using that `A` is irreducible,
hence cyclic). Hence the block-scalar operators span a finite-dimensional space
(`centralActionSpan_finite`) and act locally constantly
(`centralAction_isLocallyConstant`), and the published
`finiteActionCommutativeSpectrum` shows that the generalized character spaces
of open-kernel characters span the module. A nonzero eigenfunctional `φ` with
eigencharacter `ψ` is therefore nonzero on some vector `w` of some generalized
character space for a character `χ`, killed by all `(a - χ(a))^k`. Transposing,
`(ψ(a) - χ(a))^k φ(w) = 0`, so `ψ = χ`, and `w` witnesses the claim.

### Transport from opposite to upper Jacquet modules

`leviReverseEquiv_blockScalarLevi`: the published block relabelling
`OppositeCuspidalJacquetFiltration.leviReverseEquiv B` sends the block scalar
of `b ∘ Fin.rev` to the block scalar of `b` for the reversed shape `B.reverse`.

`isJacquetExponent_reverse`: if `ψ` has open kernel and is a generalized
eigencharacter of the block scalars on the opposite Jacquet module of `A`
along `B`, then `ψ ∘ (b ↦ b ∘ Fin.rev)` is an exponent of the upper normalized
Jacquet module of `A.ρ` along `B.reverse`, i.e. `T.IsJacquetExponent B.reverse
A.ρ (ψ.comp (precomp Fin.rev))`. The generalized eigenvector is moved through
the published equivalence
`OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv T B A` and the
published `ProductLeviDualOpposite.map_pow_sub_smul`; openness of the kernel is
preserved because relabelling coordinates is continuous.

### Real-part inequalities

`prefix_nonpos_of_antitone_bound`: let `χ` be a character of `(F^×)^r` with
real part `s` (`T.IsRealPartOf χ s`, i.e. `‖χ a‖ = ∏ |a_k|^(s_k)`). If
`‖χ a‖ ≤ 1` for every `a` whose absolute values are antitone in `k`, then every
inclusive prefix sum `∑_(k ≤ l) s_k` is `≤ 0`. Proof: take `a_k = ϖ^(-1)` for
`k ≤ l` and `a_k = 1` otherwise, with `ϖ` a uniformizer; then `|a|` is antitone
and `‖χ a‖ = q^(∑_(k ≤ l) s_k)`, with `q > 1` the residue cardinality.

`blockPrefix_nonpos_of_global`: for a refinement `D` of `C` and real numbers
`s` on the flattened labels, if all global prefix sums are `≤ 0` and the sum of
`s` over every outer block is `0`, then every prefix sum inside each outer
block is `≤ 0`. Proof: by the published order lemma
`flattenBlockEquiv_lt_iff`, the global prefix ending at label `(j, i)` is the
sum of all outer blocks before `j` (each zero) plus the prefix of block `j`
ending at `i`.

### The single-block Levi is `GL_n`

`oneBlockLeviEquiv T hn`: for `0 < n`, the published single-block shape
`CuspidalSupport.LeviAdmissibility.oneBlock n hn` (one block of size `n`) has
product Levi `∏_(i : Fin 1) GL_n(F)`, and evaluation at the unique block is an
isomorphism of topological groups onto `GL_n(F)` (type `≃ₜ*`, with the
topology `T.topology`). Its inverse sends `h` to the constant family `h`.
Both directions are continuous because evaluation and constant maps into a
product are continuous.

## The hypothesis interface `TemperedUpperExponentBound`

`TemperedUpperExponentBound.{uF,uV}` is the proposition: for every prime `p`,
`p`-adic field `F`, topological data `T`, `0 < n`, every irreducible complex
representation `π` of `GL_n(F)` on a space in universe `uV` with
`T.IsTempered π`, every block shape `B` of `n`, every exponent `χ` of the upper
normalized Jacquet module of `π` along `B` (`T.IsJacquetExponent B π χ`) and
every `a : Fin B.length → F^×` whose normalized absolute values are monotone,
`‖χ a‖ ≤ 1`. This is the content of Waldspurger's Proposition III.2.2,
direction (i)⇒(ii), for irreducible representations of `GL_n(F)` and the
standard upper parabolics; it is the exact form of the bound the main proof
consumes. It is an internal interface, introduced so that the main proof does
not depend on which of the two inputs below supplies it.

`temperedUpperExponentBound_of_criterion hcrit`: the forward direction of
`GLTemperedExponentCriterionStatement` gives the bound. Temperedness of `π` for
one Haar measure (`T.exists_isHaarMeasure_centralQuotient`) supplies a unitary
central character of `π`; restricted to scalar matrices through
`GeneralLinear.scalarToCenter` it gives the scalar character `ω_π` the
criterion requires, and `π` is admissible because it is tempered. Then
`(hcrit … ω_π hadm hω).mp htemp` is the bound.

`temperedUpperExponentBound_of_productLeviNecessity hnec`: the necessity
statement for product Levis gives the bound. Let `C = oneBlock n hn` and `e =
oneBlockLeviEquiv T hn`.

1. `σ = π ∘ e` is a representation of `C.Levi F`. It is irreducible by the
   published `isIrreducible_comp_continuousMulEquiv_iff`, so its space is
   nontrivial.
2. Choose a Borel Haar measure `ν` on `GL_n(F) / Z`
   (`T.exists_isHaarMeasure_centralQuotient`) and push it forward to the
   central quotient of `C.Levi F` by the inverse of the published
   `centralQuotientCongr e`, giving `μ`. The published
   `isTemperedModCenter_comp_continuousMulEquiv` turns `T.IsTempered π`
   (at `ν`) into `IsTemperedModCenter σ μ`.
3. `hnec` applied to `σ`, `μ` gives the core hypothesis: every open-kernel
   generalized eigencharacter of the flattened block scalars on every refined
   upper normalized Jacquet module of `σ` has norm `≤ 1` on blockwise monotone
   tuples.
4. From the unitary central character `c` contained in
   `IsTemperedModCenter σ μ`, `blockScalarCharacter C c` is a unitary character
   through which the block scalars act on `σ`; its kernel is open by the
   published `Classification.HasScalarCharacter.isOpen_ker`, using that the
   block-scalar map is continuous
   (`ProductLeviTemperedFactorization.continuous_blockScalarLevi`) and that
   `σ` is smooth.
5. The published `ProductLeviTemperedFactorization.jacquetExponent_bound_of_core`
   turns the core hypothesis for `σ` into the bound for exponents of a block
   factor. It is applied with the unique block `i = 0`, the block factor
   `τ = π` on `X = V`, insertion and contraction both the identity map (the
   required compatibilities hold by `rfl` and `Pi.mulSingle_eq_same`, since a
   family over `Fin 1` is determined by its value at `0`), and the refinement
   `D` that refines the unique block by `B`; the side condition "every other
   block has length one" is vacuous. Its conclusion is `‖χ a‖ ≤ 1` for every
   exponent `χ` of the upper Jacquet module of `π` along `B` and every monotone
   `a`.

## The conditional main theorem

`glTemperedOppositeJacquetScalarLayer_of_upperBound hup hinh` proves the exact
published proposition. Fix the data of that statement: `π` irreducible and
`T.IsTempered π`, `c : UnitaryCentralCharacter ρ`, a subrepresentation `S` of
the opposite normalized Jacquet representation `J` with a surjective
intertwiner `q : S → ρ`, and a Haar measure `μ` on `M / Z(M)`.

1. *Admissibility of `ρ`.* `π` is admissible (from temperedness), so `J` is
   admissible (`Parabolic.isAdmissible_standardOppositeJacquet`); so is `S`
   (`isAdmissible_of_injective` along the inclusion), and so is its quotient
   `ρ` (`Unramified.SphericalExistence.isAdmissible_of_surjective`, using
   compact open subgroups of the Levi from `T.leviCompactOpen`).
2. *Exponent bounds for `π`.* `hup` applied to the irreducible tempered `π`
   gives: for every block shape `B'`, every exponent `χ` of the upper
   normalized Jacquet module of `π` along `B'`, and every `a` with monotone
   absolute values, `‖χ a‖ ≤ 1`.
3. *Reduction to upper exponents of `ρ`.* By
   `tempered_of_upperExponentHypothesis` with the given `c`, it suffices to
   prove `UpperExponentHypothesis T B ρ`. Fix a refinement `D`, an open-kernel
   generalized eigencharacter `ψ` of the refined upper Jacquet module of `ρ`
   and `a` blockwise monotone.
4. *To an opposite dual exponent of `π`.* The published
   `isGeneralizedEigencharacter_reverse` turns `ψ` into a generalized
   eigencharacter `ψ'` (relabelled by `reverseLabel B D`) of the refined
   opposite Jacquet module of `ρ` along `reverseRefinement B D`, which is
   admissible (`Parabolic.isAdmissible_normalizedRefinedOppositeJacquet`).
   The published
   `DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter`
   gives a nonzero dual eigenfunctional `φ` with eigencharacter `ψ'`. The
   inheritance input `hinh` then makes `ψ'` a dual exponent of `π` along the
   flattened shape `B' = B.flatten (reverseRefinement B D)`.
5. *To an upper exponent of `π`.* By
   `isGeneralizedEigencharacter_of_isDualJacquetExponent` and
   `isJacquetExponent_reverse`, `ψ' ∘ rev` is an exponent of the upper Jacquet
   module of `π` along `B'.reverse`. Step 2 gives `‖ψ' b‖ ≤ 1` for every `b`
   with antitone absolute values.
6. *Real-part inequalities.* Let `s` be a real part of `ψ'`
   (`T.exists_isRealPartOf`). By `prefix_nonpos_of_antitone_bound` all global
   prefix sums of `s` are `≤ 0`. Since the outer block scalars act on `ρ` by
   the unitary `blockScalarCharacter B c`, the published
   `sum_fibre_eq_zero_of_unitary` makes the sum of `s` over each outer block
   `0`. By `blockPrefix_nonpos_of_global` the prefix sums inside each outer
   block are `≤ 0`.
7. *Conclusion.* `‖ψ a‖ = ‖ψ' (a ∘ reverseLabel)‖ = exp(∑ s_b log|a_b|)`.
   Inside each outer block, reversing the inner order turns the monotone
   `log|a|` into an antitone vector; the published summation by parts
   `ParabolicConeUniqueness.sum_mul_nonpos_of_antitone` (nonpositive prefix
   sums, zero total, antitone weights) makes each block contribution `≤ 0`.
   Hence `‖ψ a‖ ≤ 1`.

The remaining theorems are compositions:

- `glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound hup` is
  `glTemperedOppositeJacquetScalarLayer_of_upperBound hup
  glOppositeJacquetSubquotientExponentInheritance`;
- `glTemperedOppositeJacquetScalarLayer_of hcrit hinh` is
  `glTemperedOppositeJacquetScalarLayer_of_upperBound
  (temperedUpperExponentBound_of_criterion hcrit) hinh`;
- `glTemperedOppositeJacquetScalarLayer_of_criterion hcrit` is
  `glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound
  (temperedUpperExponentBound_of_criterion hcrit)`;
- `glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity hnec` is
  `glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound
  (temperedUpperExponentBound_of_productLeviNecessity hnec)`.

## Scope and status

- The main proof uses only `TemperedUpperExponentBound`, i.e. the bound
  for irreducible tempered representations of `GL_n(F)`. It is supplied
  either by the forward implication (temperedness implies the exponent
  bounds) of `GLTemperedExponentCriterionStatement`, owned by task
  `c98c74eb-a4cb-4924-8df8-f7556ca47689`, or by
  `GLProductLeviTemperedExponentNecessityStatement` for the single-block
  Levi, owned by task `b0fd413c-ec79-49a5-a99b-8ba0ec7c77aa`. The latter now has
  the separate proof linked above; this module's interfaces remain conditional.
- The module does not assume irreducibility, finite length or semisimplicity
  of `ρ`, nor admissibility of `ρ`; admissibility is proved.
- No new statement of a published task is introduced; the target statement
  pair and every imported pair are unchanged. `TemperedUpperExponentBound` is
  an internal hypothesis interface, not a task statement.

## Provenance

The route is derived, not verbatim. Waldspurger, *La formule de Plancherel pour
les groupes p-adiques d'après Harish-Chandra* (2003), registered as
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7` (PDF page =
printed page − 234):

- Proposition III.2.2, printed pp.265–266: an admissible representation is
  tempered iff the real parts of all exponents of all semi-standard Jacquet
  modules lie in the closed positive cone. The implication (i)⇒(ii) for
  irreducible representations of `GL_n(F)` is `TemperedUpperExponentBound`,
  supplied by `hcrit` (the same implication for admissible `GL_n`
  representations) or by `hnec` (the same implication for irreducible
  representations of product Levis, specialised to the single-block Levi); the
  implication (ii)⇒(i) for the Levi `M` is the role of
  `tempered_of_upperExponentHypothesis`, whose Lean proof is the Library's
  Cartan-cell argument rather than Waldspurger's `Ξ` estimate.
- §III.3 and Lemma III.3.1, printed p.267: the weak part of a tempered Jacquet
  module is tempered. The present proof does not pass through the
  decomposition `π_P = π_P^w ⊕ π_P^+`; instead it shows directly that every
  upper exponent of the scalar layer `ρ` satisfies the bound of
  Proposition III.2.2(ii) for `M`, using that the exponents of `ρ` are
  inherited from those of `π` (`hinh`) and that `ρ` has a unitary central
  character (zero block totals of the real part).
- I.3, printed pp.243–244: generalized eigenspace decomposition of Jacquet
  modules under the split centre, the source of the notions of exponent used
  in steps 4–5.

`blockScalarCharacter` is an internal construction (restriction of a given
central character to the block-scalar torus) with no separate literature
source. `oneBlockLeviEquiv` is the internal identification of the
single-block product Levi with `GL_n(F)`, and `TemperedUpperExponentBound` is
an internal interface stating the Proposition III.2.2 bound in the form used
here; neither has a separate literature source.
