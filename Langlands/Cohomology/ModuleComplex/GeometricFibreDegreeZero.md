# Strictly perfect complexes whose geometric fibres are concentrated in degree zero

Module `Langlands.Cohomology.ModuleComplex.GeometricFibreDegreeZero`.

This is a ring-level form of cohomology and base change. Let `R` be a
commutative ring in universe `u` and let `K` be a strictly perfect `ℤ`-indexed
cochain complex of `R`-modules (`IsStrictlyPerfect K`: bounded, with finite
projective terms). Suppose its geometric fibres have cohomology only in degree
zero, of dimension `r`. Then `H^0(K)` is a finite projective `R`-module of
constant rank `r`, and forming `H^0` commutes with every scalar extension
`R → S`.

## Definitions

- `GeometricFibresDegreeZero K r` is the hypothesis. Let `k : Type u` be any
  algebraically closed field and `φ : R →+* k` any ring map. Then the
  degreewise scalar extension `(baseChange φ).obj K` has zero homology in
  every degree `i ≠ 0`, and its degree-zero homology has `Module.finrank k`
  equal to `r`. Here `baseChange φ` is the Library functor that applies
  `ModuleCat.extendScalars φ` termwise.
- The imported `Langlands.Scheme.Modules.extendScalarsToAlgebraTensor`,
  `algebraTensorToExtendScalars` and `extendScalarsAlgebraEquiv` from
  [ExtendScalarsTensor](../../Algebra/ExtendScalarsTensor.md), applied to
  `CommRingCat.of A` and `CommRingCat.of B`, relate two descriptions of `B ⊗_A M`.
  Here `B` is an `A`-algebra and `M` an `A`-module. The first description is
  `(ModuleCat.extendScalars (algebraMap A B)).obj M`, in which `B` is an
  `A`-module through `ModuleCat.restrictScalars`. The second is the algebra
  tensor product `B ⊗[A] M`. The two `A`-module structures on `B` agree only
  propositionally. The two additive maps send `b ⊗ₜ m` to `b ⊗ₜ m`, and the
  equivalence is `B`-linear.
- `tensorHomologyZeroEquiv hK h S` is an `S`-linear equivalence for an
  `R`-algebra `S : Type u`, under the main hypotheses:
  `S ⊗[R] H^0(K) ≃ₗ[S] H^0((baseChange (algebraMap R S)).obj K)`. It is the
  inverse of `Langlands.Scheme.Modules.extendScalarsAlgebraEquiv` followed by the Library comparison
  `baseChangeHomologyMap (algebraMap R S) K 0`, which is an isomorphism by
  `isIso_baseChangeHomologyMap_zero`.

## Main results

Throughout, `hK : IsStrictlyPerfect K` and `h : GeometricFibresDegreeZero K r`.

- `homology_zero_of_geometricFibresDegreeZero hK h` combines four statements:
  1. `Module.Finite R (K.homology 0)`;
  2. `Module.Projective R (K.homology 0)`;
  3. `Module.rankAtStalk (K.homology 0) p = r` for every
     `p : PrimeSpectrum R`;
  4. `IsIso (baseChangeDerivedHomologyMap φ K 0)` for every commutative ring
     `S : Type u` and every `φ : R →+* S`.

  The map in (4) is the Library's derived-category comparison
  `S ⊗_R H^0(K) ⟶ H^0(S ⊗_R K)`. It is used with the standard derived
  categories (`HasDerivedCategory.standard`).
- `homology_zero_finite_projective_rank hK h` is (1)–(3).
- `isIso_baseChangeDerivedHomologyMap_zero hK h φ` is (4).
- `isIso_baseChangeHomologyMap_zero hK h φ` is (4) for the comparison
  `baseChangeHomologyMap φ K 0` on homology of complexes.
- `exactAt_pos_of_geometricFibresDegreeZero hK h`: `K` is exact in every
  degree `j > 0`, and the image of the differential `K^0 → K^1` is a
  projective `R`-module.

## Auxiliary results

- `exactAt_pos_of_residue_exactAt_pos hK hres`: suppose that for every maximal
  ideal `m` the reduction `(baseChange (Ideal.Quotient.mk m)).obj K` is exact
  in every degree `i > 0`. Then `K` is exact in every degree `j > 0`, and the
  image of `K^0 → K^1` is projective.
- `isZero_X_of_rank_eq_zero`: a term of a model whose prescribed rank is zero is
  the zero module.
- `exists_degreeZero_model hK h p`: let `p` be a prime ideal. There is
  `s ∉ p` such that `K` has a finite free model over `Localization.Away s`
  with term ranks `n`, in the sense of the Library predicate
  `FibreH0Spread.HasModel`. Moreover `n 0 = r`, `n i = 0` for `i ≠ 0`, and
  `n 0` equals the dimension over the residue field `κ(p)` of
  `H^0(κ(p) ⊗_R K)`.
- `isZero_homology_of_hasModel`: if a model along `α : R →+* A` has rank zero in
  degree `i`, then for every `β : A →+* T` the scalar extension of `K` along
  `β ∘ α` has zero homology in degree `i`.
- `residue_exactAt hK h m hm i hi`: each reduction at a maximal ideal is exact
  in every degree `i ≠ 0`.
- `flat_truncLE_zero_X hK h i`: every term of Mathlib's canonical truncation
  `K.truncLE 0` is flat.
- `exists_away_tensor_homology_equiv hK h p`: for every prime `p` there is
  `s ∉ p` with
  `Localization.Away s ⊗[R] H^0(K) ≃ₗ (Fin r → Localization.Away s)`.

## Proof

**Local models.** Fix a prime `p`. The Library theorem
`FibreH0Spread.exists_hasModel_rank` gives `s ∉ p` and a finite free model `P`
of `K` over `R_s = Localization.Away s`. Its term ranks `n i` are the
dimensions of `H^i(κ(p) ⊗_R K)`. Lift `R → κ(p)` to `R_s → κ(p)`, and let `k`
be an algebraic closure of `κ(p)`. The Library lemma `FibreH0Spread.fibre_data`
shows that the model's differentials vanish after extension to `k`, so `n i` is
also the dimension of `H^i(k ⊗_R K)`. The hypothesis then gives `n 0 = r` and
`n i = 0` for `i ≠ 0`. This is `exists_degreeZero_model`.

**Exactness in positive degrees.** Let `m` be a maximal ideal. Take a model at
`m`, and lift `R_s → R/m` (`s` is a unit modulo `m`). The model has rank zero
outside degree zero, so `isZero_homology_of_hasModel` shows that `R/m ⊗_R K` is
exact outside degree zero (`residue_exactAt`). The proof of
`exactAt_pos_of_residue_exactAt_pos` is a descending induction on the degree
`k ≥ 0`, starting above the upper bound of `K`. The inductive statement is that
the image of `K^k → K^{k+1}` is projective and `K` is exact in every degree
above `k`.

For the step, suppose the image of `K^{k+1} → K^{k+2}` is projective. Then the
kernel of `K^{k+1} → K^{k+2}` is a direct summand of `K^{k+1}`: the Library
lemma `exists_retraction_ker` supplies a retraction. The Library lemma
`ker_le_range_of_residue_exactAt` then uses exactness of every reduction at
degree `k + 1` to show that this kernel lies in the image of `K^k → K^{k+1}`.
So the image equals the kernel. It is therefore projective, as a direct summand
of a projective module, and `K` is exact at `k + 1`. This is the argument of
Mumford's Corollary 3 in §5, in ring form, iterated downwards.

**Base change of `H^0`.** Since `K` is exact in positive degrees, the
truncation map `K.ιTruncLE 0 : K.truncLE 0 ⟶ K` is a quasi-isomorphism.
`flat_truncLE_zero_X` shows that the truncation has flat terms:

- in negative degrees, its terms are those of `K`;
- in degree zero, its term is the kernel of `K^0 → K^1`, which is a direct
  summand of `K^0` because the image of `K^0 → K^1` is projective;
- in positive degrees, its terms are zero.

Both complexes are strictly bounded above and have flat terms. So the Library
theorem `quasiIso_baseChange_map_of_flat` shows that scalar extension along any
`φ` keeps the truncation map a quasi-isomorphism. The Library naturality result
`isIso_baseChangeDerivedHomologyMap_iff` reduces (4) for `K` to (4) for
`K.truncLE 0`. That truncation vanishes in degree `1`, so (4) holds for it by
`isIso_baseChangeDerivedHomologyMap_of_isZero` (right exactness of scalar
extension). The Library identity `baseChangeDerivedHomologyMap_eq` transfers
the result to `baseChangeHomologyMap`.

**Local freeness and rank.** At a prime `p`, take `s` and the model `P` from
`exists_degreeZero_model`. Every differential of `P` vanishes: its terms are
zero outside degree zero, and `d 0 0 = 0` by the shape of the complex. The
Library lemma `FibreH0Spread.nonempty_homology_equiv_fin` therefore gives
`H^0(R_s ⊗_R K) ≃ R_s^{n 0} = R_s^r`. Composing with `tensorHomologyZeroEquiv`
for `S = R_s` proves `exists_away_tensor_homology_equiv`.

Let `t` be the set of `s` for which such an equivalence exists. Then `t`
generates the unit ideal: otherwise it would lie in a maximal ideal `m`,
contradicting `exists_away_tensor_homology_equiv` at `m`. Each `R_s ⊗[R] H^0(K)`
with `s ∈ t` is free of finite rank over `R_s`. So Mathlib's
`Module.flat_of_isLocalized_span` and
`Module.FinitePresentation.of_localizationSpan'` show that `H^0(K)` is flat and
finitely presented. Hence it is projective
(`Module.Flat.projective_of_finitePresentation`) and finite. Finally, Mathlib's
`Module.rankAtStalk_eq` identifies the rank at `p` with the dimension of
`κ(p) ⊗[R] H^0(K)`. By `tensorHomologyZeroEquiv` for `S = κ(p)` this is the
dimension of `H^0(κ(p) ⊗_R K)`, which is `n 0 = r` by
`exists_degreeZero_model`.

## Provenance

The main result is an internal ring-level form of cohomology and base change,
with the complex `K` playing the role of the finite projective complex in
Mumford's theorem.

- Mumford, *Abelian Varieties*, Chapter II, §5, p.46: the theorem representing
  `H^p(X ×_Y Spec B, F ⊗_A B)` functorially by `H^p(K^• ⊗_A B)` for a finite
  complex `K^•` of finitely generated projective `A`-modules.
- Corollary 2 (pp.50–52): constant fibre dimension gives a locally free
  direct image whose formation commutes with base change.
- Corollary 3 (p.53), with its proof: fibrewise vanishing in degree `p` gives
  base change in degree `p - 1`, by splitting the complex near each point.

The hypothesis here is stated over all algebraically closed fields rather than
residue fields. The proof does not follow Mumford's Corollary 2, which uses a
reduced base. Instead it combines the descending-induction argument of
Corollary 3 with the Library's local finite free models
(`FibreH0Spread`, after Stacks `lemma-lift-perfect-from-residue-field`), and
it does not assume `R` noetherian. No geometric statement is made in this
module.
