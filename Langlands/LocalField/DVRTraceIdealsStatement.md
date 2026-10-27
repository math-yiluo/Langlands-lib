# Exact trace images of ideal powers in an extension of DVRs

`Langlands.LocalField.DVRTraceIdeals.{uA,uB,uK,uL}` is the proposition that,
for a finite extension of discrete valuation rings `B/A` whose fraction-field
extension `L/K` is finite and separable, with ramification index `e` and
different `𝔡(B/A) = m_B ^ d`, the field trace maps `m_B ^ n` onto exactly
`m_A ^ ⌊(d + n) / e⌋`:

`Tr_{L/K}(m_B ^ n) = m_A ^ ⌊(d + n) / e⌋` for every `n ≥ 0`,

as subsets of `K`. The declaration is a `Prop`-valued definition. This module
states the formula and does not prove it. It also contains one structural
helper theorem, `Langlands.LocalField.isTorsionFree_of_isFractionRing_tower`,
which is proved in the module and is needed only so that Mathlib's
`differentIdeal A B` can be formed.

## Carriers and structures

The four carriers `A : Type uA`, `B : Type uB`, `K : Type uK` and
`L : Type uL` have independent universe parameters. All carriers, structures
and hypotheses are quantified inside the proposition. None is fixed, and no
equal-universe restriction is imposed.

- `A` and `B` are commutative integral domains with
  `IsDiscreteValuationRing` instances. `A` gets the instance
  `IsIntegrallyClosed A` and `B` gets `IsDedekindDomain B` from Mathlib's
  instances for discrete valuation rings. `differentIdeal` needs both.
- `Algebra A B` is the ring map from `A` to `B`. The hypotheses
  `IsIntegralClosure B A L` and `Module.Finite A B` say that `B`, through
  `B → L`, is the integral closure of `A` in `L`, and that `B` is a
  finitely generated `A`-module.
- `K` and `L` are fields. `Algebra A K` with `IsFractionRing A K` makes `K` a
  fraction field of `A`. `Algebra B L` with `IsFractionRing B L` makes `L` a
  fraction field of `B`.
- `Algebra K L` is the field extension whose trace is used.
  `FiniteDimensional K L` and `Algebra.IsSeparable K L` say that it is finite
  and separable. The extra `Algebra A L` and the two hypotheses
  `IsScalarTower A K L` and `IsScalarTower A B L` say that `A → K → L` and
  `A → B → L` are both this same map `A → L`.

Every map and trace in the conclusion uses these supplied structures. The
proposition does not assume completeness, a Galois extension, a perfect residue
field, or any p-adic structure.

## The torsion-freeness helper

Mathlib's `differentIdeal A B` requires an instance `Module.IsTorsionFree A B`.
This is not assumed. It is derived from the supplied structure by
`isTorsionFree_of_isFractionRing_tower`, which is proved in this module and
installed by `haveI` inside the proposition. The proof shows that
`algebraMap A B` is injective, which is equivalent to torsion-freeness for
domains (`Module.isTorsionFree_iff_algebraMap_injective`). If two elements of
`A` have the same image in `B`, they have the same image in `L` through
`A → B → L`. That is also the map `A → K → L` by the two scalar-tower
hypotheses. Both `A → K` (`IsFractionRing.injective`) and the field map
`K → L` are injective, so the two elements are equal. The helper uses only
the domain, field, fraction-ring and scalar-tower structures, not any
arithmetic. Torsion-freeness is a proposition, so any other proof of it,
such as a host instance, gives the same `differentIdeal A B`.

## Hypotheses

Write `mA = IsLocalRing.maximalIdeal A` and `mB = IsLocalRing.maximalIdeal B`.
For all natural numbers `e` and `d`, the proposition assumes:

1. `0 < e`.
2. `Ideal.map (algebraMap A B) mA = mB ^ e`. This is the literal ideal
   equality saying that `mA B = m_B ^ e`, so `e` is the ramification index.
3. `differentIdeal A B = mB ^ d`. This is the literal equality with Mathlib's
   different ideal from `Mathlib.RingTheory.DedekindDomain.Different`, with
   exponent `d`.

No hypothesis concerns the trace, its image, or its surjectivity.

## The actual different

Mathlib defines `differentIdeal A B : Ideal B` as the inverse of the trace dual
of `1`, computed in `FractionRing A` and `FractionRing B`. With the supplied
`K` and `L`, the lemma `coeIdeal_differentIdeal` states

`↑(differentIdeal A B) = (FractionalIdeal.dual A K 1)⁻¹`

as fractional ideals of `B` in `L`. Here `FractionalIdeal.dual A K 1` is the
set of `y ∈ L` with `Tr_{L/K}(y x) ∈ A` for all `x ∈ B`. This is Serre's
codifferent `B*`, and the different is its inverse, as in Local Fields,
Chapter III §3. The lemma `differentialIdeal_le_fractionalIdeal_iff` states
that, for a nonzero fractional ideal `I` of `B` in `L`,
`differentIdeal A B ≤ I` holds if and only if the trace of `I⁻¹`, as an
`A`-submodule of `K`, is contained in `1`, the image of `A` in `K`. This is
the Mathlib form of Serre's Proposition 7 below, in the case `a = A`.
Hypothesis 3 therefore names the genuine different, not a surrogate
certificate.

## Conclusion and its pointwise meaning

For every `n : ℕ`, put `r := (d + n) / e`. For every `y : K`, the conclusion is
the equivalence

```
(∃ x : B, x ∈ mB ^ n ∧ Algebra.trace K L (algebraMap B L x) = y) ↔
  (∃ a : A, a ∈ mA ^ r ∧ algebraMap A K a = y)
```

The left side says that `y` is the trace of the image in `L` of some element of
`mB ^ n`, so it describes the set image `Tr_{L/K}(m_B ^ n) ⊆ K`. The right side
says that `y` is the image in `K` of an element of `mA ^ r`. Quantified over
all `y`, the equivalence says that these two subsets of `K` are equal.

Reading the equivalence from right to left gives, for each `a ∈ m_A ^ r`, one
actual element `x ∈ m_B ^ n` with `Tr_{L/K}(x) = a`. It does not merely place
`a` in the `A`-span of trace values. Reading it from left to right says that
every trace of an element of `m_B ^ n` lies in the image of `m_A ^ r`, so in
particular in the image of `A`.

Serre's `Tr(p_L^n)` is the image of an `A`-submodule under an `A`-linear map.
The set of values `{Tr(x) : x ∈ m_B ^ n}` is already closed under addition and
multiplication by `A`, so it equals the `A`-submodule `Submodule.map` of
`m_B ^ n` under the trace. The pointwise form here is therefore the same as the
submodule or ideal equality `Tr(p_L^n) = p_K^r`. No `Submodule.map` or span is
used in the Lean statement.

## Natural division

`r = (d + n) / e` uses natural-number division, which rounds down. Since
`d + n ≥ 0` and `e > 0`, it equals Serre's `[(m + n)/l]`, the largest integer
at most `(d + n)/e`. Hypothesis 1 rules out Lean's convention `x / 0 = 0`.
Every `n` and `d` is allowed, including `n = 0` (the trace of `B`) and `d = 0`
(the unramified-different case).

## Sources and provenance

The original sources are in Jean-Pierre Serre, *Local Fields*, translated by
Marvin Jay Greenberg, GTM 67, Springer, 1979 (source `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):

- Chapter III §3, printed p.50 / PDF p.57: definition of the codifferent `B*`
  as the largest sub-`B`-module `E` of `L` with `Tr(E) ⊆ A`, and of the
  different as its inverse.
- Chapter III §3, Proposition 7 and its proof, printed pp.50–51 / PDF
  pp.57–58: for fractional ideals `a` of `K` and `b` of `L`,
  `Tr(b) ⊆ a` if and only if `b ⊆ a 𝔇⁻¹`. Printed p.51 notes that this
  property characterizes the different.
- Chapter III §4, Proposition 10, printed p.52 / PDF p.59: the different is
  preserved by completion. This explains why a statement about DVRs, rather
  than complete DVRs, is the natural generality.
- Chapter V §3, Lemma 4 and its proof, printed p.83 / PDF p.90: in a totally
  ramified cyclic extension of prime degree `l` with different `p_L^m`,
  `Tr(p_L^n) = p_K^r` with `r = [(m + n)/l]` for every `n ≥ 0`. Serre proves it
  from Proposition 7 of Chapter III: `Tr(p_L^n) ⊆ p_K^r` if and only if
  `p_L^n ⊆ p_L^{lr - m}`, that is, `r ≤ (m + n)/l`.

The registered author corrections (source `serre-book-corrections-2019`,
*Corrections to J-P. Serre's books*, 2019, SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`), Local
Fields section, PDF pp.2–3, list no correction to printed pp.50–52 or p.83.

This Lean statement is a derived generalization of Lemma 4, not a
transcription. Serre's proof of Lemma 4 combines Proposition 7 of Chapter III
with the shape `p_L^m` of the different and the total-ramification equality
`p_K O_L = p_L^l`, which give `p_K^r 𝔇⁻¹ = p_L^{lr - m}`. None of these steps
needs the Galois group. So the statement replaces:

- the totally ramified cyclic extension of prime degree with an arbitrary
  finite separable extension of fraction fields of DVRs, with `B` the
  integral closure of `A` and finite over `A`;
- Serre's degree `l` (which equals `e` in the totally ramified case) with the
  ramification index `e`, given by the ideal equality of hypothesis 2;
- Serre's exponent `m = (t + 1)(l - 1)` from Lemma 3 with an arbitrary
  exponent `d` of Mathlib's `differentIdeal`, given by hypothesis 3;
- the ideal equality `Tr(p_L^n) = p_K^r` with the pointwise set equality
  described above.

The break-dependent value of the different, Galois structure, completeness and
the p-adic setting are omitted, because the trace-image formula does not use
them. They are supplied separately when the statement is specialized.

## Intended specialization

This statement is a prerequisite for the host target
`Langlands.LocalClassField.PrimeRamifiedTraceIdeals` in
`Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsStatement`. The host
proposition is the case `A = TF.Integers`, `B = TL.Integers`, `K = F.Carrier`,
`L = L.Carrier`, `e = ell` and `d = (t + 1) * (ell - 1)`, at universes
`{u, v, u, v}`. In that case:

- the integer-ring algebra and the two scalar towers are
  `relativeIntegerAlgebra`, `relativeIntegerFieldAlgebra`,
  `relativeIntegerFieldTower` and `relativeIntegerTower` in namespace
  `Langlands.PadicField.TopologicalData`, from
  `Langlands.LocalField.RelativeIntegers`;
- `IsIntegralClosure` and `Module.Finite` come from the accepted statement
  `Langlands.LocalClassField.NYLL.RelativeIntegerStructureStatement` and its
  proof `relativeIntegerStructure`;
- the fraction-ring instances are Mathlib's instances for valuation integers,
  and separability holds because the fields have characteristic zero;
- hypothesis 2 is the small total-ramification ideal-map adapter owned by
  Worker 521;
- hypothesis 3 is the separately stated `PrimeRamifiedDifferent`.

During authoring, a private draft not included in this module derived
`PrimeRamifiedTraceIdeals.{u,v}` from `DVRTraceIdeals.{u,v,u,v}`,
`PrimeRamifiedDifferent.{u,v}` (from its staged candidate), and the adapter in
the shape `Ideal.map (algebraMap TF.Integers TL.Integers) mTF = mTL ^ ell`. It
compiled with no errors. The final step applied this proposition directly, so
the host's coercions and `algebraMap` forms agree. No generic premise of this
proposition remains undischarged in that specialization. This check is
interface evidence only. It is not part of this candidate, and it proves
nothing about the trace formula.

## Authors

The interface was specified by Worker 512, who owns the contract and the
host proof task. It was formalized and documented by Worker 726. Worker 27
reviewed the proposed interface against the host target and Mathlib's
`Different.lean` before formalization and raised no objection. That
coordination is not semantic acceptance of this module. A separate proof task
must establish this proposition.
