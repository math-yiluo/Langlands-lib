# The actual different at a prime ramification break

Worker 231 wrote this Lean/English pair and checked the cited original and the
author corrections. It follows the statement specification that Worker 512
wrote in the objective of TaskHub task `02d82e9d-cb15-42a0-bb98-e31ae97a1246`.
Before publication of that task, Worker 27 reviewed the proposed interfaces and
raised no objection. That interface check is not semantic acceptance of this
module.

The module defines the closed proposition
`Langlands.LocalClassField.PrimeRamifiedDifferent.{u,v}`. It gives a theorem
target and does not prove the different formula. It also proves one
structural helper theorem, described below, that the target needs in order to
elaborate.

## Helper theorem

`Langlands.PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree T S`
applies to supplied p-adic fields `F`, `E` with a compatible
`Algebra F.Carrier E.Carrier` and supplied topological data `T`, `S`. With the
existing scalars `relativeIntegerAlgebra T S` installed, it proves
`Module.IsTorsionFree T.Integers S.Integers`. The proof uses Mathlib's
`Module.isTorsionFree_iff_algebraMap_injective`: the algebra map is
`relativeIntegerMap T S`, the restriction of the injective field map
`algebraMap F.Carrier E.Carrier`, so it is injective. Mathlib's
`differentIdeal` needs this instance. The target derives it from the supplied
data rather than assuming it.

## Quantifiers and hypotheses

The binders and hypotheses are the same as those of the published
`Langlands.LocalClassField.PrimeRamifiedTraceIdeals`. For every natural prime
`p` with `[Fact p.Prime]`, the proposition quantifies over
`F : PadicField.{u} p` and `L : PadicField.{v} p` at independent arbitrary
universe levels. It keeps every supplied instance of
`Algebra F.Carrier L.Carrier`, its compatible
`IsScalarTower (Padic p) F.Carrier L.Carrier`, finite dimensionality and
Galoisness. Write

```text
ell = Module.finrank F.Carrier L.Carrier,
TF = F.canonicalTopologicalData,
TL = L.canonicalTopologicalData.
```

The hypotheses are:

- `Nat.Prime ell`;
- total ramification, stated as
  `TL.ramificationIndex = ell * TF.ramificationIndex` for the canonical
  absolute ramification indices;
- for every natural `t`, the supplied break pattern

  ```text
  ∀ i : Nat, Ramification.Padic.lowerRamificationGroup TL F.Carrier i
    = if i ≤ t then top else bottom.
  ```

`Ramification.Padic.lowerRamificationGroup TL F.Carrier i` is the subgroup of
`L.Carrier ≃ₐ[F.Carrier] L.Carrier` whose elements `σ` satisfy
`σ x - x ∈ (maximalIdeal TL.Integers)^(i+1)` for every `x : TL.Integers`, with
`σ` acting through the actual integer automorphism. This is Serre's `G_i` for
`i ≥ 0` (condition b) of Chapter IV, Lemma 1). The tame case `t = 0` is
included. The break is a hypothesis for each `t`: the target does not choose
`t` or replace it with an existence statement. The hypotheses contain no
different formula, trace containment, trace image, monogenicity, generator of
the integer ring, or norm statement.

## Installed structure

Inside the proposition, these existing data are installed:

- `TF.topology`, `TF.valuativeRel`, `TF.localField` and the same three fields
  of `TL`. These are the canonical structures carried by the supplied
  topological data. `TF.Integers` and `TL.Integers` are by definition the
  valuation integer rings of these valuative relations. With these data,
  Mathlib's `IsNonarchimedeanLocalField` instance makes both integer rings
  discrete valuation rings. Mathlib then infers the instances
  `IsDedekindDomain TL.Integers` (through principal ideal rings) and
  `IsIntegrallyClosed TF.Integers` that `differentIdeal` needs. Without `localField`, `IsDedekindDomain` is not
  found. `IsDomain` holds because the integer rings are subrings of fields.
- `relativeIntegerAlgebra TF TL`. Its algebra map is the restriction of the
  supplied field algebra map to the integer rings, so it is the actual
  relative integer map.
- `relativeIntegerFieldAlgebra (E := L) TF`, with the existing towers
  `relativeIntegerFieldTower (E := L) TF`
  (`IsScalarTower TF.Integers F.Carrier L.Carrier`) and
  `relativeIntegerTower TF TL`
  (`IsScalarTower TF.Integers TL.Integers L.Carrier`). Both towers are
  definitional. They are installed for use in a later proof.
  `differentIdeal` does not refer to them, so they do not change what the
  proposition says.
- `relativeIntegerAlgebra_isTorsionFree TF TL`, the helper theorem above.

The only data that `differentIdeal TF.Integers TL.Integers` depends on are the
two rings and the relative integer algebra. Every other instance it uses
(`IsDomain`, `IsIntegrallyClosed`, `IsDedekindDomain`, `IsTorsionFree`) is a
proposition, so the way it was found does not affect the meaning of the target.

## Conclusion: the actual different

The conclusion is the literal ideal equality

```text
differentIdeal TF.Integers TL.Integers
  = (IsLocalRing.maximalIdeal TL.Integers) ^ ((t + 1) * (ell - 1)).
```

Here `differentIdeal` is Mathlib's definition in
`Mathlib/RingTheory/DedekindDomain/Different.lean`. For `A = TF.Integers` and
`B = TL.Integers`, it is the preimage in `B`, along `B → FractionRing B`, of
the inverse `1 / traceDual A (FractionRing A) 1`. The trace dual of `1`
consists of the `x` in `FractionRing B` such that, for every `b : B`,
`Algebra.trace (FractionRing A) (FractionRing B) (x * b)` lies in the image of
`A`. Here `FractionRing A → FractionRing B` is Mathlib's
`FractionRing.liftAlgebra` extension of the relative integer algebra. So the
different is the inverse of the codifferent, the standard definition. No surrogate
different, trace ideal or exponent certificate is introduced. Mathlib's
comparison lemmas, for example `coeSubmodule_differentIdeal`, describe this
ideal in another fraction field such as `L.Carrier`, under fraction-field and
integral-closure hypotheses. Establishing those hypotheses here is work for
the proof.

The right-hand side is a power of the actual maximal ideal of the canonical
integer ring of `L`. The exponent uses natural-number arithmetic. Since `ell`
is prime, `ell - 1` is the true difference.

## Original source and derived encoding

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`; retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Chapter IV, "Notation and Hypotheses" and §1, printed pp.61–64 /
  PDF pp.68–71. For a Galois extension `L/K` of complete discretely valued
  fields with separable residue extension, Lemma 1 and Proposition 1 define
  the groups `G_i`. Proposition 4 (printed p.64 / PDF p.71) states that
  `v_L(D_{L/K}) = Σ_{s ≠ 1} i_G(s) = Σ_{i ≥ 0} (Card(G_i) - 1)`. The formula
  was checked on an image of PDF p.71, because text extraction drops it.
- Chapter V, §3, printed p.83 / PDF p.90. Here `G` is cyclic of prime order
  `l` and `L/K` is totally ramified. With `t = i(s) - 1` for a generator `s`,
  the groups are `G = G_0 = ... = G_t` and `{1} = G_{t+1} = ...`. Lemma 3
  states that the different is `p_L^m` with `m = (t + 1)(l - 1)`, as a
  consequence of Chapter IV, Proposition 4.

The Lean target is a derived encoding of Lemma 3:

- The cyclic prime-order hypothesis is encoded by prime degree and
  Galoisness. The Galois group then has prime order and is cyclic.
- Total ramification is encoded by comparing the canonical absolute
  ramification indices.
- Serre defines `t` from a generator. Here `t` is given through the full
  lower-group pattern. For a group of prime order the two descriptions agree.
- The residue fields are finite, so Serre's separability assumption on the
  residue extension holds.
- The valuation exponent `m` becomes the ideal equality with the `m`-th power
  of the actual maximal ideal, using Mathlib's `differentIdeal`.

This module does not prove that Mathlib's definition agrees with Serre's
different in this setting, or that Proposition 4 holds for the actual
canonical data. Both belong to the proof of the target.

The registered author corrections, *Corrections to J-P. Serre's books* (2019),
`serre-book-corrections-2019`, retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
were read at PDF pp.2–3. In the *Local Fields* list, the two corrections on
printed p.63 concern Proposition 3 and its proof (`e_{L/K}` should be
`e_{L/K'}`, plus a typographical fix). No correction concerns Proposition 4 on
printed p.64 or Chapter V, §3 on printed p.83.

## Scope

The target states only the different formula. It is a prerequisite for the
published host `Langlands.LocalClassField.PrimeRamifiedTraceIdeals` (Serre V
§3, Lemma 4) and does not assert or assume that statement, a trace-image
formula, monogenicity of the integer extension, or a norm result. Any
monogenicity used in its proof must be proved from these hypotheses or taken
from an independently proved prerequisite. Compilation and declaration
inspection confirm that the module elaborates, that the target returns `Prop`
and that only the standard axioms are used. They do not prove the asserted
arithmetic.
