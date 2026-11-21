# Integral étaleness of the actual full-residue subfield

The theorem
`Langlands.CentralDivision.localDivisionFullResidueSubfieldEtale.{u, uL}`
proves exactly
`Langlands.CentralDivision.LocalDivisionFullResidueSubfieldEtaleStatement.{u, uL}`.
It covers both universes and arbitrary characteristic, and it adds no
hypothesis. After introducing `K`, `D`, `L`, `ι` and the two premises
(surjectivity of `localDivisionSubfieldResidueMap K D ι` and
`Module.finrank K L = CentralSimple.reducedDegree K D`), the proof shows that
the actual integer ring `B = (localDivisionSubfieldValuation K D ι).integer` is
étale over `𝒪[K]`. It uses the algebra structure
`localDivisionSubfieldIntegerAlgebra K D ι` that appears in the statement. The
proof constructs neither a new valuation nor a new algebra structure. The
statement pair and every pair it imports are unchanged.

## Notation and auxiliary private lemmas

Write `kD` for the actual division residue field
`DivisionValuation.Residue (localReducedNormValuation K D)`. Its field and
`𝓀[K]`-algebra structures are `localDivisionResidueField` and
`localDivisionResidueAlgebra`. The private ring map `subfieldReduction`
(`ρ : B →+* kD`) reduces modulo the strict-value ideal of the restricted
valuation `w`. It then applies the residue inclusion
`localDivisionSubfieldResidueMap K D ι`. The lemma
`subfieldReduction_algebraMap` rewrites `localDivisionSubfieldBaseIntegerMap_reduction`
as `ρ (algebraMap 𝒪[K] B a) = algebraMap 𝓀[K] kD (residue a)`. The lemma
`coe_sum_integer_smul` computes in `L` the coercion of an `𝒪[K]`-linear
combination in `B`.

`integer_coefficients` is the key integrality step. Let `s : I → B` be a finite
family whose reductions `ρ (s i)` are `𝓀[K]`-linearly independent. Suppose
`∑ c i • s i = x` in `L`, with `c i ∈ K` and `x ∈ B`. Then every `c i` is
integral, so `valuation K (c i) ≤ 1`. The proof is by contradiction. If some
coefficient is nonintegral, choose an index `j` at which `valuation K (c j)` is
maximal, so that `valuation K (c j) > 1`. The normalized coefficients
`d k = (c j)⁻¹ * c k` lie in `𝒪[K]`, and `d j = 1`. Put
`y = ∑ d k • s k ∈ B`. Then `y = (c j)⁻¹ • x` in `L`. The restricted valuation
of a base scalar `a` is `valuation K a ^ reducedDegree K D`, by
`localDivisionSubfieldValuation_apply`, `ι.commutes` and
`localReducedNormValuation_algebraMap`. The reduced degree is positive
(`CentralSimple.reducedDegree_pos`). Hence `w y < 1`, and
`DivisionValuation.reduction_eq_zero_iff` gives `ρ y = 0`. Expanding `ρ y` with
`subfieldReduction_algebraMap` gives the relation
`∑ residue (d k) • ρ (s k) = 0`. Its `j`-th coefficient is `1`, which
contradicts the independence hypothesis.

`bijective_adjoinRoot_to_integers` assumes the following. The polynomial
`f : 𝒪[K][X]` is monic and `b ∈ B` is a root of `f`. The powers `b ^ i` for
`i < natDegree f` are `K`-independent in `L`, and their reductions are
`𝓀[K]`-independent. Finally `natDegree f = finrank K L`. Under these
hypotheses the lemma shows that the `𝒪[K]`-algebra map
`ψ = AdjoinRoot.liftAlgHom f (Algebra.ofId 𝒪[K] B) b hb` is bijective. It uses
the monic power basis `AdjoinRoot.powerBasisAux' hf` of `AdjoinRoot f`, whose
`i`-th vector is `root f ^ i`, so `ψ` sends it to `b ^ i`.

- Injectivity: if `ψ a = 0`, then the coordinates of `a` give a `K`-linear
  relation among the powers `b ^ i` in `L`. Hence every coordinate is zero.
- Surjectivity: the `K`-independent powers have cardinality `finrank K L`. By
  `basisOfLinearIndependentOfCardEqFinrank'` they form a `K`-basis of `L`.
  Expand `x ∈ B` in this basis. `integer_coefficients`, applied to the family
  `b ^ i` with independent reductions, shows that the coordinates are integral.
  The corresponding `𝒪[K]`-combination of the power basis maps to `x`.

## Main proof

1. `exists_localDivisionResidue_generator` gives an integral unit whose
   residue `z ∈ kD` generates: every residue element is `0` or a power of `z`.
   `exists_localDivision_residue_minpoly_polynomial` gives a monic
   `f : 𝒪[K][X]` with three properties. Its reduction is `minpoly 𝓀[K] z`, it
   has the same degree, and its image in `K[X]` is irreducible.
2. In `kD`, `z` is a root of the reduction. The base residue field is finite,
   hence perfect, and the residue minimal polynomial is irreducible. It is
   therefore separable, so the reduced derivative does not vanish at `z`.
   `localDivisionSubfield_lift_base_polynomial`, which needs the surjectivity
   premise, then gives a root `b ∈ B` of `f` whose residue
   (`localDivisionSubfieldResidueMap ∘ reduction`) is `z`.
3. By `localDivisionSubfield_aeval_base_polynomial`, `b` is a root in `L` of
   the image of `f` in `K[X]`. That image is monic and irreducible, so it equals
   `minpoly K b` (`minpoly.eq_of_irreducible_of_monic`). The degree chain is
   `natDegree f = natDegree (minpoly 𝓀[K] z) = finrank 𝓀[K] kD = reducedDegree K D = finrank K L`.
   The second equality holds because `z` generates `kD`
   (`localDivisionResidue_adjoin_eq_top` and `PowerBasis.ofAdjoinEqTop`). The
   third is `localDivisionResidue_finrank_eq_reducedDegree`, and the last is
   the degree premise. `linearIndependent_pow` gives the `K`-independence of
   the powers of `b` and the `𝓀[K]`-independence of the powers of `z = ρ b`.
4. `bijective_adjoinRoot_to_integers` turns `ψ` into an `𝒪[K]`-algebra
   isomorphism `e : AdjoinRoot f ≃ₐ[𝒪[K]] B`.
5. By `hom_eval₂` and the scalar compatibility above, the residue of
   `aeval b f'` equals the reduced derivative at `z`, which is nonzero.
   `DivisionValuation.reduction_ne_zero_iff` and
   `DivisionValuation.isUnit_iff_value_eq_one` show that `aeval b f'` is a unit
   of `B`. Its preimage `t = AdjoinRoot.mk f f'` under `e` is therefore a unit
   of `AdjoinRoot f`.
6. The pair `(f, f')` is a Mathlib `StandardEtalePair` over `𝒪[K]`, with
   witness `f' · 1 + f · 0 = f' ^ 1`. Its standard étale ring is étale.
   `StandardEtalePair.equivAwayAdjoinRoot` identifies that ring with
   `Localization.Away t`. Since `t` is a unit, `IsLocalization.atUnit`
   identifies `AdjoinRoot f` with this localization; its scalars are restricted
   to `𝒪[K]`. Composing with `e` gives an `𝒪[K]`-algebra isomorphism from the
   standard étale ring to `B`. `Algebra.Etale.of_equiv` concludes.

## Comparison with the literature

The statement Markdown compares the claim with Serre, *Local Fields*,
Chapter I, §6, Propositions 15–16 (printed pp. 18–19). The implemented proof
follows that route for the actual ring `B`. As in Proposition 16, a lifted
residue generator of full degree gives a monic presentation
`𝒪[K][X]/(f) ≅ B`. As in Proposition 15, the separable reduction makes the
presentation unramified. The Lean proof does not use Serre's results as
assumptions. Its presentation step is the explicit coefficient-normalization
argument above, rather than a discriminant or Nakayama argument. The final
étaleness step goes through Mathlib's standard étale algebras.
