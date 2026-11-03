# Compactness of the norm-one idele class group

## Statement

Let `F` be a number field. The norm-one ideles `normOneIdeles F` form the kernel of
the published normalized idelic absolute value
`Langlands.Global.IdeleAbsoluteValue.full F : Ideles F →ₜ* ℝ≥0ˣ`. On an idele `x` this
absolute value is the product over all places of the normalized local absolute values:
`‖x_w‖^{mult w}` at an infinite place `w`, where the multiplicity is 1 at real and 2 at
complex places, and the normalized norm at each finite place. It is therefore the content
`c(a) = ∏_v |a_v|_v` of Milne, and `normOneIdeles F` is Milne's `I¹ = Ker(c)`.
Here `Ideles F` is the unit group of the full adele ring with the units topology. This is
the idelic topology, not the topology induced from the adeles.

`normOnePrincipal F` is the subgroup of `normOneIdeles F` made of the principal ideles
`principalIdeles F`, the range of the diagonal embedding `diagonalUnits F : Fˣ →* Ideles F`.
By the product formula every principal idele has norm one, so this is all of `Fˣ` inside
`I¹`. `NormOneIdeleClasses F` is the quotient group `I¹ / Fˣ`. It carries the quotient
topology of the subspace topology on `I¹`.

`NormOneIdeleClassCompactStatement` is the proposition that, for every number field `F`
in universe `u`, `NormOneIdeleClasses F` is a compact space. The theorem
`normOneIdeleClassCompact` proves it.

The module also proves two forms used downstream:

- `exists_isCompact_fundamentalSet F`: there is a compact set `C` of ideles contained in
  `I¹` such that every norm-one idele `x` has a field unit `a` with
  `diagonalUnits F a * x ∈ C`.
- `isCompact_ker_ideleClass F`: the kernel of the descended absolute value
  `IdeleAbsoluteValue.ideleClass F` on the actual idele class group `IdeleClasses F`
  (that is, the image of `I¹` in `C_F = I / Fˣ`, with its subspace topology) is compact.

## Source

J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, §4, item 4.4, printed
page 171 (PDF page 180). Registered source `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`. Milne defines the
content `c(a) = ∏ |a_v|_v`, sets `I¹ = Ker(c)`, notes that `K^× ⊂ I¹` by the product
formula, and states that `I¹/K^×` is compact. Milne does not prove the compactness at that
point. The Lean statement is the quotient-group form of the claim. The fundamental-set
and idele-class-group forms are derived variants proved in the same module.

## Proof

The proof is internal to this module; it follows the standard route through finiteness of
the class group and Dirichlet's unit theorem.

1. **Compact boxes.** `adeleBox F R` is the set of adeles whose infinite components have
   norm at most `R` and whose finite part lies in the published compact set
   `integralFiniteAdeles F` (`isCompact_integralFiniteAdeles`). It is compact
   (`isCompact_adeleBox`), because every closed ball in an infinite completion is the
   preimage of a closed ball in `ℂ` under the isometric extension embedding
   (`isCompact_closedBall_infiniteCompletion`).
   `ideleBox F R` is the set of ideles `x` with both `x` and `x⁻¹` in `adeleBox F R`. It
   is compact (`isCompact_ideleBox`) because `Units.embedProduct` is a closed embedding
   into the Hausdorff space `Adeles F × (Adeles F)ᵐᵒᵖ`.

2. **Logarithmic bound on the fundamental cone.** `exists_log_normAtPlace_bound` gives a
   constant `D` such that every point `z` of Mathlib's fundamental cone
   `NumberField.mixedEmbedding.fundamentalCone F` satisfies
   `|log normAtPlace w z| ≤ |log N(z)| + D` at every infinite place `w`. Here `N` is the
   mixed-space norm. The proof bounds the coordinates `logMap z` of the fundamental cone
   by the bounded fundamental domain of the unit lattice
   (`ZSpan.fundamentalDomain_isBounded`). It recovers the coordinate at the distinguished
   place `w₀` from the fact that the normalized logarithms
   `mult v · (log normAtPlace v z − log N(z)/[F:ℚ])` sum to zero.

3. **Decomposition through the class group.** `toIntegralQuotient F` maps ideles onto the
   published quotient `IntegralIdeleClassQuotient F = C_F / C∞`, where `C∞` is the image of
   the integral ideles `integralIdeles F`. These are the ideles that are units at every
   finite place. The quotient is finite by the published theorem
   `integralIdeleClassQuotientFinite`. `representative F q` chooses an idele in each class.
   `exists_integral_mul_principal` writes every idele as `x = u · a · r`, with `u` integral,
   `a` principal and `r = representative F (toIntegralQuotient F x)`.

4. **Fundamental set.** Let `x` be a norm-one idele written as in step 3. The archimedean
   part of `u` has nonzero mixed-space norm (`InfiniteAdeleRing.ringEquiv_mixedSpace`).
   Mathlib's `fundamentalCone.exists_unit_smul_mem` therefore gives a unit `ε` of `𝓞 F`
   moving it into the fundamental cone. The idele `u' = ε · u` is still integral, and
   `ε a⁻¹ · x = u' · r`. Since `x` and principal ideles have norm one, `|u'| = |r|⁻¹`. As
   `u'` is a unit at every finite place, `|u'|` is the mixed-space norm of its archimedean
   part. Step 2 then bounds `|log ‖u'_w‖|` at every infinite place by
   `|log |r|| + D`, which depends only on the class `q`. Hence `u'` lies in
   `ideleBox F (R q)` with `R q = exp (|log |representative F q|| + D)`. The set `C` is
   the finite union over `q` of the translates `ideleBox F (R q) · representative F q`,
   intersected with the closed subgroup `I¹`. It is compact and meets every principal
   coset of `I¹` (`exists_isCompact_fundamentalSet`).

5. **Compactness.** The preimage of `C` in the subtype `I¹` is compact because the subtype
   inclusion is an inducing map and `C ⊆ I¹`. Its image under the continuous quotient map
   is all of `I¹ / Fˣ`, since every class contains `diagonalUnits F a * x ∈ C`
   (`compactSpace_normOneIdeleClasses`). The same covering argument shows that the norm-one
   kernel in `IdeleClasses F` is the image of `C` under `ideleClassMap F`
   (`isCompact_ker_ideleClass`).

## Authorship

Worker 1179 wrote the Lean module and this explanation for task `40747bb3` (finite volume of
the norm-one adelic rational quotient). It is the compact-torus input for the multiplicative
group and for the central part of the reductive case.
