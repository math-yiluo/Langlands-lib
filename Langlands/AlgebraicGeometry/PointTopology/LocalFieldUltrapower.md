# Ultrapowers of locally compact fields and their convergent germs

This helper module supplies the algebraic objects that feed Mathlib's valuative
criterion (`ValuativeCommSq`, `UniversallyClosed.eq_valuativeCriterion`) in the
proof of `Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProperties`.
For an ultrafilter `𝒰` on a type `I`, the ultrapower `K^I / 𝒰` is a field. The
germs that converge along `𝒰` form a valuation subring of it. The limit map is a
`K`-algebra map from that subring back to `K`. The only topological input is
`exists_isCompact_mem_or_inv_mem` from `LocalFieldInverseBound`.

Throughout, `K : Type u` is a field and `I : Type u`, `𝒰 : Ultrafilter I`. From
`convergentGerms` on, `K` also carries a topology with `IsTopologicalDivisionRing K`,
`T2Space K` and `LocallyCompactSpace K`, and `hnd : ¬ DiscreteTopology K`.

## Dichotomy along an ultrafilter

`ultrafilter_tendsto_or_tendsto_inv_zero hnd 𝒰 g`: for every `g : I → K`, either
`g` converges along `𝒰` to some `c`, or `i ↦ (g i)⁻¹` tends to `0` along `𝒰`.
(Here `I` may lie in any universe.)

Proof as implemented. Take the compact `C` with `x ∈ C ∨ x⁻¹ ∈ C` for all `x`. If
`g i ∈ C` for `𝒰`-almost all `i`, the image ultrafilter `𝒰.map g` contains `C`,
so it converges by `IsCompact.ultrafilter_le_nhds`. Otherwise, since `𝒰` is an
ultrafilter, `g i ∉ C` almost everywhere, hence `(g i)⁻¹ ∈ C` almost everywhere,
and the same argument gives a limit `c` of `(g i)⁻¹`. If `c = 0` we are in the
second case. If `c ≠ 0`, continuity of inversion at `c` shows that `g` tends to
`c⁻¹`.

## The ultrapower field

- `UltrapowerField K 𝒰` is an `abbrev` for the germ type `(𝒰 : Filter I).Germ K`.
  Mathlib (`Mathlib.Order.Filter.FilterProduct`) makes it a field.
- `ultrapowerAlgebra : Algebra K (UltrapowerField K 𝒰)` is built by
  `Algebra.ofModule` from Mathlib's module structure on germs. Its scalar action is
  therefore the existing pointwise action on germs, so there is no instance
  diamond. The two compatibility conditions are checked on representatives with
  `Germ.inductionOn₂`, `Germ.coe_smul`, `Germ.coe_mul`, `smul_mul_assoc` and
  `mul_smul_comm`.
- `ultrapowerMap K 𝒰 : (I → K) →ₐ[K] UltrapowerField K 𝒰` is `Germ.coeRingHom`,
  made `K`-linear by `Germ.coe_smul` through `AlgHom.mk'`.
  `ultrapowerMap_apply` (simp, `rfl`) says it sends `f` to its germ.
- `ultrapowerMap_surjective`: every element is the germ of a family.
- `ultrapowerMap_eq_iff`: two families have the same image iff they agree
  `𝒰`-almost everywhere (`Germ.coe_eq`).
- `eventually_ne_zero_of_ultrapowerMap_ne_zero`: if the image of `f` is nonzero,
  then `f i ≠ 0` for `𝒰`-almost all `i`. Otherwise, because `𝒰` is an
  ultrafilter, `f i = 0` almost everywhere, so the image is `0`.
- `algebraMap_ultrapowerField_apply`: `algebraMap K _ r` is the image of the
  constant family `fun _ => r`. This follows from `AlgHom.commutes` for
  `ultrapowerMap`.

## Convergent germs

`convergentGerms K 𝒰 hnd : ValuationSubring (UltrapowerField K 𝒰)` has carrier
`{x | ∃ c, x.Tendsto (𝓝 c)}`, using Mathlib's `Filter.Germ.Tendsto`. On a germ
`↑f` this is `∃ c, Tendsto f 𝒰 (𝓝 c)`, by `Germ.coe_tendsto`.
`mem_convergentGerms_iff'` (any element) and `mem_convergentGerms_iff K 𝒰 hnd`
(images under `ultrapowerMap`) both hold by `Iff.rfl`. The subring axioms hold
because constants converge and limits are compatible with `+`, `*` and `-`.
They are checked on representatives with `Germ.inductionOn`. The valuation axiom
`x ∈ O ∨ x⁻¹ ∈ O` is the dichotomy above applied to a representative `f` of `x`.
In the second case `x⁻¹` is the germ of `i ↦ (f i)⁻¹`, which tends to `0`. Being a
valuation subring, `convergentGerms` carries Mathlib's instances `ValuationRing`,
`IsLocalRing`, `Algebra (convergentGerms …) (UltrapowerField K 𝒰)` and
`IsFractionRing (convergentGerms …) (UltrapowerField K 𝒰)`.

- `convergentGermsAlgebra : Algebra K (convergentGerms K 𝒰 hnd)` is the
  restriction (`RingHom.codRestrict`) of `algebraMap K (UltrapowerField K 𝒰)`,
  whose values are germs of constant families.
- `convergentGerms_isScalarTower : IsScalarTower K (convergentGerms K 𝒰 hnd)
  (UltrapowerField K 𝒰)` holds because both algebra maps agree definitionally
  (`IsScalarTower.of_algebraMap_eq`).

## The standard part

- `germLimit a` is a chosen limit (`Classical.choose`) of the convergent germ `a`.
  `germ_tendsto_germLimit` says the germ tends to it. Limits are unique because
  `K` is Hausdorff and `𝒰` is a proper filter (`germ_tendsto_nhds_unique`,
  `germLimit_eq_of_tendsto`).
- `germ_tendsto_add`, `germ_tendsto_mul`: limits of germs are additive and
  multiplicative.
- `standardPart K 𝒰 hnd : convergentGerms K 𝒰 hnd →ₐ[K] K` has underlying function
  `germLimit` (`standardPart_apply`). Each homomorphism law follows from
  uniqueness of limits: the limit of `1`, `0` or a constant `r` is that constant,
  and the limit of a sum or product is the sum or product of the limits.
- `tendsto_standardPart K 𝒰 hnd a h`: if `(a : UltrapowerField K 𝒰) = ultrapowerMap K 𝒰 f`,
  then `f` tends to `standardPart K 𝒰 hnd a` along `𝒰`.
  `standardPart_eq_of_tendsto` is the converse uniqueness statement.

The construction is the standard nonstandard-analysis picture of a locally
compact field: the finite (here convergent) elements of an ultrapower form a
valuation ring with standard part map. It is internal to the proof route chosen
for the target and is not taken from Conrad's paper. Conrad's Proposition 4.4
instead reduces to projective space via Chow's lemma.
