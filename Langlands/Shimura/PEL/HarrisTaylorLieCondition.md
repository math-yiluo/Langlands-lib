# Harris–Taylor central Lie traces and prescribed relative dimension

This module defines the central trace test in Harris–Taylor, *The Geometry
and Cohomology of Some Simple Shimura Varieties* (2001), III.1,
Lemma III.1.2(3), printed p.90 / PDF p.98. It uses the actual rational
endomorphism action on the actual relative Lie sheaf. It also defines the
prescribed geometric dimension appearing immediately before that lemma
and in the moduli problem on printed pp.89 and 91 / PDF pp.97 and 99.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The source's imaginary quadratic field `E` is called `L` here, its totally
real field `F⁺` is called `E`, and its CM field `F` is called `K`.
The running assumptions on printed p.51 / PDF p.59 include
`F = E.F⁺`, `[F⁺ : ℚ] = d`, and a central division algebra of dimension
`n²` over `F`. The source assumes `n > 0`. The elementary formula and
its laws below are defined also for `n = 0`, arbitrary CM number fields
`L` and `K` with an `L`-algebra structure on `K`, and arbitrary rational
algebras acting on an abelian scheme. Those generalities do not supply
the source's additional arithmetic, faithfulness or signature assumptions.

All declarations are in `Langlands.Shimura.HarrisTaylor`.

## Arithmetic trace and actual scalar sections

`lieTraceValue L K n a` is the element of `K`

```text
algebraMap L K (conj_L (Tr_{K/L}(n² a))) + n a - conj_K(n a).
```

Both conjugations are Mathlib's actual CM complex conjugations, and the
trace is `Algebra.trace L K`. This is the right-hand side of
Lemma III.1.2(3), with the source's natural embedding of its imaginary
quadratic field into its CM field written explicitly. The module proves
its zero and addition laws by additivity of trace and conjugation.
`lieTraceValue_one` computes its value at `1` as `[K : L] n²`, using
the field trace of an algebra-map scalar.

`finrank_imaginary_eq_totallyReal` proves `[K : L] = [E : ℚ]`
when `L/ℚ` and `K/E` are quadratic extensions and the indicated rational
algebra towers commute. It compares the two degree-tower formulas and
cancels `2`. This degree calculation does not prove a compositum theorem
or the source's compatibility equivalence.

For an actual structure morphism `s : S ⟶ Spec K`,
`lieTraceSection L s n a U` applies the actual induced homomorphism
`secHom s U` to this element. `lieTraceSection_restrict` proves its
compatibility with every actual arrow between smaller opens.
`lieTraceSection_pullbackLE` proves its compatibility with
`f.appLE U W h` for an arbitrary scheme morphism `f : T ⟶ S`.
These proofs use the established `secHom_map` and
`secHom_comp_appLE` identities. This pullback result concerns the
prescribed scalar section.

## The central Lie trace test

Given a ring `A` with rational and `K`-algebra structures, an actual
abelian scheme `B/S`, and an actual algebra homomorphism
`i : A →ₐ[ℚ] End0 B`, `centralAction B i` is the composite ring map
`K → A → End0 B`. The `K`-algebra structure supplies the central scalar
map. The definition and the laws in this module do not need an additional
commuting-tower hypothesis for `A`.

For an actual finite free chart
`e : free J ≅ B.Lie.over U`, an element `a : K`, and a smaller open
`V : Over U`, `CentralLieTraceConditionAt` requires equality between

- `lieRationalSectionTrace s B (centralAction B i) e a V`, the trace
  constructed from the actual rational Lie endomorphism on actual
  sections; and
- `lieTraceSection L s n a V.left`, the scalar section above.

`CentralLieTraceCondition` requires this identity for every open, every
finite chart, every central element, and every smaller open. The existing
trace construction is independent of the chosen finite chart.
`centralLieTraceConditionAt_restrict` proves preservation under actual
restriction using the two trace-restriction identities.

`centralLieTraceConditionAt_iso` proves equivalence of the test in any
two finite charts under an actual rational isomorphism of abelian schemes
intertwining the two `A` actions. Its proof applies the previously
constructed rational Lie trace invariance to the central scalar
`algebraMap K A a`. `centralLieTraceCondition_iso` proves equivalence
of the all-chart conditions by transporting charts through the actual
`lieLocalIso0`. The rational isomorphism includes a rational inverse;
the result does not assume a separate Lie isomorphism or trace identity.

`centralLieTraceConditionAt_one` specializes the identity to `a = 1`.
It obtains

```text
card J = [K : L] n²
```

in the actual section ring. It is a ring-valued equality; the module does
not cancel natural-number casts in an arbitrary ring or infer geometric
dimension from that equality.

## Prescribed geometric dimension

`PrescribedRelativeDimension E B n` is the actual predicate
`B.HasRelativeDimension ([E : ℚ] * n²)`, namely
`SmoothOfRelativeDimension` for `B.X.hom`. Here the definition works
for any number field `E`; a Harris specialization supplies the totally
real field and the remaining arithmetic data.

`prescribedRelativeDimension_baseChange` proves preservation under every
actual scheme base change, using the existing abelian-scheme base-change
theorem. `prescribedRelativeDimension_lieRank` applies the published
`lieLocalFreenessRank` proof to obtain that rank for the actual Lie sheaf.
Thus the geometric dimension supplies genuine finite local charts of
the indicated rank; the trace test is imposed on those actual modules.

`NumericalCondition` is the conjunction of this geometric
dimension predicate and the all-chart central trace test. The arithmetic
trace formula is imposed as a condition, not proved for arbitrary actions.

## Provenance and scope

The formula and prescribed dimension are translated from the original
Harris–Taylor passages. The sectionwise formulation and its intrinsic
laws are derived from the existing structure maps, rational Lie action,
finite section traces and Lie rank theorem. They construct reusable
prerequisites for the Harris PEL problem rather than store arbitrary
trace outputs.

The source's original compatibility condition uses the rank and scalar
action on `Lie⁺`, and Lemma III.1.2 proves equivalence under its running
arithmetic and geometric hypotheses. This module does not construct
`Lie⁺` or prove that equivalence. It also does not prove arbitrary
base-change invariance of the actual Lie trace condition, invariance of
geometric relative dimension under rational isomorphism, nonemptiness of
the moduli problem, or representability. Those results remain distinct
obligations; the definition `NumericalCondition` is not asserted to be the
full Harris PEL compatibility condition.
