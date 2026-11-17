# Residue degree and different exponent

This module introduces two predicates in `Langlands.BaseChange`, using the existing
valuation rings, residue fields, trace, and uniformizer predicate. It does not
choose either invariant or assert its existence.

For fields `F` and `E` equipped with independent `ValuativeRel` instances,
`IsResidueDegree F E f` means that the cardinality of the residue field of `E`
equals the cardinality of the residue field of `F` raised to `f`. The cardinalities
are `Nat.card`, which returns zero for infinite types. No algebra structure,
topology, finiteness, or compatibility between the two valuations is assumed in
this definition. For a finite extension of nonarchimedean local fields with their
usual valuations, it characterizes the usual residue degree.

For the same fields with an `F`-algebra structure on `E`,
`IsDifferentExponent F E d` means that there is a unit `ϖ` satisfying
`GeneralLinear.Iwasawa.IsUniformizingElement (ValuativeRel.valuation E) ϖ` such that,
for every `x : E`, the following conditions are equivalent:

- `Tr_{E/F}(x y)` belongs to the valuation ring of `F` for every `y` in the
  valuation ring of `E`;
- `x ϖ^d` belongs to the valuation ring of `E`.

Thus the trace codifferent is `ϖ^(-d) 𝒪_E`. In the finite separable local-field
setting its inverse, the different, is `𝔭_E^d`. This is Serre, *Local Fields*
(1979), Chapter III, §3, printed p. 50 (PDF p. 57), the definition of the
codifferent and different before Proposition 6; literature ID
`serre-1979-local-fields`. The Lean predicate is deliberately more general than
that setting and makes no separate existence or nondegeneracy assertion. The
uniformizer condition is the Library's existing condition that `v ϖ < 1` and
every nonzero element has valuation an integral power of `v ϖ`.

`IsResidueDegree.unique` proves uniqueness of `f` when `F` is a nonarchimedean
local field. Only `F` has topology and local-field hypotheses; `E` is any field
with `ValuativeRel`. The proof uses the finite residue field of `F`, its
cardinality strictly greater than one (`Finite.one_lt_card`), and injectivity
of natural powers with that base (`Nat.pow_right_injective`).
`isResidueDegree_self` proves `IsResidueDegree F F 1` for every field with
`ValuativeRel`, by the first-power identity.

`IsDifferentExponent.unique` proves uniqueness of `d` for arbitrary fields as
in its definition, without topology or local-field hypotheses. The supplied
uniformizers already provide all the discreteness needed. The proof first
shows that any two such uniformizers have the same valuation: each is an
integral power of the other in valuation, the exponent is positive because its
value is less than one, and the integer-power function is decreasing. Hence
each uniformizer's value is at most the other's. Applying the two codifferent
characterizations to the inverse `d`-th power of the first uniformizer gives
`d ≤ d'`; reversing their roles gives `d' ≤ d`. The proof uses the strict
decrease of powers of a positive value less than one. These uniqueness and
self-degree lemmas are internal consequences of the displayed definitions,
rather than additional theorems attributed to Serre.

For every finite extension of nonarchimedean local fields with compatible
topologies, the residue degree exists. Existence of the different exponent
requires separability: for a finite separable extension, the trace pairing is
nondegenerate and its codifferent is a nonzero fractional ideal, hence a power
of a uniformizer. This is the setting of Serre, Chapter III, §3, and it applies
automatically in characteristic zero. These mathematical existence facts
explain the intended use; this module proves only the stated uniqueness and
self-degree lemmas. Separability is not needed for those uniqueness proofs.
In the later conductor statement, `IsModuleTopology F E` provides the topology
of the extension induced from `F`. A local field's valuation ring consists of
its power-bounded elements and is determined by that topology, giving the
usual inclusion `𝒪_F ⊆ 𝒪_E`. Neither predicate silently adds such a compatibility
hypothesis at its general field scope.
