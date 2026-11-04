# Proper maps on actual generic-fibre adelic points

`Langlands.Global.AdelicSpreadProperMapStatement` is the conjunction of the
function-field and number-field forms of the proper-map assertion of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.11, Proposition 4.4. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

In each clause, `g : Y ⟶ W` is an actual proper morphism of schemes over the
original global field, and `W` is separated. Independently supplied finite-type
arithmetic spreads `X` and `Z`, at possibly different finite levels `S` and `U`,
come with actual original-field generic-fibre isomorphisms to `Y` and `W`.
The induced map on actual full-adele points, `p ↦ p ≫ g`, is `IsProperMap`
for the two topologies attached to those supplied spreads. This is Mathlib's
proper-map predicate, including continuity and the properness condition.

The point carriers are actual `RingPoint`s into `Y` and `W`, over the original
field and the actual adele ring. The topologies are the transported final
topologies of the fixed-model finite-level point systems, as defined in
`AdelicGenericFiberPoints`; no affine presentation or abstract place system is
assumed. All infinite completions are included in the number-field adele ring.
The function-field clause has finite constants, the specified rational-function
algebra action and compatible scalar tower, and a `FunctionField` instance.
Both clauses have an arbitrary common universe and permit empty finite levels.

The source assumes that both field schemes are separated and of finite type.
The Lean premises are equivalent in this setting: the supplied target spread
makes `W` finite type, and properness of `g` then implies finite type and
separatedness of `Y`. The source spread also supplies finite type of `Y`.
Neither supplied arithmetic spread must initially be separated. This formulation
uses topology independence and the existence of proper separated arithmetic
model morphisms after enlargement (Conrad, printed pp.5–6, Theorem 3.4(1)–(3),
Remark 3.5, and the first paragraph of the proof of Proposition 4.4).

This unit states the proper-map conclusion. Compactness for proper field schemes
and stabilization at sufficiently large finite levels are separate consequences.
