# Proper arithmetic models of a proper field morphism

This unit states the arithmetic model-existence step used in the first
paragraph of Conrad's proof of Proposition 4.4. It concerns actual schemes
and scheme-theoretic properness; it states no topological conclusion.

`AdelicSpreadProperExistenceStatement` is the conjunction of the function-field
and number-field clauses, in arbitrary common universe `u`. Given a proper
morphism `g : Y ⟶ W` over the original field, with `W` separated and of finite
type, and any prescribed finite initial place set `S`, there are:

- A finite set `T` containing `S`.
- Actual models `M` and `N` over the outside-`T` integer ring, whose structure
  morphisms are locally of finite type, quasi-compact and separated.
- Isomorphisms from their actual generic fibres to `Y` and `W`, over the
  original field.
- A proper model morphism `gm : M ⟶ N` whose generic-fibre morphism commutes
  with those isomorphisms and the originally prescribed `g`.

The displayed equality in each Lean clause records this commutative square.
Generic fibres and the morphism between them use `Over.pullback` along the
literal inclusion of the outside-`T` integer ring into the original field.
The statement does not replace the fields or their integer rings by abstract
isomorphic objects. Locally of finite type together with quasi-compactness
expresses finite type. No separate hypotheses on `Y` are necessary: properness
of `g` and the stated properties of `W` imply that `Y` is separated and of
finite type.

The function-field clause uses the actual discrete places of `F` trivial on
`k`, their outside-set integer ring, and the supplied rational-function
action and compatible scalar tower. The constants `k` are perfect and may
be infinite. A `FunctionField k F` is finite dimensional over `RatFunc k`;
separability of that extension is not imposed. The number-field clause
covers every `NumberField K` and uses its actual finite places and
`Set.integer`. The finite index subtype allows the empty initial set.
Archimedean places are implicit in the number-field convention for
outside-set integer rings.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Theorem 3.4(1) on printed page 5 gives existence of models and descent of
morphisms; Theorem 3.4(2) includes separatedness and properness. Remark 3.5
on printed page 6 identifies the actual integer-ring system with colimit
the original field. The first proof paragraph of Proposition 4.4 on printed
page 11 makes precisely this choice of separated finite-type models and
proper model morphism.

This is a derived arithmetic specialization of those passages. Noetherianity
of the actual integer rings converts finite type into finite presentation.
The perfect, possibly infinite constant fields and empty initial levels
extend the paper's global-field and nonempty-set conventions through the
actual integer colimit and Noetherian results. Nonaffine schemes are retained.
The statement does not assume a model for `g`, a spreading theorem, or a
properness-descent conclusion.

Its proof is a separate obligation. Intrinsic adelic properness, compactness,
eventual stabilization and the other results of the five-section parent task
remain separate obligations as well.
