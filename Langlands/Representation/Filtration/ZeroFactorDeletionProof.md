# Deleting prescribed zero factors from an actual representation filtration: proof

Author: Worker 250. Provenance: internal algebra.

The theorem `Langlands.ObjectRepFiltration.zeroFactorDeletionTheorem.{uR,uG,uV}`
has exactly the published type
`Langlands.ObjectRepFiltration.ZeroFactorDeletionTheorem.{uR,uG,uV}` from
`Langlands.Representation.Filtration.ZeroFactorDeletionStatement`. That module
is the sole import, and it is not changed.

The theorem therefore holds for every commutative ring `R`, monoid `G`,
representation `A : Rep R G`, length `m`, filtration
`s : ObjectRepFiltration A m` and predicate `P : Fin m → Prop`. The only
hypothesis is that `s.gradedRepresentation i` has a subsingleton carrier
whenever `¬ P i`. The theorem gives `r`, an equivalence
`e : Fin r ≃ {i : Fin m // P i}`, a filtration `t : ObjectRepFiltration A r`
of the same `A`, and, for every `j`, an actual `Representation.Equiv` from
`(t.gradedRepresentation j).ρ` to `(s.gradedRepresentation (e j).val).ρ`.
The proof does not use decidability of `P`, a field, finite length, or
splitting. It does not assume that selected factors are nonzero. Selected zero
factors are kept, and the cases `m = 0` and of an empty selected set are covered.
The three universes stay independent.

## Implemented proof

**Combinatorial core.** `exists_chain_deletion` is a statement about an
arbitrary type `L`. Let `f : Fin (m + 1) → L` satisfy
`f i.castSucc = f i.succ` whenever `¬ P i`. Then there are `r`,
`e : Fin r ≃ {i : Fin m // P i}` and `g : Fin (r + 1) → L` with
`g 0 = f 0` and `g (Fin.last r) = f (Fin.last m)`. In addition, for every `j`,
`g j.castSucc = f (e j).val.castSucc` and `g j.succ = f (e j).val.succ`.
The proof is by recursion on `m`.

- For `m = 0`, take `r = 0`, the equivalence between empty types and `g = f`.
- For `m + 1`, apply the recursion to `Fin.tail f` with the shifted predicate
  `fun i => P i.succ`. Its hypothesis is `hf i.succ`, up to the definitional
  equality `i.castSucc.succ = i.succ.castSucc`.
  - If `P 0` holds, the new chain is `Fin.cons (f 0) g` of length `r + 1`.
    Its index equivalence is `consSelectedEquiv`, which sends `0` to the
    selected index `0` and `k.succ` to `(e k).val.succ`. Its inverse is defined
    by cases on whether the index value is `0`.
  - If `P 0` fails, then `f 0 = f 1`. The chain `g` is kept, and the
    equivalence is composed with `succSelectedEquiv`. This equivalence shifts
    `{i : Fin m // P i.succ}` onto `{i : Fin (m + 1) // P i}`, with inverse
    `Fin.pred`. Here `¬ P 0` excludes the index `0`.

  In both cases the endpoint and matching equations are the recursive ones up to
  definitional unfolding. The one exception is `g 0 = f 0` in the second case,
  which also uses `f 0 = f 1`.

**Zero quotients.** In `subrepresentation_castSucc_eq_succ`, the carrier of
`s.gradedRepresentation i` is by definition the quotient of the upper invariant
submodule `s.subrepresentation i.succ` by the comap of the lower one along its
inclusion. By `Submodule.Quotient.subsingleton_iff`, a subsingleton quotient
makes this comap `⊤`. By `Submodule.comap_subtype_eq_top`, the upper submodule
is then contained in the lower one. Monotonicity of the filtration gives the
reverse inclusion. Hence each unselected index satisfies the hypothesis of the
combinatorial core.

**Equivalent quotients.** The helper `stepQuotient S T` is the actual quotient
object `quotientObj` of the constant-functor subfunctors
`objectRepresentationSubfunctor A S` and `objectRepresentationSubfunctor A T`
at the single object. Every graded quotient of an `ObjectRepFiltration` is
definitionally `stepQuotient` of its lower and upper invariant subspaces. In
`nonempty_equiv_gradedRepresentation`, two graded quotients are compared by
restating both in this form. The two equalities of invariant subspaces are then
rewritten, and `Representation.Equiv.refl` is used.

**Main theorem.** The core is applied to `f = s.subrepresentation`. The
resulting `g` is monotone by `Fin.monotone_iff_le_succ`: each step
`g j.castSucc ≤ g j.succ` rewrites to
`s.subrepresentation (e j).val.castSucc ≤ s.subrepresentation (e j).val.succ`.
Its endpoints are `s.subrepresentation 0 = ⊥` and
`s.subrepresentation (Fin.last m) = ⊤`. So
`t = ObjectRepFiltration.ofSubrepresentations g ...` is a filtration of the
same `A`, and `t.subrepresentation = g` definitionally. The matching equations
then give the required `Representation.Equiv` for each `j` through
`nonempty_equiv_gradedRepresentation`.

Kernel inspection of the theorem reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Reused definitions and provenance

The proof reuses the Library's `ObjectRepFiltration`, `subrepresentation`,
`gradedRepresentation`, `ofSubrepresentations`,
`objectRepresentationSubfunctor` and `RepSubfunctor.quotientObj`, from
`Langlands.Representation.Filtration.ObjectDefinitions` and
`Langlands.Representation.Filtration.Definitions`. It redefines no filtration,
quotient or equivalence. The argument is the elementary one given in the
statement's Markdown: a zero successive quotient makes its two adjacent
submodules equal, so the step can be deleted. It is internal algebra with no
external source and uses no geometric lemma. It was checked with Lean 4.34.0
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
