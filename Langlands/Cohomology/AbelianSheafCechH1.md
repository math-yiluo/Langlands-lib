# Finite-cover Čech degree one and actual abelian sheaf cohomology

This module constructs an additive injection from ordered Čech degree-one
cohomology on a finite open cover into actual first abelian sheaf cohomology.
It applies to every topological space `T : TopCat.{u}` and every actual sheaf
`F : TopCat.Sheaf AddCommGrpCat.{u} T`, for arbitrary universe `u`. The index
type `ι : Type w` has an independent universe and is finite. The covering
hypothesis is `⊤ ≤ iSup U`.

The construction is internal. Its inputs are the published ordered Čech complex
and its differential and functoriality in `CechCochains`, the full-cover sheaf
gluing and separation lemmas in `CechRefine`, finite-family flasque exactness
in `CechFlasque`, and the actual injective embedding and flasqueness result in
`AbelianSheafFlasque`. The cohomology and connecting homomorphisms are Mathlib's
actual Ext-defined `CategoryTheory.Sheaf.H` and
`CategoryTheory.Sheaf.H.δ`. No external-source translation is asserted.

`globalCochain P U` restricts a global section to a zero-cochain. Its differential
vanishes. For a sheaf on a full cover, `globalCochain_injective` proves
injectivity and `exists_globalCochain_eq` proves that every zero-cocycle is in
its range. These proofs use only sheaf separation and gluing, reducing
functions from `Fin 1` to constant functions. No finiteness is needed here.

For a short complex `S = (F →ᶦ J →ᵖ Q)`, `Representative z` consists of a
zero-cochain `t` in `J` and a global section `q` in `Q` satisfying
`d t = C(i) z` and `C(p) t = globalCochain q`.
If `J` is flasque and the cover is finite and full, `exists_representative`
constructs a representative for every one-cocycle `z`: finite-family flasque
exactness supplies `t`, and degree-zero gluing supplies `q`.

For a short exact `S`, `Representative.value hS r` is
`δ ((H.equiv₀ Q topTerminal).symm q) ∈ Sheaf.H F 1`. The theorem
`Representative.value_eq_zero_iff` proves

```text
r.value hS = 0 ↔ ∃ a : C F U 0, d a = z.
```

This theorem does not need finiteness or flasqueness, since the representative
is already supplied. In the forward direction, actual cohomological exactness
lifts `q` to a global section `s` of `J`. Every component of
`t - globalCochain s` lies in the kernel of `p`; left exactness on sections
lifts these components to `a`. Injectivity of `i` on sections proves `d a = z`.
In the reverse direction, if `z = d a`, the zero-cocycle `t - C(i) a` glues
to `s`. Separation identifies `p(s)` with `q`, and the zero composite in the
actual long exact sequence makes the connecting class vanish.

Addition and subtraction of representatives preserve the defining equations,
and their values add and subtract. Applying the preceding vanishing criterion
to the difference of two representatives of the same cochain proves
`Representative.value_eq`, independence of the representative.

`cocycles P U` is the kernel subgroup of `d : C¹ → C²`.
`coboundaryHom P U` is `d : C⁰ → cocycles`, using `d² = 0`.
`CechH1 P U` is the quotient of the cocycles by its range. For a finite full
cover and a short exact `S` with flasque middle term, `cocycleClassHom` chooses
representatives and takes their values. Independence and addition prove that
it is an additive homomorphism. `coboundary_range_eq_ker` identifies its kernel
exactly with the coboundaries. Thus `quotientClassHom` descends to `CechH1`
and is injective.

Finally, `comparisonHom F U hcov` specializes to the published actual chosen
injective sequence `F → Injective.under F → cokernel (Injective.ι F)`.
The middle sheaf is flasque by the proved injective flasqueness theorem.
`comparisonHom_injective` proves that this homomorphism is injective.
`comparisonHom_eq_value` computes it using any supplied representative in
this sequence, independently of the auxiliary choice.

No surjectivity for an arbitrary fixed cover is asserted. The module does not
prove that every actual H¹ class is represented on some finite cover, does not
claim naturality in the sheaf or the cover, and does not classify line bundles
or prove the final actual fppf Picard sheaf representability statement.
