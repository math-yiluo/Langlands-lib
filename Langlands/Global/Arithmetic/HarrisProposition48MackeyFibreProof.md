# The fibres of the prime-orbit Mackey index in Harris's Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48MackeyFibreProof`.

`proposition48MackeyFibre` proves `Proposition48MackeyFibreStatement.{uF}`
(module `Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement`)
for an arbitrary local-field universe `uF`, with the hypotheses as stated there
and no other premise.

## Source

Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134, 177–210 (registered source
`harris-1998-local-langlands`), proof of Proposition 4.8, printed p.203,
`math_9611226v1.tex` lines 1646–1649: "If `A_{t-1}` has `q` elements then it is
a principal homogeneous space under `Gal(E_{t-1}/E)`." Harris uses this without
proof. The statement makes it precise: the double cosets are then the fibres of
restriction to `D = E_{t-1}`, and `D ⊆ E'`. The finite-group argument below is
the one the statement's Markdown sketches.

## Notation

`Q` is a problem with fields `E ⊆ E' ⊆ L`, `G = Gal(L/E)`, `D` an intermediate
field of `L/E`, `H = D.fixingSubgroup = Gal(L/D)` and
`K = (Q.conjugateField 1).fixingSubgroup`, the subgroup fixing the copy of `E'`
in `L`. `Q.MackeyIndex D` is `DoubleCoset.Quotient H K`, the double cosets
`H \ G / K`.

## The implemented proof

1. *Galois setting.* `IsNormalClosure.normal` gives `Normal E L`; separability
   is automatic in characteristic zero, so `L/E` is Galois. The first clause of
   `IsPrimeCyclicStep` makes `D/E` Galois, so `H` is normal in `G`
   (`IsGalois.fixingSubgroup_normal_of_isGalois`).
2. *Cosets of `H` lie in double cosets.* If `a⁻¹ * b ∈ H`, then
   `b = (b * a⁻¹) * a * 1` and `b * a⁻¹ = a * (a⁻¹ * b) * a⁻¹ ∈ H` by
   normality, so `a` and `b` have the same double coset (`DoubleCoset.eq`).
   Hence `a ↦ DoubleCoset.mk H K a` descends to a map
   `f : G ⧸ H → Q.MackeyIndex D`, which is surjective because every double coset
   is the class of an element.
3. *Counting.* `IntermediateField.finrank_eq_fixingSubgroup_index` gives
   `Nat.card (G ⧸ H) = H.index = [D : E]`. With the hypothesis
   `Nat.card (Q.MackeyIndex D) = [D : E]`, the surjection `f` between finite
   types of the same cardinality is a bijection
   (`Function.Surjective.bijective_of_nat_card_le`), so `f` is injective.
4. *`K ≤ H`.* For `k ∈ K`, `1 = 1 * k * k⁻¹` with `k⁻¹ ∈ K` puts `k` and `1`
   in the same double coset, so `f k = f 1`; injectivity gives `k ∈ H`
   (`QuotientGroup.eq_one_iff`).
5. *`D ≤ Q.conjugateField 1`.* By the Galois correspondence for the finite
   Galois extension `L/E`, `IsGalois.fixedField_fixingSubgroup` rewrites both
   fields as fixed fields of their fixing subgroups, and
   `IntermediateField.fixedField_le` turns `K ≤ H` into
   `fixedField H ≤ fixedField K`, that is `D ≤ Q.conjugateField 1`.
6. *Fibres.* If `b = h * a * k` with `h ∈ H`, `k ∈ K`, then
   `a⁻¹ * b = (a⁻¹ * h * a) * k` lies in `H`, by normality and `K ≤ H`. So
   `a⁻¹ * b` fixes every `x ∈ D` (`IntermediateField.mem_fixingSubgroup_iff`),
   and applying `a` gives `a x = b x`. Conversely, if `a x = b x` for all
   `x ∈ D`, then `(a⁻¹ * b) x = a⁻¹ (a x) = x`, so `a⁻¹ * b ∈ H`, and step 2
   gives equal double cosets. This direction does not use `D ⊆ E'`.

Group identities are discharged by the `group` tactic. Multiplication in
`L ≃ₐ[E] L` is composition (`AlgEquiv.mul_apply`) and the inverse is
`AlgEquiv.symm` (`AlgEquiv.aut_inv`).
