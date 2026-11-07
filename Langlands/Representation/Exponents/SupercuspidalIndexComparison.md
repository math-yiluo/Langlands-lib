# Full source intersections at double cosets carrying a Levi conjugacy

This module compares two index sets for Renard VI.5.3(iii). One is the set of
geometric-lemma indices whose source intersection parabolic is full. The other
is the set of double cosets `P(F) \ G(F) / Q(F)` that contain an element
conjugating `L` onto `M`. It proves that they correspond **under the
parabolic-dynamic statement** `ParabolicDynamicStatement` (Milne, Theorem 25.1).
That statement is a hypothesis of the converse direction and of the final
bijection, not a theorem used here. This module does not construct the geometric
gluing and does not prove the final proposition.

For a datum `D : GeometricLemmaIntersectionDatum … z`, the source intersection
parabolic `D.p'` of `M` has range `M ∩ zQz⁻¹` on every test scheme
(`D.parabolic_eq`). Here `inner(g)` is conjugation `x ↦ g x g⁻¹`.

## Dynamic lemmas

`Dynamic.isStable_range_of_comp`: if a cocharacter has the form `χ ≫ q`, then
conjugation by it preserves the range of `q`. The conjugating point itself lies
in that range.

`Dynamic.centralizer_carrier_le_of_conj_mem`: let `G` be separated, `χ` a
cocharacter of `G` and `F` a subgroup functor represented by a closed subgroup
and stable under conjugation by `χ`. Fix a test scheme `T` and a point `a` of
`P(χ)` over `T`. If `a⁻¹ m a ∈ F` for every point `m` of `Z(χ)` over `T`, then
`Z(χ)(T) ⊆ F(T)`. Proof: let `c ∈ Z(χ)` be the limit of `a` (`limitHom`). For
`m ∈ Z(χ)`, the element `a⁻¹ (c m c⁻¹) a` lies in `F` by hypothesis and in
`P(χ)`. Its limit is `c⁻¹ (c m c⁻¹) c = m`, because the limit map is a
homomorphism on `P(χ)` and is the identity on `Z(χ)`. A closed `χ`-stable
subgroup contains the limits of its points
(`HasLimit.mem_of_isClosedSubgroup_of_isStable`), so `m ∈ F`.

## Fullness of the source intersection

`isIso_p'_of_range_le`: if `M ⊆ zQz⁻¹` on every test scheme, then `D.p'` is an
isomorphism. By `D.parabolic_eq` the range of `D.p' ≫ l ≫ p` then contains the
range of `l ≫ p`. The Library lemma
`IsClosedSubgroup.isIso_of_range_le_range_comp` applies to the closed subgroups
`D.p'` and `l ≫ p`.

`isIso_p'_of_dynamicRealization`: let `R : D.DynamicRealization` be a
simultaneous dynamic realization in the datum's common torus, and let `G` be
separated. Suppose `w = a z b` with `a ∈ P(F)` and `b ∈ Q(F)`, and `ψ : L ≅ M`
satisfies `ψ ≫ l ≫ p = lQ ≫ q ≫ inner(w)`, so `w L w⁻¹ = M`. Then `D.p'` is
an isomorphism. Proof: let `χ` be the source cocharacter of `R`, mapped into `G`
through the common torus. That torus map ends with `lQ ≫ q`, so `χ` factors
through `q`. By `R.sourceParabolic` and `R.sourceLevi`,
`z⁻¹ P z = P(χ)` and `z⁻¹ M z = Z(χ)`. The constant point `a₀ = z⁻¹ a z` lies
in `P(χ)`. A point of `Z(χ)` has the form `z⁻¹ y z` with `y ∈ M`, and
`y = w x w⁻¹` for some `x ∈ L` (via `ψ`). Then
`a₀⁻¹ (z⁻¹ y z) a₀ = b x b⁻¹`, which lies in `Q`. The range of `q` is closed
(`q` is parabolic) and `χ`-stable (`Dynamic.isStable_range_of_comp`).
`Dynamic.centralizer_carrier_le_of_conj_mem` therefore gives `Z(χ) ⊆ Q` on
every test scheme, that is `z⁻¹ M z ⊆ Q`, or `M ⊆ zQz⁻¹`.
`isIso_p'_of_range_le` concludes.

`isIso_p'_of_doubleCoset`: assume `ParabolicDynamicStatement` and that `G` is
connected reductive (affine, hence separated). If
`P(F) w Q(F) = P(F) z Q(F)` and `ψ : L ≅ M` satisfies the conjugacy equation
for `w`, then `D.p'` is an isomorphism. Write `z = a w b` with `a ∈ P(F)` and
`b ∈ Q(F)`, so `w = a⁻¹ z b⁻¹`. Then apply the previous lemma to the Library
realization `D.dynamicRealizationOfParabolicDynamic`.

`isIso_p'_iff`: under the same hypotheses, and given some isomorphism
`E : M ≅ L` of the outer Levis, `D.p'` is an isomorphism if and only if the
double coset of `z` contains an element `w` with an isomorphism `ψ : L ≅ M`
satisfying `ψ ≫ l ≫ p = lQ ≫ q ≫ inner(w)`. Forward direction:
`isIso_q'_of_isIso_p'_of_iso E` makes the target intersection full too. The
published `fullLeviConjugacy` `ε : M ≅ L` then satisfies
`ε ≫ lQ ≫ q = l ≫ p ≫ inner(z⁻¹)`. Inverting it gives `ψ = ε⁻¹` with the
required equation for `w = z`. The converse is `isIso_p'_of_doubleCoset`.

## The index bijection

`fullIndexEquiv`: under the same hypotheses, let `c` enumerate
`P(F) \ G(F) / Q(F)` by an index type `I`, with representatives `z i` of `c i`
and intersection data `D i` at `z i`. Then `c` restricts
(`Equiv.subtypeEquiv`) to a bijection from the indices `i` with full source
intersection parabolic `(D i).p'` onto the subtype of double cosets containing
an element `w` with some `ψ : L ≅ M` satisfying
`ψ ≫ l ≫ p = lQ ≫ q ≫ inner(w)`. This subtype is exactly the index type of the
enumeration in `LeviJacquetInductionSupercuspidalFiltrationStatement`.
`fullIndexEquiv_apply_coe` records that a full index goes to its own double
coset `c i`.

## Provenance and scope

This is derived support for Renard 2026, VI.5.3(iii) (printed p.173, PDF
p.179). Renard's proof of VI.5.3(i) keeps only the representatives `w` with
`M ⊆ w·L`. For (iii) he refers to Lemma V.4.6(iii) (printed p.120, PDF p.126),
`W_{L,M} ∩ W(L,M) ≃ W(L,M)/W_L`. Here `M` and `L` are standard, `W_{L,M}` are
the minimal-length representatives of the Weyl double cosets, and
`W(L,M) = {w | w·L = M}` (V.4.3.2, printed p.119, PDF p.125). The Lean route
is different. It works with arbitrary representatives of actual rational double
cosets, and uses a dynamic limit argument for one cocharacter realizing `z⁻¹Pz`,
`z⁻¹Mz` and `Q` at once. No standard form or Weyl-group combinatorics is
needed. The resulting condition, that the double coset contains some `w` with
`w L w⁻¹ = M`, is the one used by the target statement. Renard's condition
`w·L = M` on a standardized representative is a special case of it.

The final target may not assume `ParabolicDynamicStatement`. Using this module
there needs a published proof of that statement (or a dynamic realization
obtained otherwise). The geometric gluing indexed by an enumeration of all
double cosets is also still needed. No irreducibility, finite length or
standardness hypothesis appears.
