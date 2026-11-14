# Faithfulness target for the actual rational Tate action at one prime

`Langlands.AbelianScheme.Tate.FieldPrimeRationalFaithfulnessStatement` is an
unproved proposition. For every algebraically closed characteristic-zero field
`Ω : Type u`, actual abelian schemes `A` and `B` over `Spec Ω`, and every
natural prime `p` with `Fact p.Prime`, it asserts injectivity of the existing map

```text
PrimeAdic.rationalHomMap (Over.mk (𝟙 (Spec Ω))) p :
  Rationalization.Hom A B →ₗ[ℚ]
    (PrimeAdic.Rational A (Over.mk (𝟙 (Spec Ω))) p →ₗ[ℚ_[p]]
      PrimeAdic.Rational B (Over.mk (𝟙 (Spec Ω))) p).
```

The declaration retains the arbitrary universe `u` used by the abelian scheme
and Tate constructions. In particular, its specialization to `u = 0` has the
field and scheme universes of the Harris–Taylor consumer.
The identity test object includes all actual `Ω`-valued prime-power torsion
points. Algebraic closedness is a hypothesis on this field; the assertion does
not evaluate only the rational torsion of an arbitrary ground field.
Characteristic zero ensures every prime is different from the characteristic.

The domain is the existing rational Hom space `ℚ ⊗[ℤ] (A ⟶ B)`.
The actual prime Tate module is
`ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral A (Over.mk (𝟙 (Spec Ω))) p`,
where the integral module consists of compatible actual prime-power torsion
points. The imported `RationalPrimeHom` constructs this map by the additive
rationalization lift of the actual prime Tate functor. It is rational-linear
in the homomorphism and p-adic-linear in the vector.
Its `rationalHomMap_ofHom` formula recovers the published
`Langlands.GroupScheme.Tate.PrimeAdic.rationalMap` through
`AbelianScheme.groupHom`. Its pure-tensor, identity and composition laws are
already published. `RationalPrimeIso` adds explicit rational scaling and
evaluation formulas, and the equivalence `PrimeAdic.rationalIso` for a rational
isomorphism. These same constructions occur in the proposition and consequences.

## Original source and exact correspondence

The retained source is J. S. Milne, *Abelian Varieties*, 1986 article in
*Arithmetic Geometry*, author revision January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`. The source file is
`J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`,
SHA-256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Printed pages and one-based PDF pages coincide.

Theorem 12.5 on p.21 says that the integral Hom group of two abelian varieties
is free of finite rank and that, for a prime different from the characteristic,
the natural map
`ℤ_p ⊗[ℤ] Hom(A,B) → Hom_{ℤ_p}(T_p A,T_p B)` is injective with torsion-free
cokernel. Its proof on pp.21–22 uses Lemma 12.6, the divisibility of a
homomorphism detected on its Tate action, then handles simple varieties and
reduces the general case using isogeny decompositions.
Both pages, including the complete proof, were read directly as text and
rendered images.

The Lean proposition is a derived consequence, rather than the literal
statement of Theorem 12.5: it restricts to algebraically closed fields of
characteristic zero and uses rational Hom and the p-adic rational Tate module.
An abelian scheme over the field spectrum is the smooth proper geometrically
connected commutative group scheme in this specialization.
Rational scalar extension of the source injection gives an injective action
of `ℚ_p ⊗[ℤ] Hom(A,B)` on `V_p`; finite freeness of Hom makes the natural
inclusion from `ℚ ⊗[ℤ] Hom(A,B)` injective. Restricting this action gives the
map asserted here. Reversing the source's tensor-factor order uses the canonical
commutativity comparison. The canonical map `T_p → V_p` is injective because
the integral Tate module is torsion-free over `ℤ_p`.
These observations explain the mathematical implication from the source;
this file supplies no Lean proof of that implication or of its required
comparisons. No finite-rank bound or torsion-free cokernel statement is added
to the Lean target.

The complete retained errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25`, file
`J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`,
SHA-256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`,
was read. It explicitly records a correction to the original proof of
Theorem 12.5 and says its listed corrections are incorporated in the author's
corrected version. The cited 2022 PDF is that corrected source.

## Conditional consequences and implementation

All theorems below are in `Langlands.AbelianScheme.Tate.PrimeAdic` and take
`h : FieldPrimeRationalFaithfulnessStatement.{u}` explicitly.
They prove consequences of this target; they do not prove the target itself.

- `rationalEndAction_injective_of_fieldFaithfulness A p h` specializes the target
  to `A = B`. The published rational endomorphism action has definitionally
  the same function as the rational Hom map. Thus equality of its operators
  at this single prime determines equality of the original rational
  endomorphisms.
- `rationalHomMap_eq_id_iff_of_fieldFaithfulness A p h f` compares a rational
  endomorphism with `Rationalization.identity A`. It applies the asserted
  injectivity and the published identity law. Its reverse implication is the
  identity law after substitution.
- `rationalEndAction_eq_one_iff_of_fieldFaithfulness A p h f` gives the same
  detection using the unit of the actual rational endomorphism algebra and
  the unit of the p-adic operator algebra. Its forward proof uses the
  conditional injectivity; its reverse proof uses preservation of the unit.
- `rationalIso_injective_of_fieldFaithfulness p h` treats rational isomorphisms
  between `A` and `B`. It evaluates equality of their induced linear
  equivalences on every vector, applies the asserted Hom-map injectivity
  to their forward rational morphisms, then uses categorical isomorphism
  extensionality.
- `rationalIso_eq_refl_iff_of_fieldFaithfulness p h e` specializes this to
  identity detection for a rational self-isogeny. It uses the conditional
  injectivity of `rationalIso` and its identity law.

In particular, `h Ω B B p` is exactly the one-prime rational endomorphism
injectivity premise in the published Harris–Taylor rigidity reductions. It
identifies a rational self-isogeny with the identity once its actual operator
at the selected prime is the identity. The existing full rational Tate
faithfulness theorem does not supply `h`. This statement makes no finite-order,
polarization, lattice, level-smallness or full rigidity assertion. A focused
proof successor must prove this exact proposition after its publication.
