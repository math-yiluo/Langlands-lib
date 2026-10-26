# Finite étale closure of finite-group invariant algebras

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.invariantAlgebraFiniteEtale` proves
the published proposition `InvariantAlgebraFiniteEtale` from
`Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraStatements`. Its
complete telescope is

```lean
theorem invariantAlgebraFiniteEtale (R A G : Type u)
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A] :
    InvariantAlgebraFiniteEtale R A G
```

Thus the actual Mathlib subalgebra `FixedPoints.subalgebra R A G` is both
module finite and étale over `R`. The two conclusions form one conjunction,
in that order. All parameters of the published statement are retained.

For the proof, form two `R`-algebra maps from `A` to the function algebra
`G → A`. The first sends `a` to the family `g ↦ g • a`, using
`MulSemiringAction.toAlgHom`; the second sends it to the constant family
with value `a`. The private helper `fixedPoints_eq_equalizer` identifies
their equalizer with `FixedPoints.subalgebra R A G`: equality of the two
families is equivalent, by function extensionality, to every `g` fixing `a`.
This helper uses only the ring, algebra and action structures.

Because `G` is finite, Mathlib's finite-product instances make `G → A`
a finite and étale `R`-algebra. Apply the Library theorem
`Langlands.AlgebraicGeometry.FiniteEtale.equalizerAlgebraFiniteEtale` from
`Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraProof` to the two
maps and take its étaleness conclusion. Rewriting by the equality of
subalgebras gives étaleness of the invariant algebra. Its module finiteness
follows separately from the injective inclusion into `A`, via
`Module.Finite.of_injective`, using noetherianity of `R` and finiteness of
`A`. The proof returns these two results together.

This is an internal algebraic reduction of the published target. It uses
the unchanged statement module, the equalizer proof module, and
`Mathlib.RingTheory.Etale.Pi`. The equalizer theorem supplies the
local splitting and descent argument; its paired Markdown documents its
adaptation from NYLL's `Algebra.Etale.equalizer`, originally credited to
Christian Merten. This module imports that theorem and adds the fixed-point
identification and inclusion argument.

The target is the affine-algebra translation of SGA 1, Exposé V,
Corollary 3.4, printed p.97 / one-based PDF p.113, using the affine invariant
quotient description in Proposition 1.1 and Corollary 1.8, printed
pp.88 and 90 / PDF pp.104 and 106. Proposition 3.1 and Corollary 3.2,
printed p.96 / PDF p.112, provide the related étale-quotient context.
The registered original is `sga1-arxiv-math-0206203v2`, Grothendieck et al.,
*Revêtements étales et groupe fondamental*, recomposed edition,
SHA256 `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
The implemented proof uses the equalizer argument above.

The result permits disconnected bases, zero rings and arbitrary finite
group actions. It imposes no freeness, faithfulness or invertibility of
the group order. It introduces no replacement invariant object or
additional conclusion hypothesis, and does not use a geometric quotient
or Galois-category theorem.
