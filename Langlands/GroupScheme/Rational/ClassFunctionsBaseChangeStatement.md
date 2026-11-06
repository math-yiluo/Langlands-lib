# Field base change for the canonical regular-class-function quotient

Author: Worker 1744.

This module defines the proposition
`Langlands.GroupScheme.ClassFunctions.FieldBaseChangeStatement.{u}`.
It states a comparison for the published actual class-function construction;
it does not prove that proposition.

## Full statement and scope

Fix any universe `u`, fields `K F : Type u`, an instance `[Algebra K F]`,
and a group scheme `G` over `Spec (CommRingCat.of K)`. The sole geometric
hypothesis is `[IsAffineHom G.X.hom]`. Set

```lean
b = Spec.map (CommRingCat.ofHom (algebraMap K F))
GF = (GroupScheme.baseChange b).obj G
```

Affineness of `GF.X.hom` is derived inside the proposition: that structure
morphism is the second projection of the pullback of `G.X.hom` along `b`,
so the existing stability of affine morphisms under base change applies.
It is not an additional quantified premise.

All names below except the explicitly qualified APIs are in
`Langlands.GroupScheme.ClassFunctions`. The proposition asserts that there
exist, simultaneously,

```lean
e : (F ⊗[K] Coord G) ≃ₐ[F] Coord GF
phi : (F ⊗[K] algebra G) ≃ₐ[F] algebra GF
alpha : (Over.pullback b).obj (quotient G) ≅ quotient GF
```

satisfying the following four equations:

```lean
Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Descent.TensorCoordinates.baseChangeIso K F (Coord G) G.X
      (Lie.coordinateIso G)).hom =
  (Lie.coordinateIso GF).hom.left

e.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id F F) (inclusion G)) =
  (inclusion GF).comp phi.toAlgHom

alpha.hom.left =
  (HopfMorphismBaseChange.tensorSpecIso K F (algebra G)).hom ≫
    Spec.map (CommRingCat.ofHom phi.symm.toRingHom)

(Over.pullback b).map (rho G) ≫ alpha.hom = rho GF
```

The existential quantifiers and conjunction of these four equations are
the entire conclusion. Neither a comparison map nor any desired compatibility
is assumed. The fields may be finite or imperfect. There are no reductivity,
splitness, connectedness, finite-type, smoothness, reducedness, perfection or
infinitude hypotheses.

## Meanings and directions of the maps

`Coord G` is the published `Lie.coordinateAlgebra G`, presenting the actual
given scheme by `Lie.coordinateIso G`. The algebra `algebra G` is literally

```lean
AlgHom.equalizer (conjugationPullback G) (includeRight G)
```

Its defining pair consists of actual conjugation pullback and the pullback
of projection to the point being conjugated. Its published invariance criterion
tests every commutative coefficient algebra in universe `u`, including
nonreduced algebras. `inclusion G` is the actual subalgebra inclusion.
`quotient G` is relative Spec of this invariant algebra, and `rho G` is
the spectrum of that inclusion composed with `(Lie.coordinateIso G).inv`.
The notation `quotient` retains this published invariant-ring meaning.

The first equation fixes `e` as the comparison with the actual scheme pullback.
The map `Spec.map e.toRingHom` goes from the spectrum of `Coord GF` to the
spectrum of `F ⊗[K] Coord G`. The displayed `baseChangeIso` then goes from
that tensor spectrum to the actual pullback of `G.X`. This composite must
equal the chosen coordinate presentation of `GF` itself. The base morphism
called `algebraBaseMap K F` by the tensor-coordinate API is definitionally `b`.

The second equation is an equality of `F`-algebra homomorphisms from
`F ⊗[K] algebra G` to `Coord GF`. Thus `phi` agrees with `e` on the
actual inclusions into the ambient coordinate algebras. An arbitrary
isomorphism between the abstract invariant algebras is insufficient.

The third equation identifies the underlying scheme map of `alpha` explicitly.
`tensorSpecIso` goes from the base change of `quotient G` to
`Spec (F ⊗[K] algebra G)`. Contravariance then requires `phi.symm`,
whose spectrum goes from that tensor spectrum to `quotient GF`.
This specifies the quotient comparison associated with the same `phi`.

The fourth equation is in `Over (Spec (CommRingCat.of F))`. Its source is
the actual base change of `G.X`, which is the underlying object of `GF`,
and its target is `quotient GF`. It asserts commutativity for the actual
canonical maps `rho`, after the comparison `alpha`.

## Derived provenance and the remaining proof

Provenance: derived/internal.

The intended proof route is internal affine geometry and flat algebra.
Every field extension is flat. Since the published invariant algebra is a
literal equalizer, a later proof can first compare actual conjugation pullback
and projection under the tensor-coordinate presentation, then apply the
existing `AlgHom.tensorEqualizerEquiv` in
`Mathlib/RingTheory/Flat/Equalizer.lean`. The accompanying
`AlgHom.coe_tensorEqualizer` describes its compatibility with inclusion.
The published `AutomorphicAction.baseChange_conjugation` is relevant to
comparison of the actual action, and
`HopfMorphismBaseChange.tensorSpecIso_naturality` supplies spectrum naturality.
The tensor/conjugation comparison, the invariant identification, and all
four equations remain conclusions to prove; this module supplies no
provisional theorem asserting them.

The motivating original is R. Steinberg, *Regular elements of semi-simple
algebraic groups*, Publications Mathématiques de l'IHÉS 25 (1965), 49–80,
registered source `steinberg-1965-regular-elements-semisimple-groups`,
SHA-256 `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
The passages read are section 6.1 and its preceding definition, printed p.62
/ PDF p.15; section 6.10 and its preceding paragraph, printed p.64 /
PDF p.17; and section 6.16, printed pp.65–66 / PDF pp.18–19.
They motivate regular class functions, equality on them, and their affine
quotient in Steinberg's setting. They do not state the present field-base-change
proposition for arbitrary affine group schemes. No corresponding project
errata note was found. No Borel–Springer 8.6 premise is used.

This statement alone supplies no finite generation, fundamental-character
generation, geometric-fibre theorem, cross-section or rational lifting.
The proof of this proposition and the parent fibre and lifting results are
separate obligations. This new pair leaves the published `ClassFunctions`
pair, `QuasiSplitSteinbergQuotientStatement` and every pair imported by that
statement unchanged.
