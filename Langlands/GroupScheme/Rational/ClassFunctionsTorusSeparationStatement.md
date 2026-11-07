# Statement: the canonical class quotient separates conjugacy classes of torus points

Author: Worker 1531.

This module defines the proposition
`Langlands.GroupScheme.ClassFunctions.TorusSeparationStatement.{u}`. A
separate proof must prove this exact proposition.

## Complete Lean proposition

```lean
def TorusSeparationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSemisimple G),
    letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (s t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.X),
      (s ≫ j.hom.hom) ≫ rho G = (t ≫ j.hom.hom) ≫ rho G →
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
        g * (s ≫ j.hom.hom) * g⁻¹ = t ≫ j.hom.hom
```

The imports are `Langlands.GroupScheme.Rational.ClassFunctions`,
`Langlands.GroupScheme.Reductive.Semisimple` and
`Langlands.GroupScheme.Torus.Maximal`. The namespace is
`Langlands.GroupScheme.ClassFunctions`, and the one universe parameter `u` is
arbitrary.

## Objects, hypotheses and conclusion

The field `k : Type u` is algebraically closed, and its characteristic is
unrestricted. `G` is a group scheme over `Spec k` with the published
`IsSemisimple G`: connected reductive with finite scheme-theoretic centre.
Simple connectedness is not assumed. The local instance
`hG.isConnectedReductive.isAffineHom` supplies the affineness needed to form
the canonical quotient. It is derived from the hypothesis and is not an
additional premise.

`T` is a commutative group scheme over `Spec k`, and `j : T ⟶ G` satisfies
the published `IsMaximalTorus j`: `T` is a torus, `j` is a closed subgroup,
and `j` factors through no strictly larger closed torus. No splitting, root
datum, Weyl group or pinning is chosen.

`s` and `t` are `k`-points of `T`. Here `𝟙_ (Over (Spec k))` is the terminal
object `Over.mk (𝟙 (Spec k))` (the two agree definitionally), and
`s ≫ j.hom.hom` is the image of `s` in `G(k)`.

`ClassFunctions.rho G : G.X ⟶ ClassFunctions.quotient G` is the published
canonical map to the relative spectrum of `ClassFunctions.algebra G`. That
algebra is the equalizer subalgebra of the actual conjugation pullback and
the second-factor inclusion in the coordinate algebra of `G`, that is, the
algebra of regular class functions. The published `ClassFunctions.rho_eq_iff`
identifies equality of quotient images of affine points with equality of
the values of every element of this algebra. The hypothesis therefore says
that every regular class function takes the same value at the images of `s`
and `t`.

The conclusion supplies `g ∈ G(k)` with
`g * (s ≫ j.hom.hom) * g⁻¹ = t ≫ j.hom.hom`, using the group structure on
`k`-points of `G`. The conjugating point need not normalize `T`.

## Source

Provenance: derived.

R. Steinberg, *Regular elements of semi-simple algebraic groups*,
Publications Mathématiques de l'IHÉS 25 (1965), 49–80, registered source
`steinberg-1965-regular-elements-semisimple-groups`. The registered PDF was
read on one-based PDF pp.15–16 (printed pp.62–63). No corresponding project
errata note was found.

Steinberg's standing convention ("G, T, etc. are as before") is a semisimple
group `G` over an algebraically closed field `K` with a maximal torus `T`.

- Section 6, printed p.62, defines a class function as a function with equal
  values at conjugate points of definition. Theorem 6.1 introduces `C[G]`,
  the algebra of regular class functions. Before Lemma 6.2, Steinberg defines
  the restriction `C[G] → C[T/W]`. He uses that two elements of `T` are
  conjugate in `G` if and only if they are conjugate under `W`.
- Corollary 6.4, printed p.63: this restriction map is surjective, hence an
  isomorphism.
- Corollary 6.6, printed p.63: for `x` and `y` both semisimple, or both
  regular, conjugacy is equivalent to (b) `f(x) = f(y)` for every `f` in
  `C[G]`. The proof of (b) ⇒ (a) reduces to `x, y ∈ T`. It uses 6.4 to obtain
  equality of all `W`-invariant regular functions on `T`. Since `C[T/W]`
  separates `W`-orbits of the finite group `W`, the points are conjugate.

The Lean proposition is the implication (b) ⇒ (a) of Corollary 6.6 for
points of a maximal torus, which are semisimple. Steinberg's `C[G]` is
formalized by the canonical `ClassFunctions.algebra G` through `rho G`, as
described above. Over an algebraically closed field and for the reduced
group `G`, an element of the coordinate algebra is in this equalizer exactly
when its values are constant on conjugacy classes of `k`-points. Using the
scheme-theoretic invariant algebra therefore matches Steinberg's regular
class functions. This identification is the only derived step. The
proposition quantifies over arbitrary maximal tori rather than a fixed one,
which matches Steinberg's convention since every maximal torus may serve
as `T`.

## Boundary

This unit states the proposition only. It does not prove surjectivity of
Chevalley restriction (Corollary 6.4), any highest-weight theory, or the
separation of `W`-orbits. It does not assert conjugacy of non-semisimple
points or of regular points. It supplies no description of the quotient as
`T/W` and no field-base-change result. The published `ClassFunctions` pair is
unchanged.
