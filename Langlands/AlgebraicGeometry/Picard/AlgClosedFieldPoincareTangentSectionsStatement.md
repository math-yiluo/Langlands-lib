# Sections of the Poincaré bundle along a nonzero tangent vector at the origin

`Langlands.AbelianScheme.AlgClosedFieldPoincareTangentSectionsStatement` is a
proposition definition. It states a proposition and gives no proof or new axiom.

## Statement

The universe `u` is arbitrary. The binders, in order, are:

- `K : Type u` with `[Field K]` and `[IsAlgClosed K]`;
- `A : AbelianScheme (Spec (CommRingCat.of K))` and `hA : HasDualScheme A`.
  Write `D = dualScheme A hA` for the chosen dual, `p` for the projection
  `((baseChange D.hom).obj A).X.hom : A ×_K D ⟶ D`, and `P` for
  `(poincareLineBundle A hA).obj`, the Poincaré line bundle on `A ×_K D`;
- `t : Spec (CommRingCat.of (DualNumber K)) ⟶ D.left`, a `K[ε]`-point of `D`,
  where `K[ε]` is Mathlib's `DualNumber K`;
- a proof of
  `IsNonzeroTangentVectorAt D.hom (dualOrigin A hA).left t`;
- a scheme `X` with morphisms `q : X ⟶ A ×_K D` and `f : X ⟶ Spec K[ε]`, and a
  proof of `IsPullback q f p t`.

The conclusion is

```text
IsEmpty ((relativeGlobalSections f).obj ((Scheme.Modules.pullback q).obj P) ≅
  ModuleCat.of (DualNumber K) (DualNumber K))
```

In words: the `K[ε]`-module of global sections of `q^* P` on `X` is not free
of rank one.

`IsNonzeroTangentVectorAt` is the Library's predicate from
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`. It says that `t`
lies over `Spec K` (`t ≫ D.hom` is the structure map of `Spec K[ε]`), that the
closed point of `Spec K[ε]` maps to the origin
(`dualNumberAugmentation K ≫ t = (dualOrigin A hA).left`), and that `t` differs
from the zero tangent vector `dualNumberProjection K ≫ (dualOrigin A hA).left`.
`relativeGlobalSections f` is the Library's functor of global sections, viewed
as `K[ε]`-modules through `f`. The fibre product `X` is any pullback of `p`
along `t`, so `X` is isomorphic to the base change `A ×_K Spec K[ε]`, and
under this isomorphism `q^* P` is the pullback of `P` along `id_A × t`.

## Original source and derived formulation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, the second proof of
Theorem (9.1). The source's notation differs from the notation above: there
`X` is the abelian variety over the field `k`, `Xᵗ` its dual, `A = O_{Xᵗ,0}`
the local ring of the dual at the origin with maximal ideal `m`, and, for an
ideal `J` of `A`, `P(J)` is the restriction of the Poincaré bundle to
`Y(J) = X × Spec(A/J)` ((9.5), printed p.127, PDF p.131).

In (9.8), printed p.130 (PDF p.134), the authors show that the section
`1 ∈ k = H⁰(X, O_X)` lifts to a global section of `P(b)`. They conclude,
"with the same arguments as in (9.5)", that `P(b)` is trivial, and that the
universal property of `P` then forces `b = m`. The argument of (9.5), printed
p.128 (PDF p.132), is this: a homomorphism of line bundles that is an
isomorphism modulo `m` is an isomorphism, so the pullback of `P` along
`id_X × i(a)` is trivial, and by the universal property of `P` the immersion
`i(a) : Spec(A/a) ⟶ Xᵗ` factors through the origin.

This statement is derived content. It is the special case of that argument for
a first-order thickening `Spec K[ε]` of the origin. The source's ideal `b` is
replaced by a tangent vector, and the source's lifting argument is replaced by
a statement about the module of sections. The informal argument is as follows.
Suppose the sections were free of rank one over `K[ε]`, with generator `s`.
The closed fibre of `f` is `A`, and the restriction of `q^* P` to it is the
restriction of `P` to `A × {0}`, which is trivial, so its sections form
`H⁰(A, O_A) = K`. The generator `s` restricts to a nonzero element there:
otherwise `s` would be a section of `ε · q^* P`, and then `ε s = 0`. A nonzero
constant section of `O_A` vanishes nowhere, so `s` trivializes `q^* P`. By the
universal property of the chosen dual, a trivial pullback forces `t` to be the
zero tangent vector, which contradicts the hypothesis. This argument is a guide
only; a proof must establish each step for the Library's objects.

## Role

This is a prerequisite of the exact proof of
`Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement`, which
follows (9.6)–(9.9) of the source. That proof is planned to apply the
commutative-algebra proposition
`Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement`, stated in
a separate unit, to the local ring `R = O_{D,0}` and a perfect complex `C`
computing the cohomology of `P` near the origin. The last hypothesis of that
proposition requires that the degree-zero homology of `C ⊗ R/J` is not
isomorphic to `R/J` for every ideal `J` with `m² ≤ J ⋖ m`. Since the origin is
a `K`-rational point, `R/J` is then isomorphic to `K[ε]`. The consumer, not
this statement, identifies that homology with the sections in this statement,
for the nonzero tangent vector `Spec(R/J) ⟶ D`.
