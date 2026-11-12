# Lifting primitive line bundles along elementary Artinian thickenings

`Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement.{u}` is a
`Prop`-valued definition. It states the obstruction-vanishing step in the proof of
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, Proposition 6.7: on an abelian
scheme over a local Artinian ring, a line bundle over an elementary closed thickening whose
class is killed by `μ^* − p₁^* − p₂^*` lifts. The module states a target for a later proof
and adds no axiom.

## Complete checked Lean declaration

The module imports `Langlands.AlgebraicGeometry.Modules.Tensor`,
`Langlands.AlgebraicGeometry.Picard.GeometricPicardZero`,
`Mathlib.RingTheory.Artinian.Ring` and `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`.
Its entire proposition is the following declaration, in a `noncomputable section` with
universe `u`:

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

def ArtinianPrimitiveLineBundleLiftingStatement : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] (φ : B' →+* B),
    Function.Surjective φ → maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ (A : AbelianScheme (Spec (CommRingCat.of B'))),
        let j : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B') :=
          Spec.map (CommRingCat.ofHom φ)
        let A₀ : AbelianScheme (Spec (CommRingCat.of B)) := (baseChange j).obj A
        ∀ L : LineBundle A₀.X.left,
          (let P : Over (Spec (CommRingCat.of B)) := A₀.X ⨯ A₀.X
            let p1 : P ⟶ A₀.X := Limits.prod.fst
            let p2 : P ⟶ A₀.X := Limits.prod.snd
            let m : P ⟶ A₀.X := p1 * p2
            Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
              Langlands.Scheme.Modules.tensorObj
                ((Scheme.Modules.pullback p1.left).obj L.obj)
                ((Scheme.Modules.pullback p2.left).obj L.obj))) →
          ∃ L' : LineBundle A.X.left,
            Nonempty ((LineBundle.pullback (pullback.fst A.X.hom j)).obj L' ≅ L)

end Langlands.AbelianScheme
```

The approved Lean service checked this declaration in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` with zero errors and warnings. It reported
`statement_returns_prop: true`, the sole universe parameter `u`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The checked type is

```text
Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement.{u} : Prop
```

The declaration has no outer parameters; every binder occurs inside the proposition.

## Actual objects and maps

- **Rings.** `B'` and `B` are local Artinian commutative rings in `Type u`, and
  `φ : B' →+* B` is surjective. Its kernel `I := RingHom.ker φ` satisfies
  `maximalIdeal B' * I = ⊥`, so `I` is killed by the maximal ideal of `B'`. In particular
  `I² = 0` and `I` is a vector space over the residue field `k` of `B'`. These are the
  elementary thickenings of `ArtinianLiftingSmooth` and of the target
  `PicardZeroArtinianLiftingStatement`.
- **The thickening.** `j := Spec.map (CommRingCat.ofHom φ) : Spec B ⟶ Spec B'` is the
  closed immersion cut out by `I`.
- **Abelian schemes.** `A` is an abelian scheme over `Spec B'`: `A.X : Over (Spec B')` with
  smooth, proper, geometrically connected structure morphism `A.X.hom` and a commutative
  group law. `A₀ := (baseChange j).obj A` is the Library base change. By definition of
  `AbelianScheme.baseChange` its underlying scheme `A₀.X.left` is the actual fibre product
  `pullback A.X.hom j` (that is, `A ×_{Spec B'} Spec B`), with structure morphism
  `pullback.snd A.X.hom j` and the induced group law.
- **The hypothesis.** `P := A₀.X ⨯ A₀.X` is the product in `Over (Spec B)`, so `P.left` is
  the fibre product `A₀ ×_{Spec B} A₀`. `p1`, `p2` are the two projections and
  `m := p1 * p2` is their product in the group `P ⟶ A₀.X` given by the scoped group-object
  instance, that is, the actual addition `A₀ ×_B A₀ ⟶ A₀`. The premise asserts that an
  isomorphism of `P.left`-modules `m^*L ≅ p1^*L ⊗ p2^*L` exists. Here
  `Scheme.Modules.pullback` is Mathlib's pullback of module sheaves and
  `Langlands.Scheme.Modules.tensorObj` is the Library tensor product of module sheaves.
  This is the same form as the first conjunct of
  `AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement`.
- **The conclusion.** There is a line bundle `L'` on `A.X.left` such that its pullback along
  the first projection `pullback.fst A.X.hom j : A₀.X.left ⟶ A.X.left` is isomorphic to `L`
  in `LineBundle A₀.X.left`, the full subcategory of locally free rank-one module sheaves.
  So an isomorphism of underlying module sheaves exists. No isomorphism is chosen, and no
  rigidification is asked for.

## Source and translation

The source is D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*, 3rd
enlarged edition (Springer, 1994), Chapter 6, registered as literature ID
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`, file
`Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition (1994), Chapter 6.pdf`
(SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`).
Proposition 6.7 and its proof are on printed pp.117–118 (PDF pp.130–131).

Proposition 6.7 says that `Pic^τ(X/S)` is smooth over `S` for a projective abelian scheme
`X/S`. Its proof uses the infinitesimal lifting criterion: for an Artinian local ring `A`
with an ideal `I` and `m·I = (0)`, an invertible sheaf `L₀` on `X × Spec(A/I)` must be
lifted to `X × Spec(A)`. The proof makes two claims.

1. Let `q := μ^* − p₁^* − p₂^* : Pic(X/S) → Pic(X ×_S X / S)`. The theorem of the square
   over a field and Proposition 6.1 give `L₀ ∈ ker q` when `L₀` comes from `Pic^τ`.
2. The source says: "the obstruction to lifting `L₀`" and "the obstruction to lifting
   `q(L₀)`" are related by a homomorphism `H²(X̄, 𝒪) ⊗ I → H²(X̄ × X̄, 𝒪) ⊗ I`, where
   `X̄` is the closed fibre. By the structure of the cohomology of abelian varieties and
   the Künneth formula this homomorphism is injective. Since `q(L₀)` is trivial, it lifts,
   "Therefore the obstruction to lifting `L₀` must also vanish. This proves that `L`
   exists".

This statement isolates claim 2: from `L₀ ∈ ker q` it concludes that `L₀` lifts.
The dictionary is as follows.

- The source's `A` and `A/I` are `B'` and `B`. The source's `X × Spec(A)` and
  `X × Spec(A/I)` are the abelian schemes `A` over `Spec B'` and `A₀` over `Spec B` here.
  Stating everything over `Spec B'` loses no generality: a base `S` and a map
  `Spec B' ⟶ S` give the abelian scheme `X ×_S Spec B'`.
- The source's hypothesis `q(L₀) = 0` is a statement in the relative Picard group
  `Pic(X ×_S X / S)` evaluated on `Spec(A/I)`. That group is
  `Pic(X̃ ×_{A/I} X̃)` modulo line bundles from `Spec(A/I)` (here `X̃ := X × Spec(A/I)`).
  A local scheme has trivial Picard group, so the condition is the existence of an
  isomorphism `μ^*L₀ ≅ p₁^*L₀ ⊗ p₂^*L₀` of actual line bundles, which is the premise above.
- The source's conclusion, the existence of `L` on `X × Spec(A)` extending `L₀`, is the
  existence of `L'` with `(pullback.fst A.X.hom j)^*L' ≅ L`.
- The source states the result for projective `X/S`. Projectivity is used there to have
  the Picard scheme; claim 2 does not use it, and this statement has no projectivity
  hypothesis. The `AbelianScheme` bundle supplies smoothness, properness, geometric
  connectedness and the commutative group law.
- The source does not assume a rigidification for this step; neither does this statement.

## Provenance

Derived. It is claim 2 of the proof of GIT Proposition 6.7, written with the Library's
abelian schemes, base change, line bundles, module pullback and tensor product, and with the
elementary-thickening conventions of the target `PicardZeroArtinianLiftingStatement`. It is
an internal prerequisite of Task 5640 (`d1735ac9-6af5-4460-8c3a-b09a43c01ffa`), whose target
is that statement. There, the hypothesis is to be supplied by a theorem of the square for
Picard-zero line bundles over a local Artinian base; this module does not state that
theorem.

## Obligations for a later proof

The proposition is not proved in this module. A proof following the source would need:

- the obstruction class of `L` in `H²` of the ideal sheaf of `A₀ ⊂ A`
  (`SquareZeroPicardObstruction.obstructionMap`, `lineBundle_lift_iff`), identified with
  `H²(A_k, 𝒪) ⊗_k I` (`ArtinianResidueCohomology`);
- naturality of that obstruction under the three morphisms of thickenings
  `μ, p₁, p₂ : A ×_{B'} A ⟶ A`, which restrict to `m, p1, p2` on `A₀ ×_B A₀`, and its
  additivity in `L`, to get `μ^* ob(L) = p₁^* ob(L) + p₂^* ob(L)`;
- injectivity of `μ^* − p₁^* − p₂^*` on `H²(A_k, 𝒪)` for an abelian variety over a field
  `k` (Mumford, *Abelian Varieties*, §13: `H^*(A_k, 𝒪) = Λ^* H¹(A_k, 𝒪)`; the Künneth formula
  for `A_k × A_k`; a primitive element of `Λ²V` is zero in every characteristic), and its
  compatibility with `⊗_k I`.

These are proof obligations, not premises. The statement covers every characteristic and
includes relative dimension zero and the case `I = 0`.

## Authorship

Worker 3612 authored this pair.
