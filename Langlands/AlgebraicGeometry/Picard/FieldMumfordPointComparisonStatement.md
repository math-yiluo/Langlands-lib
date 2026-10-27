# The rigidified Mumford comparison at field-valued points

`Langlands.AbelianScheme.FieldMumfordPointComparisonStatement.{u}` is a
Prop-valued definition. It says that the actual rigidified Mumford family
`mumfordBundle`, pulled back along a field-valued parameter point `a`, is
isomorphic as a rigidified family to every rigidified family `Q` whose
underlying line bundle is the translation difference `t_x^*L_K ⊗ M_K`.
This file states the proposition; it does not prove it.

## Exact Lean type

The module imports only `Langlands.AlgebraicGeometry.Picard.MumfordBundle`.
Inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules`, the
complete definition is:

```lean
def FieldMumfordPointComparisonStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (k : Type u) [Field k] (A : AbelianScheme (Spec (CommRingCat.of k)))
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (a : Over.mk b ⟶ A.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange b).obj A).X),
    x.left ≫ pullback.fst A.X.hom b = a.left →
    ∀ (Q : RigidifiedFamily A (Over.mk b)),
      Nonempty (LineBundle.tensor preservation
          ((LineBundle.pullback
            (GroupScheme.translation ((baseChange b).obj A).toGrp x).left).obj
              ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
                ((RigidifiedLineBundle.forget (unitSection A)).obj L)))
          ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M) ≅
        familyLineBundle A (T := Over.mk b) Q) →
      Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (T := Over.mk b) a).obj
            (mumfordBundle A preservation L M evaluation) ≅ Q)
```

The universe `u` is arbitrary, and `k` and `K` are arbitrary fields in it.

## Notation

The statement uses no `let`; the following names abbreviate the terms
written inline above.

- `S = Spec k`, and `e = unitSection A : S ⟶ A`, the identity section.
- `A_K = (baseChange b).obj A`, the actual base change of the abelian
  scheme along `b : Spec K ⟶ Spec k`. Its total space is the chosen
  pullback `A ×_k Spec K` (abelian scheme first), with structure map the
  second projection.
- `T = Over.mk b`, the field `Spec K` as a test scheme over `S`.
- `i = pullback.fst A.X.hom b : A_K → A`, the projection to `A`.
- `L_K = i^*L`, the ordinary pullback of the underlying line bundle
  `(RigidifiedLineBundle.forget (unitSection A)).obj L`; and `M_K = i^*M`.
- `t_x = (GroupScheme.translation A_K.toGrp x).left : A_K → A_K`, left
  translation by the section `x`, built from the actual group law of `A_K`.

## Inputs

The statement quantifies, in this order, over:

1. `preservation`, a proof of `pullbackTensorComparisonIsIsoStatement.{u}`:
   the canonical pullback-tensor comparison is invertible for every scheme
   morphism. It is needed only because `LineBundle.tensor`,
   `mumfordBundle` and the rigidified tensor take it as an argument.
2. A field `k`, an abelian scheme `A` over `Spec k`, a line bundle `L`
   rigidified along `e`, an ordinary line bundle `M` on `A`, and an
   arbitrary isomorphism `evaluation : L ⊗ M ≅ O_A` of module sheaves.
   These are exactly the inputs of `mumfordBundle`; thus `M` is a
   specified tensor inverse of `L`.
3. A field `K` and any scheme morphism `b : Spec K ⟶ Spec k`, so `K` is
   an arbitrary field extension of `k`. There is no restriction on
   perfectness, separability, algebraic closure or characteristic.
4. An actual parameter point `a : T ⟶ A.X`, a morphism over `Spec k`
   from `Spec K` to `A`.
5. A section `x : Spec K ⟶ A_K` over `Spec K` (a morphism
   `Over.mk (𝟙 (Spec K)) ⟶ A_K.X`) with `x.left ≫ i = a.left`. By the
   universal property of the pullback this is the lift of `a`; the
   statement quantifies over every such `x` rather than constructing it.
6. An actual rigidified family `Q : RigidifiedFamily A T`.

`RigidifiedFamily A T` is the existing category of line bundles on the
relative space `Spec K ×_k A` (test scheme first), rigidified along the
induced section `(𝟙, b ≫ e) : Spec K → Spec K ×_k A`. Its morphisms are
module homomorphisms compatible with the rigidifications.
`familyLineBundle A Q` is the underlying line bundle of `Q`, moved from
`Spec K ×_k A` to `A_K = A ×_k Spec K` by pullback along the inverse of
the existing symmetry `relativeSpaceSymmetry`.

## Premise and conclusion

The premise is an ordinary line-bundle isomorphism, asserted in
`Nonempty` form,

```text
t_x^*L_K ⊗ M_K ≅ familyLineBundle A Q
```

in the category `LineBundle A_K.X.left`, where `⊗` is
`LineBundle.tensor preservation`. It carries no compatibility with any
rigidification.

The conclusion is an isomorphism of rigidified families over `T`, again
in `Nonempty` form:

```text
(relativePullback A.X.hom e (unitSection_comp A) a).obj
    (mumfordBundle A preservation L M evaluation) ≅ Q.
```

Here `mumfordBundle A preservation L M evaluation : RigidifiedFamily A A.X`
is the actual rigidified Mumford family. It is parameter-first: its
underlying bundle on `A ×_k A` is `(m^*L ⊗ p1^*M) ⊗ p2^*M`, where `m` is
addition and `p1` is the parameter projection. It is rigidified along
`(id, e)`. `RigidifiedLineBundle.relativePullback` along the morphism
`a : T ⟶ A.X` in `Over S` is the existing rigidified pullback in the
relative family. Its underlying morphism is
`a × id : Spec K ×_k A → A ×_k A`, and the rigidification is pulled back
along `a.left` with the canonical structure-sheaf comparison. The
conclusion therefore asserts the existence of a module isomorphism
between the actual pulled-back Mumford bundle and `Q` that respects the
two rigidifications.

## Scope

The only inputs are the ones listed above. The proposition does not
assume ampleness, Picard-zero membership, a representing dual scheme
(`HasDualScheme`), algebraic closure of `k` or `K`, any tensor coherence
beyond `preservation`, triviality of line bundles on `Spec K`, the
pointwise formula for the Mumford fibre, or any rigidified comparison.
It constructs no classifying morphism and proves neither surjectivity
nor a lifting statement. It uses only existing Library constructions:
`mumfordBundle`, `RigidifiedLineBundle.relativePullback`,
`RigidifiedFamily`, `familyLineBundle`, `GroupScheme.translation`,
`AbelianScheme.baseChange`, `LineBundle.pullback` and
`LineBundle.tensor`.

## Internal derived provenance and intended proof

This is a derived internal comparison, not a verbatim theorem of the
source. Its ordinary mathematical content is the following. The Lean file
proves none of it; a separate exact-target proof must establish it.

1. *Fibre of the three-factor family.* Move the underlying bundle of the
   pulled-back Mumford family to `A_K` with the symmetry. Composing
   `a × id` with the symmetry, addition becomes `i ∘ t_x`, the parameter
   projection `p1` becomes the constant map `a ∘ π`, where `π : A_K →
   Spec K` is the structure map, and `p2` becomes `i`. Pullback
   composition and the invertible pullback-tensor comparison then give
   `(t_x^*L_K ⊗ π^*(a^*M)) ⊗ M_K`. The scalar factor `π^*(a^*M)` is a
   line bundle pulled back from `Spec K`. The Library's
   `MumfordPicardZero.mumfordFibreIso`, `fibreToProduct_addition`,
   `pullbackTensorIso` and `pullbackCompIso` give the corresponding
   ordinary comparison on the fibre model
   `(baseChange s).obj (paramChange A)` at a field point
   `s : Spec K ⟶ A.X.left`. A proof must
   transport them to `A_K` or redo the computation there.
2. *Scalar cancellation.* `a^*M` is a line bundle on `Spec K`, so it is
   trivial by the published `fieldLineBundleTriviality`. Hence
   `π^*(a^*M) ≅ O_{A_K}`; `MumfordPicardZero.constantIso` packages such a
   trivialization. With the unit isomorphism and the premise, the moved
   pulled-back Mumford bundle is isomorphic to `familyLineBundle A Q`.
   Pulling back along the symmetry gives an ordinary isomorphism of the
   two underlying bundles on `Spec K ×_k A`.
3. *Rigidified adjustment.* The rigidification section
   `(𝟙, b ≫ e) : Spec K → Spec K ×_k A` has the retraction
   `pullback.fst` to `Spec K`. Then
   `RigidifiedLineBundle.nonempty_iso_of_forget_iso`, with the explicit
   `preservation` input and this split section, corrects the ordinary
   isomorphism by a unit pulled back from `Spec K`. The result is an
   isomorphism of rigidified line bundles. No hypothesis
   `f_*O_{X_T} = O_T` is needed for existence.

The source's ordinary line-bundle formulas do not by themselves establish
the Library's rigidified-family comparison or the chosen-parameter
transport. Those are the content of steps 1 and 3.

## Original source

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft. Registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
available as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
The printed page number is the PDF page number minus four.

- Paragraph (6.2), printed pp.88–89 (PDF pp.92–93). A rigidification of
  a line bundle `L` on `X_T` along `ε_T` is an isomorphism
  `α : O_T ≅ ε_T^*L`. A homomorphism `h : (L1, α1) → (L2, α2)` is a
  homomorphism of line bundles with `(ε^*h) ∘ α1 = α2`. Pullback along
  `h : T' → T` is `(id_X × h)^*` with the pulled-back rigidification.
  Fact (ii) normalizes `L` to `L ⊗ f^*ε^*L^{-1}` with its canonical
  rigidification. This is the rigidified category, and the pullback, used
  by `RigidifiedFamily` and `relativePullback`.
- Chapter VI §3, printed p.95 (PDF p.99). For an abelian variety `X` over
  a field, `Pic_{X/k}` represents the functor of line bundles rigidified
  along the zero section. The Mumford bundle `Λ(L)` on `X × X` is viewed
  as a family on one factor parametrized by the other, and its
  classifying map is `φ_L(x) = [t_x^*L ⊗ L^{-1}]` on points. The
  present statement is the Library's actual rigidified version of this
  pointwise description at a field-valued parameter point, with the
  explicit inverse `M` in place of `L^{-1}`. The Library's family is
  parameter-first, whereas the source parametrizes by the factor `X(2)`.
- Proposition (7.21) and its proof, printed pp.105–106 (PDF pp.109–110).
  The source states the proposition for an algebraically closed field and
  ample `L`. Its proof uses the restriction
  `K|{x}×X ≅ t_x^*L ⊗ L^{-1} ⊗ M^{-1}` of `K = Λ(L) ⊗ p2^*M^{-1}`. That
  restriction is the ordinary fibre formula of step 1. The present
  statement uses neither the ampleness nor the algebraic closure of
  (7.21); only the fibre computation is relevant.

## Errata

No errata note for this source was found in the project's public notes
or wiki. The authors' pages were checked on 2026-10-26: Ben Moonen's
research page (`https://www.math.ru.nl/~bmoonen/research.html`, book
chapters) and Gerard van der Geer's home page
(`http://van-der-geer.nl/~gerard/`). Neither lists errata for this
draft. The cited paragraphs were read directly in the registered PDF.
