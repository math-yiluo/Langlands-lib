# Polarized automorphisms that are trivial at every geometric point

This module proves that polarized automorphisms of ordinary polarized full-level data
are trivial at large level, over every base on which the level is a unit. Lefschetz's
theorem `CubicFieldEmbeddingStatement` is the only unproved input, and it enters as an
explicit hypothesis.

## Declarations

- `hom_eq_id_of_geometricPoints`: let `A` be an abelian scheme over a scheme `S` and
  `f : A ⟶ A` an endomorphism. Assume that for every algebraically closed field `K`
  (in the universe of `S`) and every morphism `b : Spec K ⟶ S`, the base change
  `(baseChange b).map f` has underlying scheme morphism the identity. Then the
  underlying scheme morphism of `f` is the identity of `A.X.left`.
- `PolarizedIso.eq_refl_of_geometricPoints`: let `a` be a datum over `S` and
  `α : PolarizedIso a a`. If for every algebraically closed field `K` and every
  `b : Spec K ⟶ S` the pulled-back polarized isomorphism `α.pullback b` equals
  `PolarizedIso.refl (a.pullback b)`, then `α = PolarizedIso.refl a`.
- `PolarizedIso.eq_refl_of_field_of_cubicFieldEmbedding`: assume
  `hL : CubicFieldEmbeddingStatement`, `0 < g`, `0 < d` and
  `(cubicProjectiveDimension g d + 1) * (6^g * d * g!) < n`. Let `K` be an algebraically
  closed field with `(n : K) ≠ 0` and `a` a datum over `Spec K`. Then every
  `α : PolarizedIso a a` equals `PolarizedIso.refl a`.
- `PolarizedIso.eq_refl_of_cubicFieldEmbedding`: under the same hypotheses on `hL`,
  `g`, `d`, `n`, let `S` be any scheme with `n` a unit in `Γ(S, ⊤)` and `a` a datum over
  `S`. Then every `α : PolarizedIso a a` equals `PolarizedIso.refl a`.

Since `cubicProjectiveDimension g d + 1 = 6^g d` for positive `d`, the size condition
reads `n > (6^g d) * (6^g d g!)`; the Lean statements keep the left side as written.

## Proofs

`hom_eq_id_of_geometricPoints`. Write `X = A.X` as a group object of `Over S`, and let
`φ : X ⟶ X` be the group homomorphism underlying `f`. In the group `X ⟶ X` (pointwise
multiplication of morphisms into a group object) put `δ = φ / 𝟙 X`.

1. Since `φ` is a monoid morphism, `η ≫ φ = η` (`IsMonHom.one_hom`), so
   `η ≫ δ = η ≫ φ / η = 1`, and on underlying schemes `η.left ≫ δ.left = η.left`.
2. Over a geometric point `b : Spec K ⟶ S` the functor `Over.pullback b` preserves the
   group operations of morphisms into `X` (`Functor.map_mul`, `Functor.map_inv'`,
   `Functor.map_one`), and maps `φ` to the identity by hypothesis. Hence
   `(Over.pullback b).map δ = (Over.pullback b).map 1`.
3. Pointwise: for `x ∈ X`, let `s` be its image in `S`, `K` the algebraic closure of the
   residue field `κ(s)`, and `b : Spec K ⟶ S` the induced geometric point. Its closed
   point lies over `s`, so (`Scheme.Pullback.exists_preimage_pullback`) some point `y`
   of `X ×_S Spec K` maps to `x`. Applying step 2 and the first projection to `y` gives
   `δ.left x = (1 : X ⟶ X).left x`, i.e. `δ.left x = η.left (p x)` where `p = X.hom`.
4. The Library proof `smoothProperConnectedGlobalFunctions` shows that `p.app U` is an
   isomorphism for every open `U` of `S`, because `p` is smooth, proper and geometrically
   connected. With the section `η.left` of `p` and step 3, the Library proof
   `factorizationOfGlobalFunctions` gives `δ.left = p ≫ η.left ≫ δ.left = p ≫ η.left`,
   so `δ = 1` as a morphism of `Over S`.
5. Then `φ = 𝟙 X` (`div_eq_one`), which is the claim.

`PolarizedIso.eq_refl_of_geometricPoints`. By the Library lemma
`PolarizedIso.eq_refl_of_hom_eq_id` (`TorsionConfigurationRigidity`) it suffices that the
underlying scheme morphism of `α.abelianIso.hom` is the identity. The abelian-scheme
isomorphism of `α.pullback b` is `(baseChange b).mapIso α.abelianIso`
(`PullbackCoherence`), so the hypothesis gives exactly the hypothesis of
`hom_eq_id_of_geometricPoints`.

`PolarizedIso.eq_refl_of_field_of_cubicFieldEmbedding`. This repeats the setup of
`Datum.exists_frameLocus_eq_top` (`FrameLocusField`). The cubic direct image is locally
free (`cubicDirectImage`), hence of finite presentation, and `hL` makes the full cubic
evaluation an epimorphism. The global cubic sections `V` have dimension
`cubicProjectiveDimension g d + 1` (`Datum.finrank_cubicSections`); choose a basis `β`
(`Module.finBasisOfFinrankEq`). It generates (`Datum.basis_generates`), and its section
map is a closed immersion (`Datum.isClosedImmersion_cubicSectionMap`, from `hL`). The
Library theorem `PolarizedIso.eq_refl_of_canonicalCubicSectionBasis_count`
(`CanonicalCubicRigidity`), with the proved count `cubicTorsionHyperplaneBound` and the
size inequality from `frameSize_lt` (`FrameLocusCoverReduction`), gives
`α = PolarizedIso.refl a`.

`PolarizedIso.eq_refl_of_cubicFieldEmbedding`. Apply
`PolarizedIso.eq_refl_of_geometricPoints`. For a geometric point `b : Spec K ⟶ S`, the
unit `n` of `Γ(S, ⊤)` maps under `b.appTop` and `Scheme.ΓSpecIso` to a unit of `K`, so
`(n : K) ≠ 0`, and the field case applies to `α.pullback b`.

## Provenance

The field case is Mumford's large-level argument: Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third edition (1994), Proposition 7.7 (printed p.138,
PDF p.151), the count of torsion points on a hyperplane that Corollary 7.8 and
Theorem 7.9 (printed p.139, PDF p.152) build on, here through the Library's
`CanonicalCubicRigidity`, which turns the count into triviality of polarized
automorphisms. Steps 1-5 of the first proof are the rigidity lemma
of the same book, Proposition 6.1 and Corollary 6.2 (printed pp.115-116, PDF
pp.128-129), in the special form where the two morphisms agree at every geometric point:
the Library's `FactorizationOfGlobalFunctions` replaces the scheme-theoretic part of
Mumford's proof. The passage through algebraic closures of residue fields and the
explicit bound are internal.
