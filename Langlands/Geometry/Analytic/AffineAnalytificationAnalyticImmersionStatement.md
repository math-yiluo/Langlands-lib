# Statement: affine analytification detects open and closed immersions

`AffineAnalytificationAnalyticImmersionStatement` compares algebraic and
analytic immersions for the Library's affine analytifications. Let `K` be a
complete ultrametric nontrivially normed field and `f : A → B` a `K`-algebra map
between finitely presented commutative `K`-algebras. Let
`F : Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` be the induced morphism in the localized category
of analytic spaces. Then:
1. `f` is surjective if and only if `F` is a closed immersion;
2. `Spec(f) : Spec B → Spec A` is an open immersion of schemes if and only if
   `F` is an open immersion.

The two analytic notions are the morphism properties `closedImmersion` and
`openImmersion` of `AnalyticImmersion`. This module states the proposition
only; it supplies no proof.

## Statement

The statement quantifies over universes `u` and `v` and over:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- commutative `K`-algebras `A B : Type v`, with finite polynomial presentations
  `P : FinitePolynomialPresentation K A` and
  `Q : FinitePolynomialPresentation K B`;
- a `K`-algebra map `f : A →ₐ[K] B`.

The conclusion is the conjunction of
- `Function.Surjective f ↔ closedImmersion (localizedHom K P Q f)`;
- `AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))
  ↔ openImmersion (localizedHom K P Q f)`.

`localizedHom K P Q f : localized K Q ⟶ localized K P` is the morphism of
`AffineAnalytificationLocalizedMap`. It is the image in
`SaturatedAtlasPresentation.LocalizedCategory.{u, u, u}` of the morphism of
saturated presentations induced by `f`. Its underlying continuous map is
`baseMap K P Q f`. `Spec.map (CommRingCat.ofHom f.toRingHom)` is Mathlib's
morphism of affine schemes `Spec B ⟶ Spec A` induced by the ring map of `f`.
`AlgebraicGeometry.IsOpenImmersion` is Mathlib's notion of open immersion of
schemes. `A` and `B` lie in one universe `v` because `CommRingCat.ofHom` needs
this.

The analytic notions are those of `AnalyticImmersion`, summarized here.
- `openImmersion φ` for `φ : X ⟶ Y` says that `φ` is an isomorphism onto the
  analytic space of an open subset `U` of the space of `Y`, followed by the
  canonical morphism of that open domain.
- `closedImmersion φ` says that the arrow `φ` is isomorphic, in the arrow
  category, to the image of a strong map `g` between constructed saturations
  with the following property. For every recognized affinoid subset `W` of the
  target, the preimage of `W` under `g` is a recognized affinoid subset `V` of
  the source. The bounded map from the algebra of `W` to that of `V` is an
  admissible epimorphism.

## Provenance

The main source is Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The pages below were read in the registered file.
- Proposition 3.4.6, printed p.65/PDF p.79. For a morphism `φ : Y → X` of
  schemes of locally finite type over `k`, `φ` has property (8) "an open
  immersion" if and only if `φᵃⁿ` does. The proof of (8) is on printed
  p.66/PDF p.80. The forward direction is "by the proof of Theorem 3.4.1". The
  converse shows that `φ` is étale and radical, hence an open immersion.
- Proposition 3.4.7(2), printed p.66/PDF p.80. If `φ` is of finite type, then
  `φ` is a closed immersion if and only if `φᵃⁿ` is. The forward direction is
  again "by the proof of Theorem 3.4.1". The converse uses that `φᵃⁿ` is a
  proper monomorphism, with Proposition 3.4.6(10) and Proposition 3.4.7(3).

The analytic notions follow Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), registered as `berkovich-1993-etale-cohomology`,
SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. Its
definition of open immersions is after Definition 1.3.1, printed p.23/PDF p.20.
Its definition of closed immersions is Lemma 1.3.7 and the text after its
proof, printed pp.27–28/PDF pp.24–25. The `AnalyticImmersion` Markdown explains
how the Lean definitions match these.

The motivating source is Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), registered as `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Printed p.19, in the proof of Proposition 5.11(3), uses that analytification is
compatible with open and closed immersions.

The formulation is derived. Berkovich treats morphisms of schemes of locally
finite type over `k`. Here the schemes are `Spec A` and `Spec B` for finitely
presented `K`-algebras, so `Spec(f)` is of finite type. A morphism of affine
schemes is a closed immersion exactly when its ring map is surjective, so item
1 uses surjectivity of `f`. Item 2 keeps the scheme-theoretic open immersion.
Only nontrivially normed `K` is treated, as the Library's affine
analytifications require. The Library's `AffineAnalytificationImmersionStatement`
gives the forward implications for underlying spaces only. This statement
upgrades them to the analytic notions and adds the converses.

## Why the statement should be true

This is not a Lean proof.

Item 1, forward. Let `f` be surjective with kernel `I`. Over each bounded
polynomial chart of `A`, with affinoid algebra `𝒜`, the corresponding chart of
`B` is the closed subspace with algebra `𝒜/I𝒜`. This is step (2) of the proof
of Berkovich 1990, Theorem 3.4.1. For any affinoid domain `W` of `Spec(A)ᵃⁿ`
with algebra `𝒜_W`, the preimage is then the affinoid domain with algebra
`𝒜_W/I𝒜_W`, and `𝒜_W → 𝒜_W/I𝒜_W` is an admissible epimorphism. Choosing
saturations of index universe `u` that are isomorphic to `localized K Q` and
`localized K P` gives the arrow isomorphism required by `closedImmersion`.

Item 1, converse. A `closedImmersion` gives a strong map `g` satisfying the
condition of Berkovich 1993, Lemma 1.3.7(b) on the recognized affinoid domains.
These domains include all chart ranges, so `g` is a closed immersion in
Berkovich's sense. The arrow isomorphism transports this to `F`. By Berkovich
1990, Proposition 3.4.7(2), `Spec(f)` is then a closed immersion, so `f` is
surjective.

Item 2. This is Berkovich 1990, Proposition 3.4.6(8). For the forward
direction, an open immersion `Spec B → Spec A` identifies `Spec(B)ᵃⁿ` with the
open subset `π⁻¹(Spec B)` of `Spec(A)ᵃⁿ`. That subset is an open domain, and the
universal property of open domains gives the isomorphism required by
`openImmersion`. For the converse, follow Berkovich's proof. An open immersion
of analytic spaces is étale, so `Spec(f)` is étale by Proposition 3.4.6(3). Its
fibres over closed points are radical. The points with radical fibre form a
locally constructible set, so every fibre is radical. An étale radical morphism
is an open immersion.
