# Extension of generic homomorphisms to smooth integral models

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Section 2.10: Lemma 2.10.9, Corollary 2.10.10 and Remark 2.10.19, printed
pp. 123–124 and 127 / PDF pp. 154–155 and 158. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, do not
amend Section 2.10. Their entries pass from Section 2.6 directly to
Section 2.11.

## Source content

In Section 2.10 (printed p. 121 / PDF p. 152), `o` is a Henselian
discrete valuation ring with fraction field `k`, `K` is a fixed maximal
unramified extension of `k`, and `O` is the ring of integers of `K`. The
residue field of `O` is the separable closure `f_s` of the residue field
`f` of `o`. By Definition 2.10.1, an integral model `𝒳` of an affine
`k`-variety `X` is an affine flat finite-type `o`-scheme with an
isomorphism `𝒳 ×_o k → X`. By Remark 2.10.3, `o[𝒳]` is an
`o`-subalgebra of `k[X]`, and a morphism `θ : X → Y` extends to
`𝒳 → 𝒴` exactly when `θ*(o[𝒴]) ⊂ o[𝒳]`. Such an extension is unique.

- **Lemma 2.10.9.** If `𝒳` is a smooth integral model of `X`, then
  `o[𝒳] = {f ∈ k[X] | f(𝒳(O)) ⊂ O}`. In the proof, smoothness makes the
  reduction map `𝒳(O) → 𝒳(f_s)` surjective (KP Lemma 8.1.3). Also,
  `𝒳(f_s)` is schematically dense in the special fibre.
- **Corollary 2.10.10.** Let `X` and `Y` be affine and of finite type over
  `k`, with `X` smooth. Let `𝒳` be a smooth `o`-model of `X` and `𝒴` any
  model of `Y`. Then `θ : X → Y` extends (necessarily uniquely) to a
  morphism `𝒳 → 𝒴` if and only if `θ(𝒳(O)) ⊂ 𝒴(O)`. The proof combines
  Remark 2.10.3 with Lemma 2.10.9.
- **Remark 2.10.19.** First, a schematic open bounded subgroup
  `U ⊂ X(K)` has a smooth model that is a group scheme. Second, suppose
  `𝒴` is a group scheme over `o` with generic fibre `Y`, and `θ` is a
  group homomorphism with `θ(𝒳(O)) ⊂ 𝒴(O)`. Then the canonical extension
  `𝒳 → 𝒴` is a homomorphism of group schemes.

## Lean declarations

All rings and schemes are in the arbitrary universe `u`. The models are
the published `IntegralModel`s: affine, flat, locally of finite type
group schemes over the integral base. Each comes with a specified
group-scheme isomorphism `genericIso` from its actual generic fibre to the
given generic group. Affine plus locally of finite type is finite type, so
these are the models of KP Definition 2.10.1(1), with a group structure.
`M.Hom N f` (`IntegralModel.Hom`) is a group-scheme morphism
`M.group ⟶ N.group`. Its generic base change, composed with the specified
generic identifications, is the given `f : G ⟶ H`. It is an extension in
the sense of KP Definition 2.10.1(2), and it is a group-scheme
homomorphism, as in the second part of Remark 2.10.19. The uniqueness in
Corollary 2.10.10 is already published as `IntegralModel.Hom.hom_eq`
(module `IntegralModel.GenericRigidity`) and is not restated here.
`M.IsSmooth` is smoothness of the actual structure morphism of `M.group`.
`M.integralPoints` is the image of the sections of `M.group` over the
integral base in `rationalPoints G`, through the specified generic
identification.

### Strictly Henselian form

`SmoothHomExtensionStatement.{u}` is an unproved proposition. Its inputs
are:

- a Henselian discrete valuation ring `R` with separably closed residue
  field, and a specified fraction field `K`;
- generic groups `G H` over `Spec K` and a homomorphism `f : G ⟶ H`;
- a model `M` of `G` with `M.IsSmooth`, and an arbitrary model `N` of `H`.

The hypothesis is that `rationalPoints.map f` carries every point of
`M.integralPoints` into `N.integralPoints`. The conclusion is
`Nonempty (M.Hom N f)`.

This is the source's case `o = O`. Take `o := R` and `k := K`. The finite
unramified extensions of a Henselian `k` correspond to the finite
separable extensions of its residue field. When the residue field is
separably closed, `k` is its own maximal unramified extension, so `K = k`
and `O = o`. Then KP's `𝒳(O)` and `𝒴(O)` are exactly `M.integralPoints`
and `N.integralPoints`, and `θ(𝒳(O)) ⊂ 𝒴(O)` is the stated hypothesis.
KP's proof of Lemma 2.10.9 uses two facts:

- reduction `𝒳(o) → 𝒳(f)` is surjective for smooth `𝒳` over a Henselian
  base;
- the residue-field points are schematically dense in the smooth special
  fibre over the separably closed field `f`.

Both hold for every such `R`; completeness is not used. KP's hypothesis
that `X` is smooth is implied: `M.IsSmooth` makes the generic fibre of
`M.group` smooth, and `genericIso` identifies that fibre with `G`. KP's
`Y` is any affine finite-type `k`-scheme, so no reducedness or smoothness
is imposed on `H` or `N`.

### Local-field form

`UnramifiedSmoothHomExtensionStatement.{u}` is an unproved proposition.
It is the source's statement over a nonarchimedean local field `F`, with:

- `o` the integers `𝒪[F]`;
- `K` the existing `inertiaFixedField F`, the fixed field of inertia in the
  chosen separable closure, i.e. the maximal unramified extension;
- `O` its integers `fixedFieldIntegers F`.

KP's `𝒳(O) ⊂ X(K)` is `M.baseChangeUnramified.integralPoints`. This is a
subgroup of the rational points of `baseChanged F (inertiaFixedField F) G`
and consists of the `O`-sections of the base change of `M.group` to `O`.
KP's `θ` acting on `X(K)` is the actual base change
`(GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map f`. The
hypothesis is that this map carries
`M.baseChangeUnramified.integralPoints` into
`N.baseChangeUnramified.integralPoints`. The conclusion is again
`Nonempty (M.Hom N f)`, a homomorphism of models over `𝒪[F]` itself, not
over `O`. No completeness, perfectness, reductivity or connectedness
premise is added. The coefficient algebra `𝒪[F] → fixedFieldIntegers F`
and its scalar tower are the local instances that `baseChangeUnramified`
itself uses: the integer algebra induced by the valuation extension
`fixedFieldValuation F`. The two local instances in this file repeat them
for the necessity lemma.

**Why maximal-unramified points.** Over a finite residue field `F_q`, the
`𝒪[F]`-points of a smooth model do not determine the model. Here is a
counterexample to the variant with `𝒪[F]`-points, where `π` is a
uniformizer. Let `N` be the dilatation of `G_a = Spec 𝒪[F][x]` along the
closed subgroup `{x^q = x}` (the constant group `F_q`) of its special
fibre. It is `Spec 𝒪[F][x, t]/(π t − (x^q − x))`, a smooth affine
`𝒪[F]`-group scheme with generic fibre `G_a`. Since every residue class
lies in `F_q`, `N(𝒪[F]) = 𝒪[F] = G_a(𝒪[F])`. So the identity
`G_a → G_a` carries the `𝒪[F]`-points of the smooth model `M = G_a` into
those of `N`. It does not extend to `G_a → N`, because
`(x^q − x)/π ∉ 𝒪[F][x]`. Over `O`, the residue field is the algebraic
closure of `F_q`, so `N(O) ⊊ G_a(O)` and the unramified hypothesis
correctly fails. This is why KP state the criterion with `𝒳(O)`.

### Necessity lemmas

Two proved lemmas give the necessary direction. They are internal
consequences of published API, not new source claims:

- `Hom.integralPoints_map_le` holds over any domain with a specified
  fraction field. A model homomorphism `φ : M.Hom N f` carries
  `M.integralPoints` into `N.integralPoints` along `rationalPoints.map f`.
  The proof is the published `Hom.map_mem_integralPoints`: an integral
  point `x` is sent to the image of the section `x ≫ φ.hom`, by the
  generic compatibility square.
- `Hom.unramifiedIntegralPoints_map_le` is the local-field version.
  `φ : M.Hom N f` carries `M.baseChangeUnramified.integralPoints` into
  `N.baseChangeUnramified.integralPoints` along the base-changed `f`. The
  proof first forms the published coefficient base change
  `φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)`.
  This is a homomorphism from `M.baseChangeUnramified` to
  `N.baseChangeUnramified` over the base-changed `f`. The proof then
  applies `Hom.map_mem_integralPoints` to it.

Each unproved statement is the converse of its proved lemma. Together
they give the source's "if and only if" in the two settings.

## Scope

- Corollary 2.10.10 is stated for affine finite-type schemes and arbitrary
  morphisms. Here both sides are group-scheme models and `f` is a
  group-scheme homomorphism. This is the setting of the second part of
  Remark 2.10.19 and of every intended consumer.
- The two forms cover the case `o = O` (any Henselian DVR with separably
  closed residue field) and the case of a nonarchimedean local field `F`.
  A general Henselian `o` with an arbitrary chosen maximal unramified
  extension is not stated.
- Not stated separately: Lemma 2.10.9 (the coordinate-ring description),
  Corollary 2.10.11 (full faithfulness), the first part of Remark 2.10.19
  (here models are group schemes by definition), and Lemma 2.10.13
  (non-affine source).
- The module proves neither target, constructs no model, and does not
  state unramified descent of models (Fact 2.10.16).

## Intended consumers

The construction of the integral models for KP Axioms 4.1.20 and 4.1.22
(task `cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) needs this extension
criterion. With it, the inclusions `P_Ω ⊂ P_Ω'` of bounded subgroups give
model homomorphisms, and actions of rational points extend to the models.
KP use the criterion in the same way. Axiom 4.1.22 (printed p. 163 /
PDF p. 194) recalls that, for strictly Henselian `k`, Corollary 2.10.10
gives the homomorphism `ρ_{Ω,Ω'} : 𝒢¹_{Ω'} → 𝒢¹_Ω`. In Section 8.3,
8.3.17 obtains `ρ_{Ω,Ω'} : 𝒢⁰_{Ω'} → 𝒢⁰_Ω` from it (printed p. 302 /
PDF p. 333).
