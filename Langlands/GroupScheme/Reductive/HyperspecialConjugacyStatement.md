# Statement: conjugacy of the translates of `G(R)` for split groups over local integers

Worker 75.

`Langlands.GroupScheme.ReductiveHyperspecialConjugacyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Adjoint.InnerAction`](../Adjoint/InnerAction.md), for
  `AutomorphicAction.conjugation_kernelActsTrivially`. Through it come
  `AutomorphicAction.quotientAction` of [`ActionDescent`](../ActionDescent.md),
  `AutomorphicAction.conjugation` of [`AutomorphicAction`](../AutomorphicAction.md),
  `IsSchemeTheoreticCenter` of [`Reductive.Semisimple`](Semisimple.md) and `kernelι` of
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md);
- [`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), for `IsFibrewiseRootDatumOf`
  and, through it, `splitTorus`, `splitTorus.commGroupScheme` and
  `splitTorus.exponentWeightSpace`;
- [`Reductive.Basic`](Basic.md), for `IsReductive` and `IsClosedSubgroup`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`;
- Mathlib's `Mathlib.NumberTheory.LocalField.Basic`, for `IsNonarchimedeanLocalField`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ G` in it is a homomorphism of
group schemes over `S`. For a test object `T : Over S`, the morphisms `T ⟶ G.X` in
`Over S` are the `T`-points of `G`. They form a group under the pointwise law
(`*`, `⁻¹`) induced by the group structure of `G`.

## Predicates and constructions used

- `IsNonarchimedeanLocalField F`, for a field `F` with a valuative relation and a
  topology: Mathlib's class of nonarchimedean local fields (the topology is the valuation
  topology, `F` is locally compact and the valuation is nontrivial). Mathlib derives that
  the valuation ring `𝒪[F]` is a discrete valuation ring with finite residue field. `𝒪[F]`
  is the ring of integers of `F`; write `R = 𝒪[F]` and `S = Spec R`.
- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field. This is
  Conrad's reductive group scheme (Definition 3.1.1). The statement takes the instance
  `IsAffineHom G.X.hom` from `hG.isAffineHom` by `haveI`, and deduces `IsAffine G.X.left`
  from it because the base `S` is affine (`isAffine_of_isAffineHom`); likewise for `Gad`.
- **The splitting hypothesis.** The four conditions on `(I, i, J, P)` are the Library's
  encoding of Conrad's Definition 5.1.1, used in
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  and [`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md). Here
  `i : splitTorus S I ⟶ G` is a homomorphism from the coordinate split torus `𝔾_m^I`
  (`I` finite) and `P : RootDatum J (I → ℤ) (I → ℤ)` is a Mathlib root datum on its
  coordinate character and cocharacter lattices:
  1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion;
  2. `IsFibrewiseMaximalTorus i`: on the residue fibre over every point of `S`, `i` is a
     maximal torus (`IsMaximalTorus`); by Conrad's Remark A.1.2 this makes `i` a maximal
     torus of `G`;
  3. `IsFibrewiseRootDatumOf I G i P`: `J` is finite, `P` is reduced, and for every field
     `k` with a ring homomorphism `R → k`, the realization of `P` over `k` is the root
     datum of the base change of `i` to `k`, so the roots and coroots of every fibre are
     the constant elements of `P`;
  4. for every root `α : J`, the weight space `splitTorus.exponentWeightSpace I G i
     (P.root α)` in the Lie algebra of `G` over `R` is isomorphic to `R` as an `R`-module,
     that is, free of rank one.
- `kernelι p : kernel p ⟶ G` is the scheme-theoretic kernel of `p`, the pullback of the
  unit section of `Gad` along `p`. `IsSchemeTheoreticCenter (kernelι p)` says that it is
  a closed subgroup whose functor of points is the full centre functor `center G` (points
  commuting with all points of `G` over all tests).
- `AutomorphicAction.conjugation (𝟙 G) : AutomorphicAction G G` is the conjugation action
  of `G` on itself; `conjugation_act` gives `act h g = h * g * h⁻¹`.
- `AutomorphicAction.quotientAction` ([`ActionDescent`](../ActionDescent.md)) descends an
  action of `G` along a quasi-compact, flat, surjective homomorphism `p : G ⟶ Gad` whose
  kernel acts trivially. Flatness and surjectivity come from the hypotheses `hflat` and
  `hsurj` by `haveI`, and quasi-compactness from the affineness of `G.X.left`. The kernel
  acts trivially by `conjugation_kernelActsTrivially hker`, since the kernel is central.
  The resulting `a : AutomorphicAction Gad G` is the action of `Gad` on `G` by group
  automorphisms over every test object, and `quotientAction_act_lift` together with
  `conjugation_act` gives `a.act (h ≫ p.hom.hom) g = h * g * h⁻¹` for all `T`-points `h`,
  `g` of `G`. It also acts by points of `Gad` that do not lift to `G`.
- **Points over `F` and over `R`.** `T := Over.mk (Spec.algebraMap ↥𝒪[F] F)` is `Spec F`
  as an `S`-scheme. Its points `T ⟶ G.X` are the `S`-morphisms `Spec F → G`, that is, the
  group `G(F)`. The terminal object `Over.mk (𝟙 S)` has as points the sections of `G`
  over `S`, the group `G(R)`. `res := Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)` is the
  structure morphism of `T`, so `res ≫ y` is the image in `G(F)` of `y ∈ G(R)`. Since `G`
  is affine over `S` and `R → F` is injective, this map `G(R) → G(F)` is injective and
  identifies `G(R)` with its usual copy in `G(F)`. The same holds for `Gad`.

## Statement and quantifiers

The proposition quantifies over:

- every field `F : Type u` with `[ValuativeRel F]`, `[TopologicalSpace F]` and
  `[IsNonarchimedeanLocalField F]`;
- `G Gad : GroupScheme (Spec 𝒪[F])` with `hG : IsReductive G` and `hGad : IsReductive Gad`,
  and a homomorphism `p : G ⟶ Gad`;
- the hypothesis that `G` is split: there are a finite type `I : Type u`, a homomorphism
  `i : splitTorus S I ⟶ G`, a type `J : Type u` and a root datum
  `P : RootDatum J (I → ℤ) (I → ℤ)` satisfying conditions 1–4 above;
- hypotheses `hflat : Flat p`, `hsurj : Surjective p`, that `p` is locally of finite
  presentation, and `hker : IsSchemeTheoreticCenter (kernelι p)` (all on the underlying
  morphism of schemes of `p`).

With `a`, `T` and `res` as above, it asserts that for every `x : T ⟶ Gad.X`, that is,
every `x ∈ Gad(F)`,

```
(∃ h ∈ G(F), ∀ g ∈ G(F), (g ∈ x · G(R)) ↔ (g ∈ h G(R) h⁻¹))
  ↔ ∃ h ∈ G(F), ∃ y ∈ Gad(R), x = p(h) · y,
```

where `x · G(R) = {a.act x (res ≫ y) : y ∈ G(R)}` is the image of `G(R)` under the
automorphism of `G(F)` given by `x`, `h G(R) h⁻¹ = {h * (res ≫ y) * h⁻¹ : y ∈ G(R)}`,
`p(h) = h ≫ p.hom.hom` and `y` on the right stands for its image `res ≫ y` in `Gad(F)`.
In words: the translate `x · G(R)` is `G(F)`-conjugate to `G(R)` if and only if
`x ∈ p(G(F)) · Gad(R)`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers, which agree with the one-based PDF pages.

- Setting, p.259: "Let K be a non-archimedean local field, and R its ring of integers.
  Let G be a reductive group scheme over S = Spec R. … There are generally several
  G(K)-conjugacy classes of such subgroups, due to the fact that G(K) → G^ad(K) may not
  be surjective, where G^ad := G/Z_G is the adjoint central quotient of G."
- pp.259–260: for an automorphism `f` of `G_K` arising from the action of a point
  `g ∈ G^ad(K)`, "Whether or not f(G(R)) is G(K)-conjugate to G(R) depends only on the
  image of g in G(K)\G^ad(K)/G^ad(R). In this split case the obstruction to
  G(K)-conjugacy can be made rather explicit:"
- Proposition 7.2.14, p.260: "If G is R-split then the "g-conjugate" of G(R) inside G(K)
  is not G(K)-conjugate to G(R) whenever g ∉ G(K)G^ad(R) inside G^ad(K). Equivalently,
  G^ad(K)/G(K)G^ad(R) labels the set of G(K)-conjugacy classes within the G^ad(K)-orbit
  of G(R)."
- Theorem 3.3.4, p.98: "Any reductive group scheme G → S admits a reductive center Z, and
  Z coincides with the scheme-theoretic center Z_G of G. In particular, Z_G is S-flat."
- Corollary 3.3.5, p.100: "Let G be a reductive S-group scheme, and Z a multiplicative
  type subgroup scheme of the center Z_G. The reductive quotient G/Z has center Z_G/Z; in
  particular, G/Z_G has trivial center."
- Definition 5.1.1, p.136: "Let G be a reductive group over a non-empty scheme S. It is
  split if there exists a maximal torus T equipped with an isomorphism T ≃ D_S(M) for a
  finite free Z-module M such that: 1. the nontrivial weights a : T → G_m that occur on 𝔤
  arise from elements of M …, 2. each root space 𝔤_a is free of rank 1 over O_S, 3. each
  coroot a∨ : G_m → T arises from an element of the dual lattice M∨ …"

## Derivation from the source

- **`K`, `R` and `G`.** Conrad's `K` is `F` with Mathlib's `IsNonarchimedeanLocalField`,
  and `R = 𝒪[F]`. No restriction on the characteristic is made, as in the source. "G is
  R-split" is Definition 5.1.1 over `S = Spec R`, encoded by conditions 1–4 as in
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md),
  whose Markdown explains the translation (a finite free `M` is `ℤ^I` after a choice of
  basis; condition 2 of Definition 5.1.1 is hypothesis 4).
- **`G^ad = G/Z_G`.** The adjoint central quotient is supplied as data: `Gad` is
  reductive and `p : G ⟶ Gad` is flat, surjective and locally of finite presentation with
  scheme-theoretic kernel the centre `Z_G`. Such `p` is an fppf covering whose kernel is
  `Z_G`, so `Gad` represents the fppf quotient sheaf `G/Z_G`; any two such pairs
  `(Gad, p)` are therefore uniquely isomorphic compatibly with `p`, and quantifying over
  all of them loses nothing. Conrad's Theorem 3.3.4 (`Z_G` is a flat group of
  multiplicative type) and Corollary 3.3.5 (`G/Z_G` is reductive, with trivial centre)
  provide such a pair; the statement does not assert its existence, so without one it
  holds vacuously. The hypothesis `IsReductive Gad` is a consequence of the others by
  Corollary 3.3.5 and is kept to match the source.
- **The action of `G^ad(K)` and the "g-conjugate" of `G(R)`.** `G^ad` acts on `G` through
  the conjugation action of `G`, which descends along `G → G/Z_G` since the centre acts
  trivially; this is `a`. A point `g ∈ G^ad(K)` acts on `G_K` by the automorphism `f`
  of the source, and the "g-conjugate" of `G(R)` is `f(G(R)) = {g · γ : γ ∈ G(R)}`, the
  set `x · G(R)` above with `x = g`. Conjugacy `f(G(R)) = h G(R) h⁻¹` for some
  `h ∈ G(K)` is the inner clause `∃ h, ∀ g, …`, an equality of subsets of `G(F)`.
- **`G(K)G^ad(R)`.** In "g ∉ G(K)G^ad(R) inside G^ad(K)" the factor `G(K)` stands for
  its image `p(G(K))` in `G^ad(K)` and `G^ad(R)` for its image in `G^ad(K)`, so the
  membership is `∃ h y, x = p(h) · y`.
- **The two directions.** The left-to-right direction is the content of
  Proposition 7.2.14 (its contrapositive: if `x ∉ p(G(F)) G^ad(R)`, the translate is not
  conjugate to `G(R)`). The right-to-left direction is elementary and is part of the
  "Equivalently" reformulation: for `y ∈ G^ad(R)` the automorphism of `G` over `R` given
  by `y` maps `G(R)` onto itself, so for `x = p(h) · y` one gets
  `x · G(R) = p(h) · G(R) = h G(R) h⁻¹`.
- **The "Equivalently" sentence.** Since `a` is an action by group automorphisms and
  `p(G(F))` is normal in `G^ad(F)` (as `z · p(h) · z⁻¹ = p(z · h)`), the subset
  `p(G(F)) G^ad(R)` is a subgroup, and `x · G(R)` is conjugate to `x' · G(R)` exactly when
  `x'⁻¹ x · G(R)` is conjugate to `G(R)`. Applying the proposition to `x'⁻¹ x` shows that
  the conjugacy classes in the orbit of `G(R)` are labelled by
  `G^ad(F)/p(G(F)) G^ad(R)`. This reformulation is a formal consequence of the stated
  equivalence for all `x` and is not stated separately.

## Scope

All objects are in universe `u`. The local field `F` is arbitrary, of characteristic
zero or positive characteristic. The statement concerns the subgroups `G(R)` and their
translates as subsets of `G(F)`; it does not mention the topology of `G(F)`, compactness,
or the maximality of `G(R)` among compact subgroups (the term "hyperspecial" of the
source). It does not state the non-split discussion before the proposition (the
reduction from automorphisms of `G_K` to points of `G^ad(K)` via Theorem 7.1.9 and the
vanishing of `H¹(R_ét, G^ad)`), Example 7.2.15, or the Iwasawa decomposition
`G^ad(K) = G^ad(R) T(K) G^ad(R)` used in the proof.

## Relation to the Library

- [`Reductive.LocalIntegerIsomorphismStatement`](LocalIntegerIsomorphismStatement.md)
  records Conrad's Theorem 7.2.16 in the same setting (reductive groups over `𝒪[F]`).
  It works with the adjoint quotient of the generic fibre over `F`
  (`IsAdjointQuotient`, a field-level interface), whereas the present statement needs the
  integral points `G^ad(R)` and therefore takes the adjoint quotient over `R`.
- [`IntegralModel`](../IntegralModel.md) describes integral points of a generic group
  through a chosen integral model and generic-fibre identification
  (`IntegralModel.integralPoints`). Here `G` is given over `R` directly, and its
  `F`-points are its points over `Spec F` as an `R`-scheme, so no identification is
  needed.
