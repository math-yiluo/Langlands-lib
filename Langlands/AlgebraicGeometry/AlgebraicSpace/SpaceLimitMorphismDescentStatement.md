# Morphisms of algebraic spaces along cofiltered limits of affine schemes

Author: Worker 208.

This target states the existence half of the morphism part of Brian Conrad's
claim, in *Weil and Grothendieck approaches to adelic points* (31 December
2011), printed p.13 (start of Section 5): "Theorem 3.4 is valid with finitely
presented algebraic spaces in place of finitely presented schemes". Conrad
says this follows by an étale descent argument and refers to the proof of
[Ols, Prop. 2.2]. Theorem 3.4(1) (printed p.5) says that for finitely
presented `A_{i₀}`-objects `X_{i₀}`, `Y_{i₀}` and a directed system of rings with
colimit `A`, the natural map `lim Hom_{A_i}(X_i, Y_i) → Hom_A(X, Y)` is
bijective. This target is the surjectivity half of that map for algebraic
spaces. Section 5 uses
it on printed p.17 to topologize `X(A_F)` functorially for a separated
algebraic space `X` of finite type over a global field `F`, independently of
the chosen model. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`; pages 5,
13 and 17 were reread for this target.

`SpaceLimitMorphismDescent` is a proposition; no proof is supplied here. It
quantifies over a small cofiltered category `I`, a diagram `D` of affine
schemes indexed by `I`, an affine base scheme `S`, a natural transformation
`t` from `D` to the constant diagram `S`, an actual limit cone `c` of `D`,
and a morphism `p : c.pt ⟶ S` with `c.π.app i ≫ t.app i = p` for every `i`.
Everything lives in one arbitrary universe `u`. For two algebraic spaces `X`
and `Z` over `S`, `baseChange g X` is the Library's base change of `X` along a
scheme morphism `g` into `S`. Its sections over a test scheme `W` over the
source of `g` are the sections of `X` over `W` viewed over `S` through
`Over.map g`.

The hypotheses are:

- `IsSeparated X`: the diagonal of `X` is a closed immersion.
- `HasAtlasProperty QuasiCompact X`: some surjective étale scheme atlas of
  `X` is quasi-compact over `S`.
- `LocallyOfFinitePresentationOverBase Z`: some surjective étale scheme atlas
  of `Z` is locally of finite presentation over `S`.

For every morphism `φ` from the base change of `X` to the base change of `Z`
along `p`, the statement asserts a stage `i` and a morphism `φi` from the base
change of `X` to the base change of `Z` along `t.app i`. They agree on every
test scheme `W` over the limit, in the following sense. View `W` over the
stage `D.obj i` through `c.π.app i`. Then `W` over `S` through `p` and through
`c.π.app i ≫ t.app i` are the same scheme with equal structure maps, related
by identity morphisms over `S`. Evaluating `φ` on a section `x` over `W`
equals moving `x` along the identity, evaluating `φi`, and moving back.
Equivalently, the base change of `φi` to the limit is `φ`, written on
sections without an iterated base-change isomorphism.

In Conrad's ring setting, `D` is the diagram of spectra of a filtered system
of `R`-algebras `A_i` with colimit `A`, and `S = Spec R`. A finitely presented
separated space over `R` has a quasi-compact atlas and a locally finitely
presented atlas, so it satisfies both hypotheses. The general cofiltered
diagram, the separate hypotheses on source and target, and the affine base
are a derived generalization of Conrad's finitely presented setting. They
follow the Stacks Project's characterization of algebraic spaces locally of
finite presentation by limit preservation, which needs only that the source is
quasi-compact and quasi-separated. Separatedness of `X` and affineness of `S`
are kept so that an affine atlas of `X` has an affine kernel pair, and the
proof can use only diagrams of affine schemes.

This target states only existence of a descended morphism. It does not state
uniqueness or eventual equality of descended morphisms, descent of algebraic
spaces themselves (existence of models), descent of properties of morphisms,
or any arithmetic specialization. Those remain separate obligations.
