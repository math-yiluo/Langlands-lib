# Models of algebraic spaces along cofiltered limits of affine schemes

Author: Worker 208.

This target states the existence part of Brian Conrad's claim, in *Weil and
Grothendieck approaches to adelic points* (31 December 2011), printed p.13
(start of Section 5): "Theorem 3.4 is valid with finitely presented algebraic
spaces in place of finitely presented schemes". Conrad says this follows by an
étale descent argument and refers to the proof of [Ols, Prop. 2.2].
Theorem 3.4(1) (printed p.5) begins: for a directed system of rings `A_i` with
colimit `A` and a finitely presented `A`-object `X`, "there exists some `i₀`
and a finitely presented `A_{i₀}`-scheme `X_{i₀}` whose base change over `A` is
isomorphic to `X`". Theorem 3.4(2) adds that separatedness is acquired at some
stage. Section 5 uses the space version on printed p.17 to topologize `X(A_F)`
for every separated algebraic space `X` of finite type over a global field `F`,
through a model over some ring of `S`-integers. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`; pages 5,
13 and 17 were reread for this target.

`SpaceLimitModelExistence` is a proposition; no proof is supplied here. It
quantifies over the following data, all in one arbitrary universe `u`:

- a small cofiltered category `I`;
- a diagram `D` of affine schemes indexed by `I`, with an actual limit cone
  `c`;
- an algebraic space `Y` over the limit scheme `c.pt`.

It assumes that:

- `Y` is separated: its diagonal is a closed immersion;
- `Y` has a surjective étale scheme atlas whose structure map to `c.pt` is
  locally of finite presentation and quasi-compact.

It asserts a stage `i` and an algebraic space `X` over `D.obj i` with three
properties:

- `X` is separated;
- `X` has a surjective étale scheme atlas whose structure map is locally of
  finite presentation and quasi-compact;
- the base change of `X` along the cone leg `c.π.app i`, in the Library's
  `baseChange`, is isomorphic to `Y` as algebraic spaces over `c.pt`.

In Conrad's ring setting, `D` is the diagram of spectra of a directed system
of rings `A_i` and `c.pt` is the spectrum of its colimit `A`. A separated
finitely presented algebraic space over `A` has an atlas of the stated kind.
The general cofiltered diagram of affine schemes is a derived generalization
of the ring setting. Separatedness of `Y` is assumed so that an affine atlas
has an affine relation scheme. Conrad works with quasi-separated spaces;
separated spaces are the case used for the adelic topology on printed p.17.

This target states only existence of a model. It does not state uniqueness of
models, descent of morphisms (stated separately as
`SpaceLimitMorphismDescent`), descent of other properties, or any arithmetic
specialization to rings of `S`-integers.
