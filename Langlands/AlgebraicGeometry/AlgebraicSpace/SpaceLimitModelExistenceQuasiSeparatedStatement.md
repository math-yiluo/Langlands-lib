# Models of quasi-separated algebraic spaces along cofiltered limits of affine schemes

Author: Worker 208.

This target states the existence part of Brian Conrad's claim, in *Weil and
Grothendieck approaches to adelic points* (31 December 2011), printed p.13
(start of Section 5): "Theorem 3.4 is valid with finitely presented algebraic
spaces in place of finitely presented schemes". Conrad says this follows by an
étale descent argument and refers to the proof of [Ols, Prop. 2.2].
Theorem 3.4(1) (printed p.5) begins: for a directed system of rings `A_i` with
colimit `A` and a finitely presented `A`-object `X`, "there exists some `i₀`
and a finitely presented `A_{i₀}`-scheme `X_{i₀}` whose base change over `A` is
isomorphic to `X`". Finitely presented algebraic spaces in Conrad's sense are
quasi-compact and quasi-separated, so this target is stated for
quasi-separated spaces. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`; pages 5
and 13 were reread for this target.

`SpaceLimitModelExistenceQuasiSeparated` is a proposition; no proof is
supplied here. It quantifies over the following data, all in one arbitrary
universe `u`:

- a small cofiltered category `I`;
- a diagram `D` of affine schemes indexed by `I`, with an actual limit cone
  `c`;
- an algebraic space `Y` over the limit scheme `c.pt`.

It assumes that:

- `Y` is quasi-separated: its diagonal is representable and every represented
  projection of it is a quasi-compact scheme morphism;
- `Y` has a surjective étale scheme atlas whose structure map to `c.pt` is
  locally of finite presentation and quasi-compact.

It asserts a stage `i` and an algebraic space `X` over `D.obj i` with three
properties:

- `X` is quasi-separated;
- `X` has a surjective étale scheme atlas whose structure map is locally of
  finite presentation and quasi-compact;
- the base change of `X` along the cone leg `c.π.app i`, in the Library's
  `baseChange`, is isomorphic to `Y` as algebraic spaces over `c.pt`.

In Conrad's ring setting, `D` is the diagram of spectra of a directed system
of rings `A_i` and `c.pt` is the spectrum of its colimit `A`. A finitely
presented algebraic space over `A` is quasi-separated and has an atlas of the
stated kind. The general cofiltered diagram of affine schemes is a derived
generalization of the ring setting. The statement follows Stacks Project
Lemma 70.7.1 (Tag 07SK), which treats quasi-compact and quasi-separated
algebraic spaces of finite presentation.

The Library's `SpaceLimitModelExistence` is the analogous statement with
separatedness in both the hypothesis on `Y` and the conclusion on `X`. Neither
statement is derived from the other here: this target weakens the hypothesis
and also weakens the conclusion.

This target states only existence of a model. It does not state uniqueness of
models, descent of morphisms (stated separately as
`SpaceLimitMorphismDescentQuasiSeparated`), descent of separatedness or other
properties, or any arithmetic specialization to rings of `S`-integers.
