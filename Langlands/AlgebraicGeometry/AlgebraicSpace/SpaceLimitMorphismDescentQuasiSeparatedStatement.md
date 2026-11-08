# Morphisms of quasi-separated algebraic spaces along cofiltered limits of affine schemes

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
spaces, with only quasi-separatedness of the source. Finitely presented
algebraic spaces in Conrad's sense are quasi-compact and quasi-separated, so
this is the generality of his claim. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`; pages 5
and 13 were reread for this target.

`SpaceLimitMorphismDescentQuasiSeparated` is a proposition; no proof is
supplied here. Its data are those of the Library's `SpaceLimitMorphismDescent`.
It quantifies over a small cofiltered category `I`, a diagram `D` of affine
schemes indexed by `I`, an affine base scheme `S`, a natural transformation
`t` from `D` to the constant diagram `S`, an actual limit cone `c` of `D`,
and a morphism `p : c.pt ⟶ S` with `c.π.app i ≫ t.app i = p` for every `i`.
Everything lives in one arbitrary universe `u`. For two algebraic spaces `X`
and `Z` over `S`, `baseChange g X` is the Library's base change of `X` along a
scheme morphism `g` into `S`. Its sections over a test scheme `W` over the
source of `g` are the sections of `X` over `W` viewed over `S` through
`Over.map g`.

The hypotheses are:

- `IsQuasiSeparated X`: the diagonal of `X` is representable and every
  represented projection of it is a quasi-compact scheme morphism.
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
algebraic space over `R` is quasi-separated, has a quasi-compact atlas and has
a locally finitely presented atlas, so it satisfies all three hypotheses. The
general cofiltered diagram, the separate hypotheses on source and target, and
the affine base are a derived generalization of Conrad's finitely presented
setting. They follow the Stacks Project's characterization of algebraic spaces
locally of finite presentation by limit preservation, which needs only that
the source is quasi-compact and quasi-separated.

Stacks Project Lemma 70.7.1 (Tag 07SK) proves, for algebraic spaces of
finite presentation over a limit of quasi-compact and quasi-separated spaces
with affine transition maps, that the category of such spaces over the limit
is the colimit of the categories at the stages. Its fullness part, that every
morphism over the limit comes from a morphism at some stage, is the analogue
of this target there.

The Library's `SpaceLimitMorphismDescent` is the same statement with
`IsSeparated X` in place of `IsQuasiSeparated X`. Mathematically a separated
space is quasi-separated, so this target is the more general one; no
implication between the two Lean propositions is proved here.

This target states only existence of a descended morphism. It does not state
uniqueness or eventual equality of descended morphisms, descent of algebraic
spaces themselves (existence of models), descent of properties of morphisms,
or any arithmetic specialization. Those remain separate obligations.
