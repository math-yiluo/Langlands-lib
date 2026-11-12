# Quotients by smooth group actions with smooth stabilizers

Author: Worker 79.

`SmoothStabilizerActionQuotientStatement` states that the fppf sheaf quotient of a scheme
by a smooth group action with smooth stabilizer scheme is an algebraic space, with a
smooth surjective quotient map. It is the quotient step of Conrad's Example 5.5 (clauses
2 and 3 of `UnipotentOrbitQuotientStatement`), in the smooth case of quotients by flat
groupoids locally of finite presentation. The module states the claim and contains no
proof.

## The statement

Notation is that of `UnipotentOrbitQuotientStatement.lean`. Let `S : Scheme.{u}`,
`G : GroupScheme S` a group scheme with `G → S` smooth (`Smooth G.X.hom`), `V : Over S`
a scheme locally of finite type over `S`, and `a : SchemeAction G V` an action. Products
are fibre products over `S`. Assume that the stabilizer scheme is smooth over `V`: the
projection `pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))`, the base change of
the action graph `(g, v) ↦ (g.v, v)` along the diagonal of `V`, is smooth. The statement
asserts:

1. *Existence.* There are an algebraic space `X` over `S` and a map `π : h_V ⟶ X` of fppf
   sheaves with `IsFppfActionQuotient a π`: `π` coequalizes `h_{G × V} ⇉ h_V` (action and
   projection) and the cofork is a colimit in fppf sheaves.
2. *Properties of every quotient.* For every algebraic space `X` over `S` and every `π`
   with `IsFppfActionQuotient a π`:
   - `IsSmooth π.hom` and `IsSurjective π.hom`: `π` is representable by schemes and each
     of its base changes along a map from a scheme is a smooth surjective morphism of
     schemes (`SmoothRelationQuotientStatement.lean`, `Basic.lean`);
   - `LocallyOfFiniteTypeOverBase X`: `X` has a surjective étale atlas by a scheme locally
     of finite type over `S` (`StructuralAtlasGeometry.lean`).

The second part is stated for every quotient because fppf quotients are only unique up to
isomorphism, and clause 3 of the target quantifies over all of them. Smoothness of `π`
gives flatness, the `IsFlat π.hom` of clause 2.

## Sources

- Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
  registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Example 5.5,
  printed p.16: "Thus, by [Del2, Prop. 3.11] there is a finitely presented algebraic
  space `X` over `k` and a faithfully flat map `V_d → X` that identifies `X` with the fppf
  sheaf quotient of `V_d` by its `G`-action".
- The Stacks Project, Morphisms of Algebraic Stacks, Proposition 101.28.9 (Tag 06QJ),
  proof of (2) ⇒ (1), and Bootstrap, Lemma 80.11.7 (Tag 06PH), registered source
  `stacks-free-action-stabilizer-quotient-06PH-06QJ-2026-11-10`, SHA-256
  `d727706c88620e0d0f345ed4316cc7aa33499138e0eed0f9cad6c6a2bb2f2ddc`, files
  `tag-06QJ.html` and `tag-06PH.html`. For a groupoid `(U, R, s, t, c)` whose stabilizer
  `G → U` is flat and locally of finite presentation, the proof lets `G` act freely on
  `R` by `(g, r) ↦ c(g, r)`; "Hence `R' = R/G` is an algebraic space and the quotient
  morphism `π : R → R'` is surjective, flat, and locally of finite presentation by
  Bootstrap, Lemma 80.11.7." The maps `s', t' : R' → U` are flat and locally of finite
  presentation, `j' = (t', s') : R' → U × U` is an equivalence relation, "Hence
  Bootstrap, Theorem 80.10.1 shows that `X = U/R'` is an algebraic space."
- The Stacks Project, Bootstrap, Theorem 80.10.1 (Tag 04S6), and Descent and Algebraic
  Spaces, Remark 74.20.5 (Tag 06FC), registered source
  `stacks-smooth-quotient-local-finite-type-2026-11-01`, SHA-256
  `ea18197c7ff281b249564e51225bb653f30bbf175c60df3c275a9a3c15e14072`, files `04S6.html`
  and `06FC.html`. Theorem 80.10.1: "`F = U/R` where `(U, R, s, t, c)` is a groupoid in
  algebraic spaces over `S` such that `s, t` are flat and locally of finite presentation,
  and `j = (t, s) : R → U ×_S U` is an equivalence relation" implies that `F` is an
  algebraic space. Remark 74.20.5: local finite type is smooth local on the source.
- The Stacks Project, Descent, Lemma 35.14.5 (Tag 05B5), and Descent and Algebraic
  Spaces, Lemma 74.8.4 (Tag 0AHE), registered source
  `stacks-smooth-etale-source-descent-2026-11-02`, SHA-256
  `48d0329a769c0531881a211fed43bfd95306a602e134e33ca11d91c03e15f0b9`, files `05B5.html`
  and `0AHE.html`: for `f : X → Y` over a base with structure maps `p` and `q`, "Assume
  that `f` is surjective, flat, and locally of finite presentation, `p` is smooth (resp.
  étale). Then `q` is smooth (resp. étale)." Lemma 74.8.4 is the same for algebraic
  spaces.

## Derivation (provenance: derived)

The statement specializes the proof of Proposition 101.28.9 to the groupoid
`R = G × V ⇉ V` of the action, with `s` the projection and `t = a`, and to smooth rather
than flat locally finitely presented data. It is not stated in this form in a source.

- `s : G × V → V` is smooth as a base change of `G → S`, and `t` is smooth by symmetry
  through the inverse of `G`. The stabilizer of the groupoid is the stabilizer scheme
  above, smooth over `V` by assumption.
- As in Proposition 101.28.9, `R' = R/Stab` is an algebraic space and `R → R'` is a
  smooth surjective `Stab`-torsor (Lemma 80.11.7, with smoothness because `Stab` is
  smooth). By Lemma 74.8.4, `s', t' : R' → V` are smooth. The map
  `j' : R' → V × V` is a monomorphism and an equivalence relation, the image of the action
  graph. By Theorem 80.10.1, `V/R'` is an algebraic space. As a sheaf it is the
  coequalizer of `R ⇉ V`, that is, the fppf quotient of `V` by `G`. This gives (1). The
  smooth case of Theorem 80.10.1 is the Library's `SmoothRelationQuotientStatement`.
- For any quotient `π : V → X`, `V ×_X V ≅ R'` and `R' → V` is smooth and surjective. As
  `π` is fppf locally on `X` a base change of `R' → V`, it is smooth and surjective. The
  map `π` is representable by schemes because `X` has a representable diagonal (the
  Library's `AlgebraicSpace.representable_from_scheme`). Since `V` is locally of finite
  type over `S` and `π` is smooth and surjective, `X` is locally of finite type over `S`
  (Remark 74.20.5). This gives (2).

In Example 5.5 the group is unipotent over a field of characteristic zero, hence smooth
(Cartier), and its stabilizer on the stratum is smooth
(`UnipotentOrbitStabilizerSmoothStatement`). Conrad cites [Del2, Prop. 3.11] instead; the
task constraint permits the Stacks route. The names of the declarations are derived here.
