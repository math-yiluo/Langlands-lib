# The torsor of relative Levi subgroups

`Langlands.GroupScheme.RelativeLeviTorsorStatement.{u}` states the torsor
realization of the actual relative Levi moduli. It is a proposition definition,
not a proof of the theorem.

For every base scheme `S : Scheme.{u}`, group schemes `G`, `P` and `U` over
`S`, a relative parabolic `i : P → G` with reductive `G`, and a supplied
relative unipotent radical `r : U → P`, the proposition asserts the existence
of an actual `S`-scheme `X`, an actual action `ModObj U.X X`, and
`ρ : RelativeLevi.ModuliRepresentation P X`. All geometric objects remain in
the same arbitrary universe `u`; the all-test image and representing data may
occupy a higher type universe.

The representing correspondence identifies the `T`-points of `X`, on every
scheme test `T → S`, with the all-test subgroup images of actual homomorphisms
`L → P_T` satisfying the existing `IsRelativeLeviSubgroup`. Its naturality
field is literal subgroup base change followed by the canonical comparison of
ambient pullbacks. Equality is equality of subgroup functors, independent of
a presenting group scheme or inclusion. The condition `ρ.IsEquivariant r`
requires the action on these points to be conjugation by the image under `r`
of the corresponding `T`-point of `U`. Thus the action and the moduli points
are related by the actual conjugation operation.

The remaining conclusions are `Flat X.hom`, `Surjective X.hom`,
`QuasiCompact X.hom`, and `IsIso (ModObj.leftSMul U.X X)`. The first three
say that the structure map `X → S` is faithfully flat and quasi-compact.
The last says that the actual morphism
`U ×_S X → X ×_S X`, `(u, x) ↦ (u • x, x)`, is an isomorphism.
Together these are the fpqc torsor conditions. In particular, the conclusion
requires local existence as well as simple transitivity.

There is no affine-base hypothesis, global Levi subgroup, or section in the
premises. If a section is subsequently supplied, the proved
`RelativeLevi.ModuliRepresentation.ofSection_exists_presentation` extracts a
Levi inclusion over `S`, using the canonical identity-pullback isomorphism;
`exists_isRelativeLeviSubgroup_of_section` retains just the existence claim.
These implications are already proved in `ModuliRepresentation`; this module
asserts no section and uses no affine torsor-vanishing assertion.

The original source is Brian Conrad, *Reductive group schemes* (2014),
Definition 5.4.2, p.174, and Corollary 5.4.6 with its proof, p.178.
Source ID: `conrad-2014-reductive-group-schemes`; SHA-256:
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Corollary 5.4.6 represents `Lev(P)`, equipped with the radical's actual
conjugation action, by a radical torsor. Its proof uses étale-local Levi
existence, simple transitivity of conjugation, and affine descent. The Lean
target records the resulting fpqc torsor properties rather than choosing a
specific étale trivializing cover. This is a consequence of the source's
torsor realization and does not require a global trivialization. Corollary
5.4.8, p.179, then uses affine vanishing to get a point and hence a Levi; that
later step is outside this proposition.
