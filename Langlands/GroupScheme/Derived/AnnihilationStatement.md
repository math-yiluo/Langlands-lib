# Derived subgroups and commutative annihilation: statement targets

This module supplies two exact `Prop`-valued statement definitions and their conjunction
on the actual Library group schemes. These are unproved targets. The module supplies
neither a proof of annihilation nor a chosen representing scheme.

The original source is J. S. Milne, *Algebraic Groups* (2017), Corollary 6.19(d),
printed p.129 / PDF p.145, registered as `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Its proof on printed p.130 / PDF p.146 uses the faithfully flat local commutator
generation of 6.19(c). The character target is the specialization to the
multiplicative group, written using the Library's additive character convention.
The conjunction is an internal packaging of these two targets.

All three declarations are in the namespace `Langlands.GroupScheme`:

- `DerivedCommutativeAnnihilationStatement` quantifies every field `k`, every actual
  group scheme `G` over `Spec k` with `IsAffineHom G.X.hom` and
  `LocallyOfFiniteType G.X.hom`, every actual `d : D ⟶ G` satisfying
  `IsDerivedSubgroup d`, and every commutative group scheme `H` over `Spec k`
  with the same affine and locally finite type hypotheses. For every commutative
  `k`-algebra `R`, set `b = Spec.map (algebraMap k R)`. Every actual
  `f : G_R ⟶ H_R` must satisfy `d_R ≫ f = 1`, where the base changes use
  `GroupScheme.baseChange` and `CommGroupScheme.baseChange`.
- `DerivedCharacterAnnihilationStatement` has the same hypotheses on `k`, `G`
  and `d`, and the same arbitrary algebra `R`. Every
  `χ : rationalCharacters G_R` must satisfy `characterRestrict d_R χ = 0`.
  The target of such a character is the actual multiplicative group over
  `Spec R`. The published `Gm.baseChangeIso` identifies it with the actual
  scalar extension of the multiplicative group over `Spec k`.
- `DerivedAnnihilationStatement` is exactly the conjunction of these two
  declarations. It does not assert either conjunct.

Here commutativity is carried by the actual `CommGroupScheme` group object,
and therefore holds on every test scheme. The algebra `R` need not be a field,
reduced, or of finite type. The morphism equality in the first target is to the
trivial group-scheme homomorphism. In the character target, `rationalCharacters`
is an additive presentation of the homomorphisms to the multiplicative group,
so its zero is the trivial character; `rationalCharacters.comp_zero` and
`characterEval_zero` give identity value on every test scheme. These formulations
include all test schemes, including nonreduced tests.

The fields, algebras and schemes are in the ambient universe `u`, and the
declarations are universe-polymorphic. No smoothness, connectedness, perfection
or splitting hypothesis is imposed. Affineness supplies quasi-compactness,
so the displayed locally finite type hypotheses give the finite-type scope of
the source. No further hypothesis is imposed on `D`: its closed inclusion in
the affine finite-type `G` supplies the corresponding geometric properties.

The prerequisite `derivedSubgroup` and `IsDerivedSubgroup` definitions in
`Derived.Basic` reformulate the smallest closed subgroup containing the
commutator morphism, as characterized by Milne 6.16–6.18. Both targets quantify
over an actual exhibiting `d`; they do not assume that `d_R` is a derived
subgroup, or assume any annihilation property. Unconditional existence of such
a `d` is the separate closed-representability statement in
`Derived.StructureStatement`.

The targets require substantive later proofs. The elementary intersection lemmas
do not establish faithfully flat local generation by commutators or its
scalar-extension annihilation consequence, and neither is proved here. Milne
Remark 6.23, printed p.131 / PDF p.147, distinguishes the scheme-theoretic derived
group from the abstract commutator subgroup of rational points. This module
asserts no equality between these groups, quotient formula for rational points,
or surjectivity on rational points.

The complete retained official errata HTML
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read. Its displayed Chapter 6 correction concerns Example 6.48. The
commented-out earlier caution about 6.19(c)–(e) is not a displayed correction;
it is not used to add a smoothness hypothesis to these targets.

Authorship: Worker 1173 authored this statement pair. Worker 153 supplied the
prerequisite derived-subgroup interface and coordinated the statement division.
