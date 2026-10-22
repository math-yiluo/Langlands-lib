# Characterization and coherence of relative differential maps

`Langlands.Scheme.RelativeDifferentialsMapLawsStatement.{u}` is a proposition
with three clauses for arbitrary schemes in universe `u`:

1. A morphism from the actual pulled-back relative differential sheaf is
   `relativeDifferentialsMap g w` if and only if its adjoint, postcomposed
   with the distinguished derivation on the target of `g`, is the
   precomposition of the distinguished derivation on the source of `g`.
2. For an identity scheme morphism, the induced differential map is the
   component of Mathlib's `Modules.pullbackId` isomorphism in its forward
   direction.
3. For composable morphisms `g : X ⟶ Y` and `h : Y ⟶ Z` over the same base,
   the map for `g ≫ h` equals the map for `h` pulled back along `g`, followed
   by the map for `g`, with `Modules.pullbackComp g h` in its inverse
   direction identifying the source objects.

Every clause uses the actual constructed `relativeDifferentials` and its
induced maps. The only hypotheses are the stated commuting triangles;
there is no geometric restriction or assumed universal property. The
composite commuting triangle is proved from the two input triangles.

The characterization is Stacks Project Lemma 17.28.12 (tag 08RU), specialized
to schemes over a fixed base. The composition clause is Lemma 17.28.13
(tag 01UW) under the same specialization; its displayed canonical
identification is made explicit with the Mathlib pullback composition
isomorphism. The identity clause follows from the unique characterization
by taking the identity morphism. Scheme specialization is Definition
29.33.1 (tag 01UM). These facts explain the derived provenance of the
combined proposition, which is a packaging of those standard properties.

Registered source: `stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
files `08RL.html` and `01UM.html`. This module only states the proposition;
its proof is in `RelativeDifferentialsMapsCoherence`.
