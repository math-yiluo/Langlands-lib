# Restriction of actual unramified characters

Author: Worker 200.

This is a derived functorial construction for the actual unramified character
groups used in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), I.1, printed pp.239–240
(PDF pp.5–6), source ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
That passage uses restriction from \(X(G)\) to \(X(A_G)\).
The present construction supplies the restriction map for any morphism of
actual affine group schemes. Finiteness of its kernel, its surjectivity,
algebraic or manifold structure, and measure normalization are separate
obligations.

The source's common norm kernel and character description also appear in
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.3–V.2.6, printed pp.105–108 (PDF pp.111–114), source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The continuity and functoriality proofs below are derived from the published
point and character constructions, rather than quoted assertions about a
new character space.

## Common norm kernel

Let \(F:\mathrm{Type}\ u\) have `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`. All group schemes are
the shared `GroupScheme (Spec (CommRingCat.of F))`.
For an actual morphism \(f:H\to G\),
`rationalCommonNormKernel_le_comap` proves
\[
 H^1\ \leq\ f(F)^{-1}(G^1),
\]
where \(H^1\) and \(G^1\) are the published
`rationalCommonNormKernel H` and `rationalCommonNormKernel G`.
For a rational character \(\chi\) of \(G\), its restriction
`GroupScheme.characterRestrict f chi` is a rational character of \(H\).
The already proved evaluation identity therefore gives norm one at every
point of \(H^1\). This proves the inclusion without any point topology,
affineness, finite generation, reductivity, splitness or injectivity premise.

## Actual continuous restriction

For affine \(H\) and \(G\), the module installs exactly the published
`rationalPointTopology F H.X` and `rationalPointTopology F G.X`.
`rationalContinuousPointsMap f` bundles the existing
`GroupScheme.rationalPoints.map f` as a continuous multiplicative
homomorphism. Its continuity is the published
`continuous_rationalPointMap` for postcomposition between affine schemes;
the group law is the existing point-map law.

`rationalUnramifiedCharacterRestrict f` is a continuous multiplicative map
\[
 X(G)\ \longrightarrow\ X(H),\qquad
 \chi\ \longmapsto\bigl(h\mapsto\chi(f(F)(h))\bigr).
\]
Both character groups are the existing `unramifiedCharacters` for the actual
families `fun chi => (rationalNormCharacters _ chi).toMul`, with their
compact-open subspace topologies. The common-kernel inclusion proves that
precomposition is unramified. Mathlib's continuity of precomposition on
continuous homomorphisms proves continuity, followed by passage to the
subspace. `rationalUnramifiedCharacterRestrict_apply` is the exact pointwise
formula.

`rationalUnitaryUnramifiedCharacterRestrict f` restricts the same construction
to the existing `unitaryUnramifiedCharacters`: norm one is preserved simply
by evaluating the original norm-one condition at \(f(F)(h)\).
Its `_apply` theorem gives the same values.
`rationalUnitaryUnramifiedCharacterRestrict_coe` proves compatibility with
forgetting norm-one membership.

`rationalUnramifiedCharacterRestrict_id` and
`rationalUnramifiedCharacterRestrict_comp` prove the identity and composition
laws. The proofs use extensionality and identity and associativity of
composition of the actual scheme points. Thus the map is contravariant in
the group scheme, with no choices of character bases.

## Scope

There is no characteristic restriction, and the construction applies without
connectedness, reductivity, finite type, a split torus or a central morphism.
In the intended split-center application, take the actual map \(A_G\to G\).
This unit proves no finite-index image, restriction-kernel finiteness,
extension of characters, Haar identity, representation-stabilizer or orbit
finiteness, or Plancherel assertion.

Local instances use explicit module-specific names to prevent generated-name
collisions under joint imports. Their types, bodies and local scope are
unchanged.
