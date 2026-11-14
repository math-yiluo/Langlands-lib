# Reductive Kottwitz existence from four structural inputs

`ReductiveKottwitzRemainingInputsStatement` is an internal reduction of
`ReductiveKottwitzExistenceStatement` to four existing Library propositions:

- `FundamentalInertiaMapStatement`, the specification and functor laws of
  the selected fundamental-inertia maps;
- `Langlands.GroupScheme.ZExtensionPointSurjectivityStatement`,
  surjectivity on field points for every actual z-extension;
- `CentralTorusInertiaExactnessStatement`, right exactness of the actual
  inertia maps for central torus quotients;
- `Langlands.GroupScheme.ZExtensionCommonDominationStatement`, a common
  dominating actual z-extension with both commuting triangles.

The declaration is an implication from these four propositions to the full
target. It does not assert any of these premises or the target unconditionally.
The fields, coefficient towers, groups and selected maps in the conclusion
are exactly those of the unchanged `ReductiveKottwitzExistenceStatement`.
No substitute map or supplied Kottwitz square is introduced.

`reductiveKottwitzExistence_of_remaining_inputs` proves this implication.
For each local field, coefficient tower and connected reductive group, it
applies `reductiveKottwitzExistenceAt_of_torus_existence`. The point
surjectivity premise is specialized to the maximal unramified extension.
The published `CentralTorusInertiaExactnessStatement.zExtension`
specialization supplies inertia-map surjectivity as the first conjunct;
its kernel-image conjunct is unnecessary for this final application.
The common-domination premise supplies the two commuting triangles.

The imported reductions already supply the other inputs. Published torus
existence and norm naturality give the upstairs Kottwitz construction and
its naturality through actual cocenters. The canonical fundamental-group
comparison, its map consequence, and both torus comparison proofs identify
the targets. Published z-extension existence supplies a first actual
extension. Naturality annihilates the central-torus point kernel.
Surjective homomorphism descent gives one square, and common domination
compares such descents to obtain every square. Point surjectivity gives
uniqueness, and upstairs and target surjectivity give surjectivity of the
selected reductive map. The same naturality square proves agreement with
the simply-connected-derived construction.

This is a derived internal composition of the imported statements and
proved reductions. Its mathematical route follows Kaletha–Prasad (2023),
Lemma 11.5.1, printed p. 430 / PDF p. 461; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The four-premise interface is
an implementation boundary, not a separate assertion made in that source.
