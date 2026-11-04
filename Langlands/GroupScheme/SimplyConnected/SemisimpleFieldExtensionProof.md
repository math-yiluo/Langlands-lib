# Semisimplicity under arbitrary field extension

Author: Worker 1294.

The theorem `Langlands.GroupScheme.isSemisimpleFieldExtension` proves exactly
the published `Langlands.GroupScheme.IsSemisimpleFieldExtensionStatement.{u}`
from `Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`.

For arbitrary fields `k K : Type u`, an `Algebra k K`, and an actual group
scheme `G` over `Spec k`, it sends `IsSemisimple G` to semisimplicity of

```lean
(GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G
```

The extension is unrestricted: it may be transcendental or inseparable, the
fields may be imperfect, and either characteristic is allowed. The universe
`u` is arbitrary. The theorem has no premise beyond those in the statement.

## Implemented proof

The Library predicate `IsSemisimple G` has two fields:
`isConnectedReductive : IsConnectedReductive G` and
`hasFiniteCenter : HasFiniteCenter G`. The proof constructs these two fields
for the actual pullback.

Apply the published `connectedReductiveFieldExtensionStatement` from
`Langlands.GroupScheme.Reductive.FieldExtensionProof` to `k`, `K`, `G` and
`hG.isConnectedReductive`. Its conclusion supplies connected reductivity of
the pullback. The geometric connectedness and radical-preservation arguments
are implemented in that theorem and its published dependencies.

Apply the published `HasFiniteCenter.baseChange` from
`Langlands.GroupScheme.Reductive.FiniteCenterBaseChange` to
`hG.hasFiniteCenter` along `algebraBaseMap k K`. This base map is
definitionally `Spec.map (CommRingCat.ofHom (algebraMap k K))`, so the two
conclusions concern exactly the same group scheme.

The finite-centre helper pulls back the actual centre representative and
its inclusion, identifies its range with the entire all-test centre, and
uses stability of finite morphisms under pullback. It retains the full
scheme-theoretic centre, including nonreduced structure. No smoothness or
reducedness of the centre is assumed.

## Provenance and dependencies

This is derived assembly from two proved Library results and the unchanged
definition of `IsSemisimple`. The connected-reductivity theorem and the
finite-centre helper are imported by their Lean module names. The latter
uses the published full-centre base-change proof. No definition, target
statement or imported file is changed.

The original mathematical sources are recorded in the statement's Markdown:
Milne, *Algebraic Groups* (2017), Proposition 19.5, printed pp.398–399
(PDF pp.414–415), states semisimplicity invariance under arbitrary extension;
Propositions 19.10 and 19.13, printed p.400 (PDF p.416), give the finite-centre
characterization and reductivity invariance used here. CGP, *Pseudo-reductive
groups*, second edition (2015), the discussion after Definition A.1.9 and
Definition A.1.10, printed p.469 (PDF p.495), describes compatibility of full
centres with ground-field extension, including the nonreduced centre `μ_p`
of `SL_p`. These registered original passages and the complete retained
Milne errata snapshot of 2026-11-02 were read during this task. The errata
do not change Propositions 19.5, 19.10 or 19.13.
