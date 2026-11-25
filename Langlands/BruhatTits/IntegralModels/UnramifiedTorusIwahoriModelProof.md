# Proof of connected torus Iwahori models over the maximal unramified integers

Lean module: `Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelProof`.

`Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriModel` proves the
unchanged published proposition `UnramifiedTorusIwahoriModelStatement.{u}` at
arbitrary universe `u`. For every nonarchimedean local field `F`, write
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`. Let `T` be an affine
commutative group scheme over `K` and let `L` be a finite Galois intermediate
field of `SeparableClosure F / K` that splits `T`. Then `T` has a smooth model
`M` over `O` with geometrically connected fibres whose integral points equal
`torusNormIwahori K L (intermediateValuation F L) T`, the norm-defined Iwahori
subgroup `T(K)⁰`. The exact formulation and provenance are in the statement's
paired Markdown, `UnramifiedTorusIwahoriModelStatement.md`.

## The Lean proof

The proof is a single term. It applies the published conditional reduction
`unramifiedTorusIwahoriModelAssembly`, which proves
`UnramifiedTorusIwahoriModelAssemblyStatement`. That statement is the
implication from four inputs to the target. The inputs are supplied, in this
order, by these published Library theorems:

1. `IntegralModel.SmoothHomExtensionStatement` is proved by
   `Langlands.GroupScheme.IntegralModel.smoothHomExtension`
   (module `Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof`).
2. `UnramifiedTorusBoundedModelStatement` is proved by
   `unramifiedTorusBoundedModel`
   (module `Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof`).
3. `UnramifiedTorusConnectedBoundStatement` is proved inline, by applying the
   published reduction `unramifiedTorusConnectedBoundAssembly`
   (module `Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly`)
   to the published proofs of its three premises:
   - `UnramifiedTorusBoundedModelStatement`, by `unramifiedTorusBoundedModel`;
   - `UnramifiedTorusNeutralSurjectivityStatement` (KP Corollary B.8.6), by
     `unramifiedTorusNeutralSurjectivity`
     (module `Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityProof`);
   - `UnramifiedTorusNormPresentationStatement`, by
     `unramifiedTorusNormPresentation`
     (module `Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof`).
4. `UnramifiedTorusIwahoriConnectedImageStatement` is proved by
   `unramifiedTorusIwahoriConnectedImage`
   (module `Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof`).

Every result is used at the same universe `u`, so no universe is restricted.
No hypothesis is added and the conclusion is not weakened. The module adds no
definition or statement and uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## How the argument runs

The mathematics is in the two assemblies and their inputs. Their paired
Markdown files describe it in detail.

Input 2 gives a smooth model `M` of `T` whose integral points are the maximal
bounded subgroup `T(K)¹`. Its relative identity component `M⁰` is smooth with
geometrically connected fibres. This is the candidate model.

The upper bound `M⁰(O) ⊆ T(K)⁰` is input 3. Its reduction chooses a norm
presentation `q : S → T` of tori whose kernel is a torus, with
`q(S(K)¹) ⊆ T(K)⁰`. Any connected smooth model of `T` factors through the
neutral model of `T`. The neutral integral points of `T` lift along `q` to
neutral integral points of `S` (KP B.8.6). Those lie in `S(K)¹`, and `q` carries
`S(K)¹` into `T(K)⁰`.

The lower bound `T(K)⁰ ⊆ M⁰(O)` uses input 4. It supplies a smooth model `W`
with geometrically connected fibres and a homomorphism `n` that carries `W(O)`
onto `T(K)⁰`. In the source, `W` is the Weil restriction of a split torus and
`n` is the norm. Since `T(K)⁰ ⊆ T(K)¹ = M(O)`, input 1 extends `n` to a model
homomorphism `W → M`. Because `W` has geometrically connected fibres, this
homomorphism factors through `M⁰`.

## Sources and provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Proposition B.8.4(3), Remark B.8.5 and Corollaries B.8.6–B.8.7, printed
pp. 681–683 / PDF pp. 712–714, with the argument of Proposition B.8.8(3),
printed pp. 683–684 / PDF pp. 714–715. The source works with finite-type and lft Néron
models. The Lean route replaces their mapping properties by the smooth
homomorphism-extension criterion (input 1) and the explicit bounded model
(input 2), as explained in `UnramifiedTorusIwahoriModelAssembly.md`. The
registered corrections `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, amend
Appendix B only in Section B.10.
