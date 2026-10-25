# Pullback tensor associativity

The theorem `Langlands.Scheme.Modules.pullbackTensorAssociativity` proves
exactly the existing `PullbackTensorAssociativityStatement.{u}`: the conjunction
of `LocalizedPullbackTensorAssociativityStatement.{u}` and
`ExplicitPullbackTensorAssociativityStatement.{u}`. Both equations hold for
every pair of schemes `X,Y : Scheme.{u}`, every morphism `f : X ⟶ Y`, and all
module sheaves `M,N,P` on `Y`, with no additional hypotheses.

Write `F` for pullback along `f`, `d` for the fixed localized comparison,
`D` for the fixed explicit comparison, `T` for `tensorObj`, `t` for
`tensorMap`, and `A` for `tensorAssociator`. The localized equation is

```text
d(M ⊗ N,P) ≫ (d(M,N) ▷ FP) ≫ α(FM,FN,FP).hom
  = F.map α(M,N,P).hom ≫ d(M,N ⊗ P) ≫ (FM ◁ d(N,P)).
```

Both composites run from `F((M ⊗ N) ⊗ P)` to `FM ⊗ (FN ⊗ FP)`.
Here `⊗`, `α`, and the whiskerings belong to the published localized
monoidal structure on scheme-module sheaves. The explicit equation is

```text
D(T(M,N),P) ≫ t(D(M,N),id(FP)) ≫ A(FM,FN,FP).hom
  = F.map A(M,N,P).hom ≫ D(M,T(N,P)) ≫ t(id(FM),D(N,P)).
```

Its source is `F(T(T(M,N),P))` and its target is `T(FM,T(FN,FP))`.
The explicit tensor is the sheafified tensor, and `A` is the fixed
associator transported through `localizedTensorIso`.

The argument uses the existing fixed maps and does not assume invertibility of
the pullback tensor comparison. It imports the published naturality lemmas for
`localizedTensorIso` from `Picard.RigidifiedTensorAssociativity`; these are
unconditional lemmas, and none of that module's conditional rigidified
associativity results are used.

Write `i(M,N)` for `localizedTensorIso X M N`. The reused
`localizedTensorIso_associativity` lemma from
`PushforwardTensorAssociativityProofs` unfolds the definition of `tensorAssociator` and
cancels inverse pairs to identify the associator square between
`((M ⊗ N) ⊗ P)` and `tensorObj M (tensorObj N P)`. Its left comparison is
`(i(M,N).hom ⊗ id) ≫ i(tensorObj M N,P).hom`; its right comparison is
`(id ⊗ i(N,P).hom) ≫ i(M,tensorObj N P).hom`.

The private `left_comparison` and `right_comparison` lemmas express each nested
localized pullback comparison in explicit tensor coordinates. They expand
`localizedPullbackTensorComparisonApp_eq`, cancel the resulting inverse pairs,
apply the naturality of `localizedTensorIso`, and use
`pullbackTensorComparisonApp_naturality` with one tensor-comparison isomorphism
and one identity. Functoriality of `tensorMap` and of pullback finishes these
calculations.

The lemma `localizedPullbackTensorAssociativity_of_explicit` postcomposes the
localized equation with the invertible right comparison above. The associator
square and the two nested comparison formulas transform the two sides into the
same outer pullback map followed by the two sides of the explicit equation.
Applying its explicit-equation hypothesis proves the transported equality;
cancellation yields the desired localized equality.

The theorem `localizedPullbackTensorAssociativity` discharges the transfer
lemma's hypothesis with the published unconditional
`explicitPullbackTensorAssociativity`, imported from
`ExplicitPullbackTensorAssociativityProofs`. The final theorem
`pullbackTensorAssociativity` pairs this localized result with the imported
explicit result. It assumes neither an associativity law nor a monoidal
pullback structure, comparison invertibility, or a geometric restriction.
This module supplies the two associativity equations; it does not assemble
a strong symmetric monoidal pullback structure.

Worker 339 authored the comparison calculations, transfer lemma, and final
conjunction in this module. The imported explicit proof was authored by
Worker 367 with Worker 339's adjunction calculation; it in turn uses
Worker 464's published pushforward associativity theorem. This is an internal
categorical consequence of the fixed Library definitions and those published
results, not a translation of a separate literature theorem. The imported
statements and constructions are unchanged. Integration exposes Worker 464's
existing associator comparison and reuses it here in place of the identical
private comparison statement. No axioms or proof holes are added.
