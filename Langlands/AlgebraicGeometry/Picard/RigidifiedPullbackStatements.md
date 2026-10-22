# Compatibility targets for canonical rigidified pullback

The namespace `Langlands.SchemeModule.RigidifiedModule` contains two proposition
statements about the constructed canonical pullback of rigidified module
sheaves. `PullbackCoherenceStatement` is their conjunction. This file states
the laws; it does not prove them or add them as axioms.

For a scheme map `ε : S → X`, a rigidified module is an actual module sheaf `M`
on `X` together with an isomorphism `α : O_S ≅ ε* M`. Pullback along a commuting
square with maps `f : X' → X` and `g : S' → S` uses the canonical structure-sheaf
comparison and the actual scheme-module pullback comparisons, as defined in
`RigidifiedLineBundle` and `RigidificationBaseChange`.

`PullbackIdentityStatement` says that the underlying module comparison
`id_X* M ≅ M` respects the rigidifications: composing the pulled-back
rigidification with `ε*` of its forward map gives `α`.

`PullbackCompositionStatement` considers two consecutive squares, with
`f' : X'' → X'` and `g' : S'' → S'`. It says that the underlying comparison
`f'* (f* M) ≅ (f' ≫ f)* M` respects the rigidifications along `ε''`.
Both sides use the canonical pullback construction. The statement explicitly
quantifies over proofs of commutativity for both squares and their composite;
the third equality follows from the first two by associativity. Its proof is
an argument only to identify the same scheme maps, not additional geometric
data. Proof irrelevance makes the statements independent of all these choices.

These are internal compatibility targets derived from the standard rigidified
pullback described in Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
Chapter VI §1, (6.2), printed p.88 (PDF p.92). The retained source is registered
as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source describes pullback on rigidified line bundles and the resulting
contravariant functor. These particular equations expose the categorical
compatibility underlying that description. They are formulated for all
rigidified module sheaves and all commuting squares, since neither local rank
one nor the source's extra hypotheses for automorphism and Picard comparison
results are needed for compatibility of pullbacks.

The intended proof uses the published canonical unit identity/composition laws
in `Modules.PullbackUnitProofs`, together with the associativity and unit laws
for scheme-module pullback in pinned Mathlib. No tensor product, group law,
sheaf property, representability, or higher coherence assertion is included.
A downstream construction may use this exact proposition as an explicit proof
hypothesis until its separate proof is published.
