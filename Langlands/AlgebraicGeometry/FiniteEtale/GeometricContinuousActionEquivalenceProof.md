# Equivalence for the actual geometric continuous-action functor

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.geometricContinuousActionEquivalence`
proves the published proposition `GeometricContinuousActionEquivalence s hfin`
from `Statements`. Its full telescope is retained:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

The conclusion is `(continuousActionFunctor s hfin).IsEquivalence`. Here
`Cover S` is the full category of finite étale schemes over `S`. The functor
uses the actual geometric fibres `Fiber s Y`, with maps given by
postcomposition, and their continuous evaluation action by
`FundamentalGroup s hfin = Aut (fiberFunctor s hfin)`. Its target is
`ContAction FintypeCat.{u} (FundamentalGroup s hfin)`.

## Implemented argument

The proof imports `geometricGaloisFiberFunctor` by Lean name from
`GeometricGaloisFiberFunctorProof`. It unpacks that theorem into a witness
`hG : GaloisCategory (Cover S)` and the fibre-functor structure for the actual
`fiberFunctor s hfin`. These proved structures are installed as local instances.
They are obtained from the geometric result under the displayed hypotheses;
they are not premises of the closing theorem.

Mathlib `CategoryTheory.Galois.Equivalence` defines
`PreGaloisCategory.functorToContAction F` by lifting
`PreGaloisCategory.functorToAction F` to continuous finite actions, using
`PreGaloisCategory.continuousSMul_aut_fiber F Y` for continuity.
The project's `continuousActionFunctor s hfin` is defined by exactly this
lift with `F = fiberFunctor s hfin`: its `actionFunctor` unfolds to
`PreGaloisCategory.functorToAction F`. Thus the two functors agree by
definitional equality, including their action, finite-set topology, and
automorphism-group topology. The proof's `change` step checks this equality.

With the local Galois-category and fibre-functor instances, Mathlib supplies
`(PreGaloisCategory.functorToContAction (fiberFunctor s hfin)).IsEquivalence`.
The final `infer_instance` applies that result to prove the original target.
This proves equivalence of the specified functor itself.

## Source and scope

The geometric statement comes from Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter X §3, Definitions 10.25–10.26
and Theorem 10.28, printed pp.150–151 (PDF pp.154–155).
The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition 10.25 supplies the finite étale category and geometric-point
functor; Definition 10.26 identifies its automorphism group for connected
locally noetherian schemes. Theorem 10.28 states that this functor induces
the equivalence with finite continuous actions. The present proof implements
the final abstract Galois-theory step using pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; its geometric input is the
published theorem `geometricGaloisFiberFunctor`.

The explicit `hfin` is retained to package the geometric fibres as finite
sets. The definitions fix their discrete topology and the evaluation topology
on the natural automorphism group. No additional topological hypothesis is
required. All new class instances are local to the proof, and the published
statement pair and its imports are unchanged.
