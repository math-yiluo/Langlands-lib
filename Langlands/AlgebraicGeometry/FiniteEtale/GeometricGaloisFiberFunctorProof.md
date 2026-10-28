# The geometric finite étale Galois category and fibre functor

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.geometricGaloisFiberFunctor`
proves the published proposition `GeometricGaloisFiberFunctor s hfin`
from `Statements`. It retains the entire telescope:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

Here `Cover S` is the actual full category of finite étale schemes over `S`.
The type `Fiber s Y` consists of morphisms from the geometric point `s` to
`Y` over `S`, and `fiberFunctor s hfin` packages this geometric-point functor
in finite sets using the explicit witness `hfin`. These are the constructions
in `Definitions`.

The conclusion is an existential witness `hG : GaloisCategory (Cover S)`
together with the fibre-functor structure for this particular
`fiberFunctor s hfin`, using `hG` locally. Both structures are constructed
in the proof.

## Implemented proof

The proof imports three geometric results by Lean name:

| Published theorem | Fields supplied |
| --- | --- |
| `geometricFiniteLimitsCoproducts` | Terminal objects, pullbacks and finite coproducts in `Cover S`, and their preservation by `fiberFunctor s hfin`. |
| `geometricMonoEpiConservative` | The direct-summand property of every monomorphism, preservation of epimorphisms and reflection of isomorphisms by this functor. |
| `geometricFiniteGroupQuotients` | Quotients of diagrams `SingleObj G ⥤ Cover S` for every finite group `G : Type u`, and their preservation by this functor. |

It unpacks the first two conjunctions and retains the third as `hquot`.
The five fields of a local `PreGaloisCategory (Cover S)` are assigned
explicitly: the three existence properties from the first theorem,
`fun G => (hquot G).1` for finite-group quotients, and the monomorphism
property from the second theorem.

For that local category structure, the proof explicitly assigns all six
fields of `PreGaloisCategory.FiberFunctor (fiberFunctor s hfin)`.
The first theorem supplies preservation of terminal objects, pullbacks
and finite coproducts. The second supplies preservation of epimorphisms
and reflection of isomorphisms. The quotient-preservation field is
`fun G => (hquot G).2`. The quotient theorem retains the full universe
required by the class fields.

The proof then constructs `hG : GaloisCategory (Cover S)` using the
constructed pre-Galois structure and this same geometric functor as
the witness for `hasFiberFunctor`. Finally it returns `hG` together
with the fibre-functor structure already built. `PreGaloisCategory`
is proposition-valued, so proof irrelevance identifies its local
instance with the one inherited from `hG` when elaborating the final
existential. All instance bindings in this argument are local.

## Provenance and scope

This theorem is an internal assembly of the published geometric proofs
and the class definitions in pinned Mathlib `CategoryTheory.Galois.Basic`.
The paired Markdown for each imported proof explains its implemented
geometric argument. This module introduces no further geometric lemma.

The original geometric context is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter X §3,
Definitions 10.25–10.26 and Theorem 10.28, printed pp.150–151
(PDF pp.154–155). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
As explained in `Statements`, the target expresses the geometric
Galois axioms through Mathlib's classes; the book does not print this
exact Lean axiom formulation.

The theorem keeps `hfin` explicit. The separately published
`geometricFiberFinite` theorem can supply geometric fibre finiteness.
The category and fibre-functor structures are conclusions, with no
additional structural or action-equivalence hypothesis. The statement
pair and its imports are unchanged.
