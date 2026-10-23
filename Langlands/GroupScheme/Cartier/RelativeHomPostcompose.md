# Covariance of relative Hom in the target

Author: Worker 139.

This module extends the published `Langlands.GroupScheme.Cartier.Restriction`
API. All group schemes are actual `Langlands.CommGroupScheme S` objects over
an arbitrary scheme `S`; there are no finiteness or geometric hypotheses.
`RelativeHom G H T` remains the actual additive Hom group from `G_T` to `H_T`.

For a homomorphism `ψ : H ⟶ H'`, `postcompose G ψ T` is the additive map
sending `χ` to `χ ≫ (CommGroupScheme.baseChange T.hom).map ψ`.
`postcompose_apply` exposes this formula. Its additivity is supplied by
`Preadditive.rightComp` in the category of commutative group schemes over
`T.left`. `postcompose_id` and `postcompose_comp` prove that this target action
preserves identities and composition; their proofs use the functor laws of
actual base change and associativity of categorical composition.

`restrict_postcompose` proves that postcomposition commutes with the published
restriction map along every `a : T' ⟶ T`. The proof compares the first
projections of the two actual scheme morphisms using `relativeHom_ext`.
The published `restrict_fst` and `baseChange_map_fst` formulas identify these
projections. Hence `postcomposeNatTrans G ψ` is a natural transformation from
`relativeHomFunctor G H` to `relativeHomFunctor G H'`. Its component formula,
identity law and composition law are given by
`postcomposeNatTrans_app_apply`, `postcomposeNatTrans_id`, and
`postcomposeNatTrans_comp`. `relativeHomTargetFunctor G` packages these into a
functor from commutative group schemes over `S` to additive presheaves on
`Over S`.

`precompose_postcompose` states that source precomposition by `φ : G' ⟶ G`
and target postcomposition by `ψ : H ⟶ H'` commute. Its proof is associativity.
`precomposeNatTrans_postcomposeNatTrans` states the same commuting square of
natural transformations. The published
`evaluation_postcompose` applies definitionally to the new additive action: evaluating the
postcomposed homomorphism at `x` gives `evaluation χ x ≫ ψ.toMul.hom.hom`.
No duplicate evaluation definition or lemma is introduced.

## Provenance

These constructions are derived categorical infrastructure, extending the
published restriction module in the target variable. Edixhoven, van der Geer
and Moonen, *Abelian Varieties*, preliminary draft, Definition (3.1), printed
p.29/PDF33, defines actual group schemes and their homomorphisms and describes
base change. Section (3.21), printed p.41/PDF45, defines the relative character
functor with value `Hom_T(G_T, Gm,T)`. The present target-functor construction
generalizes its target to an arbitrary commutative group scheme and proves
formal covariance by composition. This extra generality is derived from the
category structure, rather than quoted as a separate theorem of the source.
No Cartier representability, biduality, or isogeny kernel duality is claimed.
The restriction functor, its identity/composition laws, section-evaluation
naturality, and source-precomposition action are imported by Lean name.

Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`.
SHA256: `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Retained file:
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
PDF33 and PDF45 were read for this extension.
