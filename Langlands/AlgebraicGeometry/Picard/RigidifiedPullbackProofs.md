# Identity and composition compatibility of canonical rigidified pullback

`Langlands.SchemeModule.RigidifiedModule.pullbackCoherence` proves
`Langlands.SchemeModule.RigidifiedModule.PullbackCoherenceStatement` from
`Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackStatements`. It is the
pair of `pullbackIdentity : PullbackIdentityStatement` and
`pullbackComposition : PullbackCompositionStatement`. Both hold for all
schemes, morphisms, commuting squares and rigidified module sheaves in an
arbitrary universe `u`.

The proof is internal categorical reasoning with the canonical unit
comparison laws published in `Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs`
and the pseudofunctor laws for scheme-module pullback in pinned Mathlib. It
does not claim to reproduce a literature proof.

## Recalled construction

For a commuting square `ε' ≫ f = g ≫ ε` and a rigidified module `(M, α)` with
`α : O_S ≅ ε^* M`, the canonical pulled-back rigidification of `f^* M` is
the composite of three isomorphisms. The first is the inverse canonical unit
comparison `O_{S'} ≅ g^* O_S`. The second is `g^* α`. The third is the square
comparison `g^* ε^* M ≅ (g ≫ ε)^* M = (ε' ≫ f)^* M ≅ ε'^* f^* M`, built from
Mathlib's `pullbackComp`, `pullbackCongr` and the inverse of `pullbackComp`.

## Helper lemmas

`compHom a b c h N` is the comparison `a^* (b^* N) ⟶ c^* N` attached to an
arbitrary proof `h : a ≫ b = c`. It is the component at `N` of Mathlib's
`Scheme.Modules.pullbackComp a b`, followed by that of
`Scheme.Modules.pullbackCongr h`. Allowing an arbitrary target map `c` lets the
squares below be pasted without rewriting scheme maps inside types.

- `compHom_rfl`: for the defining equation `a ≫ b = a ≫ b`, `compHom` is the
  component of `pullbackComp a b`, since `pullbackCongr rfl` is an identity
  `eqToHom`.
- `compHom_assoc`: for maps `a`, `b`, `c` and any proofs naming the composites
  `ab`, `bc` and `abc`, the two ways of comparing `a^* b^* c^* N` with
  `abc^* N` agree. After substituting the equations, it is the component at
  `N` of Mathlib's `Scheme.Modules.pseudofunctor_associativity`. Cancelling
  the inverse composition comparisons in front puts it into this form.
- `compHom_id_left`: when the first map is `𝟙 X`, `compHom` is the identity
  comparison `(pullbackId X).hom` at `a^* N`, followed by an `eqToHom`. This
  comes from Mathlib's `Scheme.Modules.pseudofunctor_right_unitality`.
- `pullbackComp_inv_app_comp_pullbackId`: the inverse comparison
  `(a ≫ 𝟙 Y)^* N ⟶ a^* (𝟙 Y)^* N` followed by `a^*` of the identity comparison
  is an `eqToHom`. This is Mathlib's `Scheme.Modules.pseudofunctor_left_unitality`
  at `N`.
- `pullbackUnitIso_inv_comp`: rewrites the published
  `Langlands.Scheme.Modules.pullbackUnitComposition` for inverse maps. The
  inverse unit comparison along `f`, then `f^*` of the inverse along `g`, then
  the composition comparison at `O_Z`, gives the inverse unit comparison along
  `f ≫ g`. The proof uses `Iso.comp_hom_eq_id` and functoriality.
- `pullback_rigidification_hom_comp`: the forward map of the canonical
  pulled-back rigidification, followed by `(pullbackComp ε' f).hom` at `M`,
  equals the inverse unit comparison along `g`, then `g^* α`, then
  `compHom g ε (ε' ≫ f) comm.symm M`. After unfolding the definition, the
  inverse of `pullbackComp ε' f` cancels against its forward map.

## Identity law

`pullbackIdentity` unfolds the pulled-back rigidification for the square with
`𝟙 X` and `𝟙 S`. `pullbackComp_inv_app_comp_pullbackId` and `compHom_id_left`
remove the composition comparisons. The published
`Langlands.Scheme.Modules.pullbackUnitIdentity`, via `Iso.ext`, identifies the
unit comparison along `𝟙 S` with the component of `pullbackId S` at
`O_S`. Naturality of `pullbackId S` moves `α` past this comparison. The
inverse and forward components then cancel, and the remaining `eqToHom`
maps compose to the identity, leaving `α`.

## Composition law

`pullbackComposition` compares two maps into `ε''^* ((f' ≫ f)^* M)`. Since
`(pullbackComp ε'' (f' ≫ f)).hom` at `M` is an isomorphism, it suffices to
compare the composites with it (`cancel_mono`). All comparisons are then
taken into `E^* M` for the common composite `E = ε'' ≫ f' ≫ f`. Three
instances of `compHom_assoc` paste the squares:

1. For `ε''`, `f'`, `f`, it moves `ε''^*` of `pullbackComp f' f` into
   comparisons through `(ε'' ≫ f')^*`.
2. For `g'`, `ε'`, `f`, with the equation `ε'' ≫ f' = g' ≫ ε'` from `comm'`,
   it replaces the outer square by the inner square's comparison.
3. For `g'`, `g`, `ε`, with `g ≫ ε = ε' ≫ f` from `comm` and
   `(g' ≫ g) ≫ ε = ε'' ≫ (f' ≫ f)` from `comm''`, it identifies the result
   with the comparison of the composite square.

`pullback_rigidification_hom_comp` is applied to each of the three
rigidifications (along `(f, g)`, `(f', g')` and `(f' ≫ f, g' ≫ g)`).
Naturality of `pullbackComp g' g` on the forward map of `α` lines up
`g'^* g^* α` with `(g' ≫ g)^* α`. Finally, `pullbackUnitIso_inv_comp` for
`g'` and `g` merges the two inverse unit comparisons into the one along
`g' ≫ g`.

## Technical notes

Each helper lemma and the theorems `pullbackIdentity` and `pullbackComposition`
use the local option `backward.isDefEq.respectTransparency false`, so that
elaboration can see through the existing scheme-module wrappers. A few
steps use `erw`, because the carrier of a pulled-back rigidified module and
`SheafOfModules.unit` versus `structureModule` agree only definitionally.
The proof introduces no hypotheses beyond those of the statements and no new
axioms. It proves exactly the two compatibility equations; it says nothing
about rank-one, tensor, group-law or representability properties.
