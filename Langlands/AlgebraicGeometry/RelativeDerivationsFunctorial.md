# Precomposition of relative derivations

Let `X`, `Y`, `Z`, and `S` be arbitrary `Scheme.{u}` objects. For a morphism
`g : X ⟶ Y`, a structure morphism `f : Y ⟶ S`, an actual sheaf of modules
`M : X.Modules`, and a relative derivation `d : RelativeDerivation (g ≫ f) M`,
`Langlands.Scheme.RelativeDerivation.precomp g f d` is a relative derivation
on `Y` into the actual module sheaf `Scheme.Modules.pushforward g |>.obj M`.
On every open `U` of `Y`, it sends a local section `a` to
`d.app (g ⁻¹ᵁ U) (g.app U a)`.

`precompOver g h d` supplies the same operation when the structure morphisms
`fX : X ⟶ S` and `fY : Y ⟶ S` are given separately, with a commuting triangle
`h : g ≫ fY = fX`. The section formulas are proved by `precomp_app` and
`precompOver_app`. This is the operation on derivations used in the first
part of Stacks Project Lemma 17.28.12 (tag 08RU), with the base map the identity.
That lemma applies it to the universal derivation; here the construction is
made for every relative derivation, with no assumed cotangent object.

The construction composes additive maps on local sections. The Leibniz
identity follows from multiplicativity of `g.app U` and the Leibniz identity
for `d`, since the scalar action on the pushforward module is restriction
of scalars along that ring map. Restriction compatibility follows from
naturality of `g.c` and restriction compatibility of `d`. Vanishing on base
sections follows from the composite ring map and the relative condition on
`d`. The arbitrary commuting triangle is handled by equality transport.

`precompOver_postcomp` proves naturality with respect to a module morphism
`α : M ⟶ N`: precomposing `d.postcomp α` is the postcomposition of
`precompOver g h d` by `(Scheme.Modules.pushforward g).map α`.

The coherence lemmas use the actual module-sheaf pushforward isomorphisms:

- `precompOver_id` states that precomposition along the identity, followed by
  `(Scheme.Modules.pushforwardId X).hom.app M`, recovers `d`.
- `precompOver_comp` states that precomposition first along `h : X ⟶ Y`
  and then along `k : Y ⟶ Z`, followed by
  `(Scheme.Modules.pushforwardComp h k).hom.app M`, equals precomposition
  along `h ≫ k`. Each morphism is equipped with its commuting triangle over
  `S`; the composite triangle follows by associativity.

These proofs reduce equality of derivations to equality on local sections.
The pushforward coherence maps are identities on those sections, and the
identity and composition laws of scheme section maps give the result.
The composition law is the derivation-level calculation underlying Stacks
Project Lemma 17.28.13 (tag 01UW). No cotangent sheaf, representability theorem,
or induced map from a pulled-back cotangent sheaf is asserted in this file.
Those require the separate construction and its universal property.

The implementation develops Worker 136's initial draft of this module;
Worker 208 completed the elaboration and the coherence proofs.

## Sources

- Registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
  content SHA256
  `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`:
  `08RL.html`, Definition 17.28.10 and Lemmas 17.28.12–13 (tags 08RT, 08RU,
  01UW). These are the original relative-derivation setting and the source
  of the functorial construction; the general derivation-level identities
  above are derived directly from their local-section formulas.
- Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
  `AlgebraicGeometry/Modules/Sheaf.lean` supplies actual pushforward sheaves,
  their identity and composition isomorphisms; `AlgebraicGeometry/Scheme.lean`
  supplies the local ring maps and their laws.
