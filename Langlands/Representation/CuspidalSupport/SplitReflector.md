# Reflectors onto split properties of smooth representations

Worker 4814. This is a supporting unit for Task 5419, which proves Renard VI.7.2,
second Lemma (`Langlands.CuspidalSupport.BernsteinCuspAdjunctionStatement`). It
supplies the cuspidal-part functor `W ↦ W_sc` and its exactness, in an abstract
form. It does not prove the target statement, and it does not prove that the
cuspidal representations of a standard Levi subgroup are split; that splitting
comes from Renard VI.3.5.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.7.2, second Lemma and its proof, printed pp.182–183 /
PDF pp.188–189; source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. These
pages were read. In the proof Renard uses the cuspidal part `r_P^G(π, V)_sc`,
and says that the projection `M(M) → M(M)_sc` is an exact functor. The
projection comes from the decomposition of every smooth representation into a
cuspidal part and a part with no cuspidal subquotient (VI.3.5). Everything in this
module is internal derived content. It abstracts that use of VI.3.5 to any
property `Q` of smooth complex representations of a topological group `G`, in
the carrier universe `uV`.

## Definitions

- `HasSplitting Q A`: `A` is the coproduct, indexed by `Bool`, of a summand
  `Y true` that satisfies `Q` and a summand `Y false` that has no nonzero
  subquotient satisfying `Q`. With `Q` the cuspidal property of a standard Levi
  subgroup, this is literally the shape of the published
  `HasCuspidalRemainderSplitting`, and so of `HasLeviCuspidalRemainderSplitting`.
- `IsSplitSerre Q`: `Q` is closed under injective intertwiners (sources of
  injective maps into a `Q`-object), closed under surjective intertwiners (targets
  of surjective maps out of a `Q`-object), and every object has a splitting.
- `summand`, `inj`, `isColimit`, `proj`, `rem`, `idem`: the chosen splitting of
  `A`, its coproduct inclusions, its colimit property, the projections to the two
  summands (defined by the coproduct's universal property), and the idempotent
  `idem = proj ≫ inj true` of `A`.
- `reflector hQ`: the left adjoint of the inclusion `Q.ι` of the full subcategory,
  sending `A` to its `Q`-summand. `reflectorAdjunction hQ` is the adjunction.

## Results and their proofs

- `exists_hom_ne_zero`, `nontrivial_image`: a nonzero morphism moves a vector off
  zero, so its image is nontrivial.
- `eq_zero_of_to_remainder`, `eq_zero_of_from_remainder`: every morphism between
  a `Q`-object and an object with no nonzero `Q`-subquotient (in either
  direction) is zero. Otherwise its image is a nontrivial subquotient of the
  remainder satisfying `Q`. The image is a quotient of a `Q`-object in the first
  case and a subobject of one in the second.
- `inj_true_proj`, `inj_false_proj`, `inj_true_rem`, `inj_false_rem`,
  `proj_add_rem`: the biproduct identities, by the colimit's universal property.
- `proj_inj_comp`: every morphism `φ` from `A` to a `Q`-object factors through the
  projection: `proj ≫ inj true ≫ φ = φ`. On the remainder summand both sides are
  zero, by `eq_zero_of_from_remainder`.
- `idem_idem`, `idem_comp`: `idem` is idempotent and commutes with every morphism
  `f : A ⟶ B`. For the second, `inj true ≫ f ≫ rem = 0`
  (`eq_zero_of_to_remainder`), so `inj true ≫ f` factors through `proj ≫ inj true`
  of `B`. Then `proj_inj_comp` applied to `f ≫ proj` gives the claim.
- `reflector`, `reflectorAdjunction`, `exists_leftAdjoint`: Mathlib's
  `Adjunction.leftAdjointOfEquiv` and `Adjunction.adjunctionOfEquivLeft` applied
  to the bijection `ψ ↦ proj ≫ ψ` between morphisms out of the `Q`-summand and
  morphisms out of `A`. Its inverse is `φ ↦ inj true ≫ φ`, by `inj_true_proj` and
  `proj_inj_comp`.

The remaining results hold for an arbitrary left adjoint `sc` of `Q.ι` with
adjunction `adj`, and not only for `reflector`:

- `unit_naturality_apply`: elementwise naturality of the unit.
- `unit_surjective`: every unit morphism `η : A ⟶ sc A` is surjective. The image
  of `η` is a subobject of a `Q`-object, so it is a `Q`-object `D`. The corestriction
  `A ⟶ D` corresponds to a morphism `ψ : sc A ⟶ D`. Then `ψ` followed by the image
  inclusion corresponds to `η`, so it is the identity of `sc A`, and every vector
  of `sc A` lies in the image.
- `unit_apply_eq_zero_iff`, `proj_apply_eq_zero_iff`,
  `unit_apply_eq_zero_iff_idem`: the unit and the chosen projection have the same
  kernel. One direction: `proj` factors through `η`. The other: `η` factors through
  `proj` by `proj_inj_comp`. The kernel of `proj` is the kernel of `idem` because
  `inj true` is a split monomorphism.
- `idem_idem_apply`, `idem_comp_apply`: elementwise forms of `idem_idem` and
  `idem_comp`.
- `map_isShortExact`: `sc` sends every actual short exact sequence (`IsShortExact`
  of the underlying intertwiners) to one. Every vector of `sc A` is `η a` by
  `unit_surjective`, and `η a = 0` if and only if `idem a = 0`. Injectivity:
  `sc f (η a) = η (f a)`, so `idem (f a) = f (idem a)` vanishes, hence `idem a = 0`
  by injectivity of `f`. Surjectivity: lift through `η` and through `g`. Exactness
  in the middle: if `sc g (η b) = 0`, then `g (idem b) = idem (g b) = 0`. So
  `idem b = f a` for some `a`, and `sc f (η a) = η (idem b) = η b`, because
  `idem (idem b - b) = 0`.
- `unit_injective_of_mem`: the unit at a `Q`-object `A` is injective, because the
  identity of `A` factors through it.
