# Vanishing of the characteristic exponent after base change to local algebras

This internal derived module moves the local theorem of
[`Reductive.AffineSplitSurjectionLocalCore`](AffineSplitSurjectionLocalCore.md)
from a local base ring to the setting of Conrad, *Reductive group schemes*
(2014), Proposition 6.1.7 (p.190), over an arbitrary affine base `Spec R`. It
proves condition 3 of Definition 6.1.6 (p.190) one local ring at a time: if a
root factor `q > 1` is a power of the prime `p`, then `p = 0`. Conrad proves this
in Lemma 6.1.4 (pp.188-189) by working Zariski-locally on the base. Here the
local theorem is applied after base change to a local `R`-algebra `A` whose
spectrum maps into the open set where the character map is known. The proof of
`AffineSplitSurjectionRootDatumStatement` in
[`Reductive.AffineSplitSurjectionRootDatumProof`](AffineSplitSurjectionRootDatumProof.md)
then uses `A = R_𝔭` for primes `𝔭` of `R`.

All declarations are in the namespace
`Langlands.GroupScheme.AffineSplitSurjection`. Throughout, `R` is a commutative
ring, `A` is an `R`-algebra, and `algebraBaseMap R A : Spec A ⟶ Spec R` is the
induced morphism of spectra.

## Base change of a torus homomorphism

- `torusBaseChange A τ` (definition): for a homomorphism
  `τ : 𝔾_m^I → 𝔾_m^{I'}` of coordinate split tori over `Spec R`, this is the
  homomorphism of coordinate split tori over `Spec A` obtained from the base
  change of `τ` along `algebraBaseMap R A`. It is the base change conjugated by
  the Library identifications `splitTorus.baseChangeIso` of the base-changed
  coordinate tori with the coordinate tori over `Spec A`.
- `groupHom_torusBaseChange` unfolds this definition (`rfl`).
- `baseChangePointsEquiv_torusBaseChange`: a point of the coordinate torus over a
  test scheme `Z` over `Spec A` corresponds to a point over `Spec R`
  (`GroupScheme.baseChangePointsEquiv`). Under this correspondence, applying
  `torusBaseChange A τ` corresponds to applying `τ`.
- `torusBaseChange_exponentCharacter`: suppose `splitTorus.CharacterMapOn τ V h`
  ([`Torus.SplitTorusCharacterIdempotents`](../Torus/SplitTorusCharacterIdempotents.md))
  and `algebraBaseMap R A ⁻¹ᵁ V = ⊤`. Then for every exponent vector `m`, the
  composite of `torusBaseChange A τ` with the exponent character `m` of
  `𝔾_m^{I'}` is the exponent character `h m` of `𝔾_m^I`, as an equality of
  homomorphisms of commutative group schemes over `Spec A`. Proof: two
  characters agree if they agree on points over every test scheme `Z` over
  `Spec A` (`CommGroupScheme.hom_ext_points`). The Library lemma
  `charValue_exponentCharacter_baseChange` computes the value of an exponent
  character on such a point as its value on the corresponding point over
  `Spec R`. The test scheme `Z`, viewed over `Spec R`, maps into `V`, because
  `Spec A` does. So `CharacterMapOn τ V h` applies to the corresponding point.

## Base change of the group data

- A local instance shows that the base change of an affine group scheme is
  affine.
- `locallyQuasiFinite_baseChange_map`: the base change of a locally quasi-finite
  homomorphism `φ` is locally quasi-finite. The base change of `φ` is a pullback
  of `φ` (the Library's `baseChange_map_isPullback`), and local quasi-finiteness
  is stable under pullback.
- `baseChangeHom_comp_map`: the base change of the torus square
  `i ≫ φ = τ ≫ i'` to `A`, written with the Library's base-changed torus
  embeddings `splitTorus.baseChangeHom` and with `torusBaseChange A τ`. Proof: by
  unfolding the definitions and functoriality of base change.

## Main theorem

`natCast_eq_zero_of_local_baseChange` has the following hypotheses:

- `A` is a local `R`-algebra;
- `G` and `H` are reductive group schemes over `Spec R` with coordinate split
  tori `i` and `i'` that are maximal on every fibre, with reduced fibrewise root
  data `P` and `Q`, and with root spaces free of rank one (the hypotheses of
  `AffineSplitSurjectionRootDatumStatement`, except that the tori are not required to be closed);
- `φ : G ⟶ H` is locally quasi-finite and `i ≫ φ = τ ≫ i'`;
- `splitTorus.CharacterMapOn τ V h` holds on an open set `V`;
- `r : RootDatumIsogeny p Q P` is a root-datum isogeny with `r.weightMap = h`;
- `algebraBaseMap R A ⁻¹ᵁ V = ⊤`;
- `r.rootFactor β ≠ 1` for some `β : J'`.

It concludes `(p : A) = 0`. Surjectivity of `φ` is not used.

Proof. Everything is base changed to `Spec A`. By `torusBaseChange_exponentCharacter`,
the base-changed torus map pulls back each exponent character `m` to
`r.weightMap m`. This is the hypothesis `hweight` of
`RelativeIsogeny.natCast_eq_zero_of_rootFactor_ne_one`. The remaining
hypotheses of that theorem are supplied by Library results:

- the base-changed fibrewise root data, by `IsFibrewiseRootDatumOf.baseChange`;
- the base-changed torus square, by `baseChangeHom_comp_map`;
- reductivity of the base change of `H`, by `IsReductive.baseChange`;
- fibrewise maximality of the base-changed torus of `H`, by
  `IsFibrewiseMaximalTorus.baseChange_coordinates`;
- local quasi-finiteness of the base change of `φ`, by
  `locallyQuasiFinite_baseChange_map`;
- root parametrizations of `G` for `P.root (r.indexEquiv β)` and of `H` for
  `Q.root β`. These are the global root parametrizations built from the free
  root spaces
  (`LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights`), base
  changed to `A` by `isRootParametrization_baseChangeRoot`.

The theorem `natCast_eq_zero_of_rootFactor_ne_one` then gives `(p : A) = 0`.
