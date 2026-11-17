# The root-datum isogeny of a quasi-finite surjection on a field-valued fibre

Worker 407, for Task 6494 (with Worker 99).

This module supports the proof of
[`Reductive.AffineSplitSurjectionRootDatumStatement`](AffineSplitSurjectionRootDatumStatement.md)
(Conrad, *Reductive group schemes*, Proposition 6.1.7, over an affine base `Spec R`).
It handles the field-level step. Take a quasi-finite surjection `φ : G ⟶ H` of split
reductive group schemes over `Spec R` that maps the split torus `i` of `G` into the
split torus `i'` of `H` through `τ`. Suppose that on an open `V` the map `τ` pulls the
exponent characters back by a fixed linear map `h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)`. Then `h`
is the weight map of a root-datum isogeny `Q → P` between the coordinate root data.

It is internal helper content. It formalizes no numbered statement of the literature. It
is the step "each `f_s` is an isogeny, so Milne Proposition 23.5 gives a `p`-morphism of
the root data of the fibre", which Conrad uses on p.187 and after Definition 6.1.6
(p.190) of the cited notes. The module does not prove the task target. It does not prove
the root-factor clause `(p : Γ(Spec R, V)) = 0`. It also does not prove that the
character identity holds on some open `V`. Both come from other modules of the proof.

All declarations are in the namespace `Langlands.GroupScheme.AffineSplitSurjection`, in
universe `u`.

## Declarations

### Lattice part

- `isReduced_fieldRealization k P`: for a field `k` and a reduced coordinate root datum
  `P : RootDatum J (I → ℤ) (I → ℤ)`, the field realization `fieldRealization k P`
  ([`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md)) is reduced. It is the same
  statement as the Library's `fieldRealization_isReduced` in
  [`Reductive.LocalSplitCell`](LocalSplitCell.md), restated here to avoid importing that
  module. Proof: each root of `fieldRealization k P` is the image of the corresponding
  root of `P` under the inverse of `splitTorus.characterLatticeEquiv k I`. A linear
  dependence of two realized roots therefore pulls back to a dependence of the roots of
  `P`, through the `ℤ`-linear injective map of that additive equivalence
  (`LinearIndependent.map_injOn`). Reducedness of `P` then gives `β = ±α`.
- `ofFieldRealization f` (definition): given
  `f : RootDatumIsogeny p (fieldRealization k Q) (fieldRealization k P)`, it returns the
  root-datum isogeny `Q → P`. It composes `f` with the root-datum isomorphisms
  `fieldRealizationEquiv k Q` and `(fieldRealizationEquiv k P).symm`. Each of these is
  turned into a root-datum isogeny with exponent `p` by `RootDatumIsogeny.ofHom`. Its
  weight map is the composite of the three weight maps. Its exponent is the exponent `p`
  of `f`.
- `ofFieldRealization_weightMap f h hf`: if `f.weightMap` sends the exponent character
  `χ_m` of `𝔾_m^{I'}` over `k` to `χ_{h m}` for every `m : I' → ℤ`, then
  `(ofFieldRealization f).weightMap = h`. Proof: compute the composite with
  `fieldRealizationEquiv_weightMap`, which identifies the weight map of
  `fieldRealizationEquiv k P` with `m ↦ χ_m`, and cancel the equivalence.

### Base change of the torus homomorphism

- `baseChangeTorusHom b τ` (definition): for `b : S' ⟶ S` and a homomorphism
  `τ : splitTorus S I ⟶ splitTorus S I'`, it is the homomorphism of commutative group
  schemes `splitTorus.commGroupScheme S' I ⟶ splitTorus.commGroupScheme S' I'`. It is the
  base change `(baseChange b).map τ`, conjugated by the canonical isomorphisms
  `splitTorus.baseChangeIso b` between the base change of the coordinate split torus and
  the coordinate split torus over `S'`.
- `baseChangeTorusHom_exponentCharacter b τ hb hV m`: let `V` be an open of `S` with
  `b ⁻¹ᵁ V = ⊤`. Suppose `hV`: for every test scheme `U` over `S` landing in `V`, every
  `x : U ⟶ 𝔾_m^I` and every `m`,
  `∏ j', (pointsEquiv I' U (x ≫ τ.hom.hom))_{j'} ^ m j' = ∏ j, (pointsEquiv I U x)_j ^ (h m) j`.
  This is the identity of points of the target statement. Then
  `baseChangeTorusHom b τ ≫ exponentCharacter S' I' m = exponentCharacter S' I (h m)` as
  characters over `S'`. Proof: compare the two homomorphisms on points
  (`CommGroupScheme.hom_ext_points`). A `U`-point of the base-changed torus over `S'`
  corresponds, through `splitTorus.baseChangeIso` and
  `GroupScheme.baseChangePointsEquiv`, to a point of `𝔾_m^I` over the test scheme
  `U → S' → S`. That test scheme lands in `V` because `b ⁻¹ᵁ V = ⊤`, so `hV` applies to
  it. The coordinates of the points agree by `splitTorus.pointsEquiv_baseChangeIso_hom`
  and `GroupScheme.baseChangePointsEquiv_comp`.

### Field-level root-datum isogeny

Both theorems take the hypotheses of the target statement on `(G, i, P)` and `(H, i', Q)`
except the closed-subgroup hypotheses `IsClosedSubgroup i` and `IsClosedSubgroup i'`,
which the proof does not use. They also take a homomorphism `φ : G ⟶ H` that is locally
quasi-finite and surjective, a torus homomorphism `τ` with `i ≫ φ = τ ≫ i'`, an open `V`
of `Spec R`, a linear map `h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)`, and the hypothesis `hV` above
over `S = Spec R`. Here `IsAffineHom G.X.hom` and `IsAffineHom H.X.hom` are instance
arguments (the target statement obtains them from `IsReductive`). The free root-space
hypotheses of the target statement are not needed.

- `exists_rootDatumIsogeny_weightMap_of_field … k hk`: for a field `k` with an
  `R`-algebra structure such that `algebraBaseMap R k ⁻¹ᵁ V = ⊤`, there are `p : ℕ` and
  `r : RootDatumIsogeny p Q P` with `r.weightMap = h`.
- `exists_rootDatumIsogeny_weightMap … s hs`: the same conclusion for every point `s` of
  `V`. It is the field form applied to the residue field `κ(s)` of the prime `s`. The map
  `Spec κ(s) → Spec R` has image `{s} ⊆ V`: the prime of `κ(s)` is `0`, and its
  contraction to `R` is the kernel of `R → κ(s)`, which is `s`
  (`Ideal.ker_algebraMap_residueField`).

## Proof of the field form

Let `b = algebraBaseMap R k : Spec k ⟶ Spec R`, and let `G_k`, `H_k` and `φ_k` be the base
changes of `G`, `H` and `φ` along `b`.

1. **Connected reductive fibres.** `IsReductive.isConnectedReductive_baseChange` gives
   that `G_k` and `H_k` are connected reductive groups over `k`.
2. **`φ_k` is an isogeny.** The morphism `φ` is quasi-compact. Its composite with the
   affine structure map of `H` equals the structure map of `G`, which is quasi-compact.
   Since `φ_k` is a pullback of `φ` (`baseChange_map_isPullback`), it is quasi-compact,
   locally quasi-finite and surjective. `G_k` is quasi-compact and locally of finite type
   over `k`, and `H_k` is smooth over `k`. So `flat_of_surjective`
   ([`CentralIsogeny.ProjectionCentralIsogeny`](../CentralIsogeny/ProjectionCentralIsogeny.md))
   shows that `φ_k` is flat. Then `isogeny_of_quasiFinite_flat_surjective_over_field`
   ([`Reductive.NoetherianIsogenyApproximation`](NoetherianIsogenyApproximation.md))
   shows that `φ_k` is an isogeny.
3. **The torus square over `k`.** Let `t = baseChangeTorusHom b τ`. The square
   `i ≫ φ = τ ≫ i'` base changes to
   `splitTorus.baseChangeHom G I i ≫ φ_k = t ≫ splitTorus.baseChangeHom H I' i'`, by
   functoriality of base change and cancellation of `splitTorus.baseChangeIso`.
4. **Milne Proposition 23.5.** The base-changed tori are maximal by
   `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`. Their root data are
   `fieldRealization k P` and `fieldRealization k Q` by `hP.field k` and `hQ.field k`.
   These root data are reduced by `isReduced_fieldRealization`. The Library theorem
   `isogenyRootDatum`, which proves
   [`Reductive.IsogenyRootDatumStatement`](IsogenyRootDatumStatement.md), then gives
   `f : RootDatumIsogeny (ringExpChar k) (fieldRealization k Q) (fieldRealization k P)`
   with `f.weightMap χ = t ≫ χ` for every character `χ`.
5. **Transport.** By step 4 and `baseChangeTorusHom_exponentCharacter` (which applies
   because `b ⁻¹ᵁ V = ⊤`), `f.weightMap χ_m = t ≫ χ_m = χ_{h m}`. So
   `r = ofFieldRealization f` satisfies `r.weightMap = h` by
   `ofFieldRealization_weightMap`.

The exponent `p` of the conclusion is `ringExpChar k`, but the statement only asserts the
existence of some `p`.

## Sources

- Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
  Panoramas et Synthèses 42–43, SMF, 2014 (`conrad-2014-reductive-group-schemes`):
  p.187 (before Lemma 6.1.3) and the remark after Definition 6.1.6, p.190, which pass
  to the fibres `f_s`, which are isogenies; Proposition 6.1.7, p.190, the target.
- J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017
  (`milne-2017-algebraic-groups`), Proposition 23.5. It is used through the published
  Library theorem `isogenyRootDatum`, not restated here.
