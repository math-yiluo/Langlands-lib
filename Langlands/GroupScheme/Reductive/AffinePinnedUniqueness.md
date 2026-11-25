# Uniqueness in the pinned Isomorphism Theorem over an affine base

Module `Langlands.GroupScheme.Reductive.AffinePinnedUniqueness`, namespace
`Langlands.GroupScheme`. It proves the uniqueness half of
[`AffinePinnedIsomorphismTheoremStatement`](AffinePinnedIsomorphismTheoremStatement.md):
over any commutative ring `R`, two isomorphisms `φ ψ : G ≅ H` of split reductive group
schemes over `Spec R` that are both compatible with the splittings and with the pinnings
(parts 1 and 2 of that statement's conclusion, for the same `f`) are equal. The main
step is rigidity of pinned automorphisms: an automorphism of `G` that is the identity on
the split torus and whose Lie algebra map fixes the pinning vectors is the identity.
This is Conrad, *Reductive group schemes* (2014), Proposition 6.1.13(2), applied to
`φ⁻¹ ∘ ψ`, as in the statement's Markdown ("Existence and uniqueness"). It does not
prove existence.

It imports [`AffineRootLieDerivative`](AffineRootLieDerivative.md) and the Library
modules `LocalSimpleRootPowerRigidity`,
`RelativeTorusConjugationRigidity`, `GlobalSplitRootParametrization` and
`AffinePinnedIsomorphismTheoremStatement`.

## Declarations

Section `LocalToGlobal`:

- `hom_ext_of_localBaseChange`: for group schemes `G H` over `Spec R` with `H.X.left`
  affine, two homomorphisms `f F : G ⟶ H` are equal if their base changes to `Spec A`
  agree for every local `R`-algebra `A`.

Section `BaseChange` (an `R`-algebra `A`, a split torus `i : splitTorus (Spec R) I ⟶ G`;
`splitTorus.baseChangeHom G I i` is the Library's base-changed torus of `G_A`):

- `baseChangeHom_comp_of_comp_eq`: if `i ≫ σ = i` then the base-changed torus is fixed by
  the base change of `σ`.
- `isClosedSubgroup_baseChangeHom`: the base-changed torus of a closed torus is closed.

Section `Rigidity` (`G` with `IsAffineHom G.X.hom`, reductive `hG`, a closed fibrewise
maximal split torus `i` with fibrewise root datum `P` and free root spaces `hfree`, a base
`b : P.Base`, an automorphism `σ : G ≅ G` with `i ≫ σ.hom = i`, and
`hX`: `Lie.targetMapLinear σ.hom R` fixes every vector of the root space of every simple
root `a ∈ b.support`):

- `simpleRoot_comp_eq_of_fixes`: `σ` fixes the Library's chosen global parametrization
  `LocalRootGroup.rootParametrizationsOfFreeWeights … a` of each simple root `a`.
- `baseChange_map_eq_id_of_fixes`: for every local `R`-algebra `A`, the base change of
  `σ.hom` to `Spec A` is the identity.
- `iso_eq_refl_of_fixes`: **rigidity of pinned automorphisms**: `σ = Iso.refl G`.
- `iso_eq_refl_of_fixes_pinning`: the same with `hX` replaced by: for trivializations
  `X a : R ≃ₗ[R] exponentWeightSpace I G i (P.root a)` of the simple root spaces,
  `Lie.targetMapLinear σ.hom R (X a 1).val = (X a 1).val` for each `a : b.support`.

Section `Torus`:

- `splitTorus_hom_eq_of_characters`: two homomorphisms `τ τ' : 𝔾_m^I → 𝔾_m^{I'}` over any
  scheme that both satisfy the character identity
  `∏ j', τ(x)_{j'} ^ m j' = ∏ j, x_j ^ (w m) j` (for all test schemes, points `x` and
  `m : I' → ℤ`), for the same `w : (I' → ℤ) → (I → ℤ)`, are equal.

Section `Pinned`:

- `affinePinned_hom_eq`: for `G` as in `Rigidity` (only the hypotheses on `G` are
  needed; `H` only needs `IsAffineHom H.X.hom`), pinnings `b, X` and `b', Y`,
  `f : RootPairing.Equiv Q P` with `hf`, and isomorphisms `φ ψ : G ≅ H` with
  `i ≫ φ.hom = τ ≫ i'` and `i ≫ ψ.hom = τ ≫ i'` for the same `τ`, and both sending
  `(X ⟨f.indexEquiv a', _⟩ 1).val` to `(Y a' 1).val` under the Lie algebra map: `φ = ψ`.
- `affinePinnedIsomorphism_unique`: the uniqueness half in the exact shape of the
  target statement. Its binders are those of `AffinePinnedIsomorphismTheoremStatement`
  (`R, G, H, hG, hH, I, I', i, i', J, J', P, Q`, the instances `IsAffineHom` from
  `hG.isAffineHom`, `hH.isAffineHom` by `haveI`, the four hypotheses on `(G, i, P)`, and
  `b, b', X, Y, f, hf`), but it omits the four hypotheses on `(H, i', Q)`, which are not
  needed. Then for `φ ψ : G ≅ H`, if each satisfies the property inside the target's
  `∃!` (a torus isomorphism `τ` with `i ≫ φ.hom = τ.hom ≫ i'` and the character
  identity for `f.weightMap`, and compatibility with the pinnings), then `φ = ψ`.
  Combined with an existence proof, `fun ψ hψ => affinePinnedIsomorphism_unique … ψ φ hψ hφ`
  supplies the uniqueness part of `∃!`.

## Proofs

- `hom_ext_of_localBaseChange`: by `Grp.hom_ext` it suffices to compare the underlying
  morphisms of schemes over `Spec R`, and by the Library's
  `CellGluing.hom_ext_of_localRingPoints` (the target is affine) it suffices to compare
  them on points `q : Spec A → G` with `A` a local ring. Such a point makes `A` an
  `R`-algebra through `Spec.preimage` of its structure map, and is then the image of an
  `A`-point of `G_A` under `baseChangePointsEquiv`; the hypothesis for this `A` and
  `baseChangePointsEquiv_comp` give `q ≫ f = q ≫ F`.
- `baseChangeHom_comp_of_comp_eq`: `baseChangeHom` is an isomorphism followed by the
  base change of `i`; use functoriality. `isClosedSubgroup_baseChangeHom`: a closed
  immersion is stable under base change (`IsClosedSubgroup.baseChange`) and composition
  with an isomorphism.
- `simpleRoot_comp_eq_of_fixes`: `IsRootParametrization.comp_eq_of_fixes_weightSpace`
  from [`AffineRootLieDerivative`](AffineRootLieDerivative.md), with
  `isRootParametrization_rootParametrizationsOfFreeWeights` and `P.ne_zero a`.
- `baseChange_map_eq_id_of_fixes`: base change to `A` preserves all hypotheses
  (`IsReductive.baseChange`, `isClosedSubgroup_baseChangeHom`,
  `splitTorus.isFibrewiseMaximalTorus_baseChangeHom`, `hP.baseChange_implicit`,
  `baseChangeHom_comp_of_comp_eq`). Let `U = simpleRootFamilyLocal …` be the Library's
  chosen normalized simple-root family of `G_A` (`simpleRootFamilyLocal_spec` gives its
  root-parametrization and Weyl properties).
  - For a simple root `a`, `U a` and the base change of the global parametrization
    `rootParametrizationsOfFreeWeights … a` (`isRootParametrization_baseChangeRoot`)
    parametrize the same nonzero root, so `U a = scaleHom c ≫ baseChangeRoot A u`
    (`exists_scalar_of_ne_zero`). Since `u ≫ σ.hom = u` by
    `simpleRoot_comp_eq_of_fixes`, `U a ≫ σ_A = U a`.
  - For the opposite root `-a`, `U(-a) ≫ σ_A` is again a parametrization of `-a`
    (`IsRootParametrization.comp_iso`), hence equals `scaleHom (d a) ≫ U(-a)` for some
    `d a ∈ A` (`choose!` collects these).
  - So `σ_A` and `𝟙` satisfy the power formulas `HasSimpleRootPowerFormulas` with
    `q = 1`, `c = 1`, `e = id` and opposite coefficients `d` and `1`, and agree on the
    torus. The Library's `hom_ext_of_chosenSimpleRootPowerFormulas` (over the local ring
    `A`) gives `σ_A = 𝟙`. The opposite coefficients `d a` and `1` may differ; that
    theorem does not require them to agree.
- `iso_eq_refl_of_fixes`: `G.X.left` is affine (`isAffine_of_isAffineHom`); apply
  `hom_ext_of_localBaseChange` to `σ.hom` and `𝟙 G`, and `baseChange_map_eq_id_of_fixes`
  with `Functor.map_id`.
- `iso_eq_refl_of_fixes_pinning`: `fixes_weightSpace_of_fixes_generator` turns
  the generator condition into `hX`.
- `splitTorus_hom_eq_of_characters`: testing the identity at `m = Pi.single j' 1` gives
  `τ(x)_{j'} = τ'(x)_{j'}` for every coordinate; apply this to the universal point
  `x = 𝟙` and conclude by `Grp.hom_ext`.
- `affinePinned_hom_eq`: `σ := ψ ≪≫ φ.symm` satisfies `i ≫ σ.hom = i` (from the two
  torus equations and `φ.hom ≫ φ.inv = 𝟙`). For a simple root `a = f.indexEquiv a'`,
  `dσ(X_a) = dφ⁻¹(dψ(X_a)) = dφ⁻¹(Y_{a'}) = dφ⁻¹(dφ(X_a)) = X_a` by
  `Lie.targetMapLinear_comp` and `Lie.targetMapLinear_id`; every element of `b.support`
  is of this form since `f.indexEquiv` is a bijection matching the bases. So
  `iso_eq_refl_of_fixes_pinning` gives `σ = Iso.refl G`, i.e. `ψ.hom ≫ φ.inv = 𝟙`,
  hence `ψ.hom = φ.hom`.
- `affinePinnedIsomorphism_unique`: the torus isomorphisms `τ`, `τ'` attached to `φ` and
  `ψ` satisfy the character identity for the same `f.weightMap`, so `τ.hom = τ'.hom` by
  `splitTorus_hom_eq_of_characters`; then apply `affinePinned_hom_eq`.

## Relation to the source

Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I (2014),
registered as `conrad-2014-reductive-group-schemes`. Proposition 6.1.13(2), pp.194–195:
an isogeny compatible with splittings "is uniquely determined by R(f) and the pinnings".
The Markdown of the target statement derives uniqueness from it applied to
`φ₂⁻¹ ∘ φ₁`; this module follows that route over an affine base. The Lean proof uses the
Library's local-ring rigidity (`hom_ext_of_chosenSimpleRootPowerFormulas`, a homomorphism
over a local base is determined by the torus and the simple root groups and their
opposites) together with reduction to local rings, instead of Conrad's argument with the
open cell over a general base. The Lie algebra step (a parametrization is determined by
its derivative) is the content of Lemma 6.1.4 used in the source's definition of
compatibility with pinnings.

## Scope

- Only uniqueness is proved; existence (the isomorphism compatible with splittings and
  pinnings) is not addressed here.
- `affinePinnedIsomorphism_unique` is not the target statement; it is the second half of
  its `∃!`, and assumes only the hypotheses on `G`.
