# Torus cocycles of simply connected groups of type E₇ have order dividing 36

Module: `Langlands.GroupScheme.Rational.TypeE7MaximalTorusCocycleOrderProof`.

## Main result

`typeE7MaximalTorusCocycleOrder` proves the Library proposition
`TypeE7MaximalTorusCocycleOrderStatement` (module
`Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE7Inputs`). Let `G` be a simply
connected group over a field `K` with Tits index data whose Cartan matrix is
`CartanMatrix.E 7`, let `i : T ⟶ G` be a maximal `K`-torus, and let `τ` be a cocycle of `T` on
the cover `Spec L → Spec K` of a finite Galois extension `L/K`. The proof takes `a = b = 2`:
the cocycle `τ.map (CommGroupScheme.groupHom (36 • 𝟙 T))`, whose values are the `36`-th powers
of those of `τ`, is trivial.

The argument shows that `36 • 𝟙 T` factors through an induced torus. Let `X` be the character
lattice of `T` over a splitting field, `Φ ⊆ X` its roots in `G` and `ℤ[Φ]` the free abelian
group on `Φ`, a Galois permutation module. The maps

- `ℤ[Φ] → X`, `[α] ↦ α`, and
- `X → ℤ[Φ]`, `x ↦ ∑_α ⟨x, α^∨⟩ [α]`,

are Galois equivariant, and their composite `X → X` is `x ↦ ∑_α ⟨x, α^∨⟩ α = 36 x` by the
Casimir identity for `E₇` (module `Langlands.LinearAlgebra.E7Casimir`). The torus `Q` with
character lattice `ℤ[Φ]` is induced, so its cocycles are trivial, and the `36`-th power of
`τ` is the pushforward along `Q → T` of the trivial cocycle `τ.map (T → Q)`.

The proof does not use the hypothesis `IsAbsolutelyAlmostSimple G`, and the triviality of
cocycles of induced tori (`isTrivial_of_isInducedTorus`) is proved on the cover of an arbitrary
field extension `L/K`.

## Auxiliary results

### The permutation lattice of the roots

For a monoid `Γ` acting on a root datum `P : RootDatum ι M N` through `act : Γ →* P.Aut`:

- `rootRep P act` is the permutation representation of `Γ` on `ι →₀ ℤ` induced by the index
  bijections (`rootRep_single`).
- `rootCombination P : (ι →₀ ℤ) →ₗ[ℤ] M` sends `[i]` to `P.root i`, and
  `corootCoefficients P : M →ₗ[ℤ] (ι →₀ ℤ)` sends `x` to `∑ᵢ ⟨x, αᵢ^∨⟩ [i]`.
- `rootCombination_rootRep` and `corootCoefficients_weightMap` say that both maps intertwine
  `rootRep P act` with the weight maps of the action; the second uses
  `E7Casimir.toLinearMap_weightMap_coroot_indexEquiv`.
- `rootCombination_corootCoefficients`: the composite is `x ↦ ∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ`.

### Galois pinning data with a prescribed torus

`GaloisPinningData.ofSplittingField` builds, from a maximal torus `i : T ⟶ G` of a connected reductive
`G` and a field `E` over which `T` splits, Galois pinning data over `E` whose torus is `T`
(`pinningDataOfSplittingField_torus`). The root datum is the one supplied by
`rootDatumExistence` for the split maximal torus `T_E` of `G_E`, the base is
`Langlands.LinearAlgebra.RootDatumBase.base`, and the pinning is
`RootPinning.ofSplitMaximalTorus`. This is the construction used inside the module
`Langlands.GroupScheme.Reductive.AbsoluteStarAction`, made available with the torus fixed.

### Factorization through an induced torus

`exists_inducedTorus_comp_eq_zsmul`: let `E/k` be finite Galois and `d` Galois pinning data over
`E` with torus `T` and root datum `P`. If `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = n x` for every character `x`, then
there are an induced torus `Q` and homomorphisms `f : T ⟶ Q`, `g : Q ⟶ T` with
`f ≫ g = n • 𝟙 T`. Proof:

1. `ρ = rootRep P d.galoisAction` is the permutation representation of `Gal(E/k)` on `ℤ[Φ]`.
   `torusGaloisLatticeRealization` gives a torus `Q` split by `E` with a Galois-equivariant
   identification `eQ` of its character lattice with `ℤ[Φ]`. As `ρ` permutes the basis
   `Finsupp.basisSingleOne`, `isInducedTorus_of_equivariant_basis` shows that `Q` is induced.
2. The Galois action on the root datum agrees with the Galois action on the characters of `T`
   (`StarActionIndependence.galoisAction_weightMap_apply`). Hence the character maps
   `F₁ = rootCombination P ∘ eQ⁻¹ : X(Q) → X(T)` and
   `F₂ = eQ ∘ corootCoefficients P : X(T) → X(Q)` are equivariant.
3. `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap` gives `f : T ⟶ Q` with
   character pullback `F₁` and `g : Q ⟶ T` with character pullback `F₂`. The character pullback
   of `f ≫ g` is `F₁ ∘ F₂ = (x ↦ ∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ) = n • id`, which is also the character
   pullback of `n • 𝟙 T` (`TorusSurjectionIsogenySection.baseChange_map_zsmul_id`). The
   uniqueness part of the same lemma gives `f ≫ g = n • 𝟙 T`.

### Cocycles of induced tori

`isTrivial_of_isInducedTorus`: every cocycle of an induced torus `Q` over `K` on the cover
`Spec L → Spec K` of an arbitrary field extension is trivial. By
`inducedTorusWeilDecomposition`, `Q` is isomorphic to the Weil restriction of `𝔾_m` from a
finite product of finite field extensions of `K`. The cover is affine, flat and surjective
(`fieldExtension_fpqc`), and `K` is semilocal, so
`Cocycle.isTrivial_of_weilPresentation_of_semilocal` applies.

`isTrivial_map_comp`: if `τ.map φ` is trivial, so is `τ.map (φ ≫ ψ)`.

## Proof of the main theorem

1. `G` is connected reductive (it is semisimple by the Tits index data).
   `torusFiniteGaloisSplitting` gives a finite Galois extension `E/K` splitting `T`, and
   `GaloisPinningData.ofSplittingField` gives Galois pinning data `d'` over `E` with torus `T`.
2. An embedding `E →ₐ[K] Kˢᵉᵖ` (`IsSepClosed.lift`) and `StarActionFiniteStage.exists_lift` give
   Galois pinning data `pd` over the separable closure `Kˢᵉᵖ` and an equivalence
   `e₁` from the root datum of `d'` to that of `pd`. `StarActionIndependence.starActionIndependence`
   gives an equivalence `e₂` from the root datum of the pinning data `d.pinning` of the Tits index
   to that of `pd`.
3. For the root datum `P₀` of `d.pinning`, the simple roots numbered through `e` have Cartan
   matrix `CartanMatrix.E 7` by the hypothesis on `d.cartan`. `G_{Kˢᵉᵖ}` is simply connected
   (`isSimplyConnectedFieldExtension`), so the coroots of `P₀` span the cocharacter lattice
   (`splitSimplyConnectedCorootSpanIndependent`). `E7Casimir.sum_toLinearMap_coroot_smul_root`
   gives `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = 36 x` for `P₀`. Transport along `e₂`
   (`E7Casimir.sum_toLinearMap_coroot_smul_root_of_equiv`) and back along `e₁`
   (`E7Casimir.sum_toLinearMap_coroot_smul_root_of_equiv_symm`) gives the same identity for the
   root datum of `d'`.
4. `exists_inducedTorus_comp_eq_zsmul d' 36` gives an induced torus `Q` and `f : T ⟶ Q`,
   `g : Q ⟶ T` with `f ≫ g = 36 • 𝟙 T`. The cocycle `τ.map f` is trivial by
   `isTrivial_of_isInducedTorus`, hence so is `τ.map (f ≫ g)` by `isTrivial_map_comp`. Since
   `(2 ^ 2 * 3 ^ 2 : ℕ) • 𝟙 T = 36 • 𝟙 T = f ≫ g`, this is the required cocycle.

## Relation to the literature

The statement is the `E₇` case of Platonov and Rapinchuk, *Algebraic Groups and Number
Theory* (1994), Proposition 6.21, for classes represented on a field cover. The Lean proof does
not follow the argument there: it replaces it by the factorization of `36 • 𝟙 T` through the
induced torus with character lattice `ℤ[Φ]`, which uses only the Casimir identity
`∑_α ⟨x, α^∨⟩ α = 36 x` of the root datum of `E₇` and the triviality of cocycles of induced
tori.
