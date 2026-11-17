# The absolute-Galois character anti-equivalence: proof

Workers 132 and 336.

The theorem `Langlands.GroupScheme.multiplicativeTypeAbsoluteEquivalence` proves the
proposition `Langlands.GroupScheme.MultiplicativeTypeAbsoluteEquivalenceStatement.{u}`
(module `Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceStatement`).
Fix a field `k : Type u`, write `Ω = SeparableClosure k` and `Γ = Ω ≃ₐ[k] Ω`. The
statement asserts that the published functor

```text
MultiplicativeTypeGroup.characterFunctor k :
  (MultiplicativeTypeGroup k)ᵒᵖ ⥤ FGDiscreteGaloisModule.{u,u} k
```

is an equivalence of categories (`Functor.IsEquivalence`). This functor sends a group `T`
of multiplicative type over `k` to its character group over `Ω`,
`characterLattice (T_Ω)`, with the representation
`characterLattice.galoisRepresentation k Ω T` of `Γ`. It sends a homomorphism to
precomposition with its base change to `Ω`. This is Milne, *Algebraic Groups* (2017),
Theorem 12.23, §12.g, printed pp.239–240 / PDF pp.255–256 (source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The original pages and complete retained official 2017 errata were checked; no
correction affects this passage. The target retains all ground-field group-scheme
homomorphisms and all equivariant integral linear maps.

The proof registers three instances in the namespace
`Langlands.GroupScheme.MultiplicativeTypeGroup`: `characterFunctor_faithful`,
`characterFunctor_full` and `characterFunctor_essSurj`. Then the final theorem is
`fun _ _ => { }`, because Mathlib's `Functor.IsEquivalence` has exactly these three
fields. The auxiliary declarations are in the namespace
`Langlands.GroupScheme.MultiplicativeTypeAbsoluteEquivalence`. None is private.

## Route

Milne defines a quasi-inverse using the invariant coordinate algebra of `D_Ω(M)`
and deduces the equivalence from split diagonalizable duality and Galois descent.
This Lean proof uses that descent principle for full faithfulness. For essential
surjectivity it imports the finite-level realization by a kernel of a map between
induced tori, then proves the required comparison over `Ω`. This derives the same
canonical character equivalence using the existing Library constructions. The
internal auxiliary lemmas implement its descent and tower comparisons. The work
splits as follows.

- **Faithful and full: over `Ω` itself.** Every group of multiplicative type becomes
  diagonalizable over `Ω`. Morphisms between diagonalizable groups are determined by
  character pullback, and any additive map of character groups comes from such a
  morphism. Character separation uses points over every test scheme, which retains
  torsion characters and finite nonsmooth diagonalizable groups. A morphism over `Ω`
  that is equivariant on characters is descended to `k`
  by the published Galois descent of homomorphisms for an *arbitrary* Galois extension,
  `Descent.GaloisHom`. No finite splitting field is chosen.
- **Essentially surjective: through a finite level.** The module's action factors
  through a finite Galois subextension `L ⊆ Ω` of `k`. The published finite-level
  realization theorem produces a group whose character module over `L` is the given
  module. Its character module over `Ω` is then compared with the given module through
  the published tower lattice map `towerCharacterOf` for `k ⊆ L ⊆ Ω`.

## Imported results

- `MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic` and
  `MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`, from module
  `Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof`.
  Being of multiplicative type is preserved by algebraic extension. Over a separably
  closed field, such a group is isomorphic to `D(Λ)` for some finitely generated `Λ`.
- `MultiplicativeTypeGaloisFullFaithfulness.hom_ext_of_iso_diagonalizable`,
  `exists_hom_of_characterMap` and `galoisHomTransport_eq_of_diagonalizable`, from
  module `Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessProof`.
  These say three things. Homomorphisms into a group isomorphic to `D(Λ')` are
  determined by character pullback. Over a field, every additive map between the
  character groups of two groups isomorphic to diagonalizable groups is a character
  pullback. A morphism over `L` whose character pullback is `Gal(L/k)`-equivariant, and
  whose target is diagonalizable over `L`, is fixed by Galois transport. The extension
  `L` may be arbitrary here.
- `discreteGaloisFiniteFactorization`, from module
  `Langlands.GroupScheme.Torus.DiscreteGaloisFiniteFactorizationProof`. An action
  of `Γ` on a finitely generated module with open vector stabilizers for the Krull
  topology factors through
  `AlgEquiv.restrictNormalHom L` for some finite Galois intermediate field `L` of
  `Ω / k`.
- `multiplicativeTypeGaloisModuleRealization`, from module
  `Langlands.GroupScheme.Torus.GaloisModuleRealizationProof`. Let `L/k` be finite
  Galois, let `M` be a finitely generated abelian group and let `ρ` be a representation
  of `Gal(L/k)` on `M`. Then there are a group `T` over `k`, an isomorphism
  `i : T_L ≅ D_L(M)` and an additive isomorphism `e : M ≃+ X^*(T_L)`. The character
  `e m` is evaluation at `m` read through `i`, and `e` intertwines `ρ` with
  `characterLattice.galoisRepresentation k L T`.
- `Descent.GaloisHom.hom` and `Descent.GaloisHom.baseChange_hom`, from module
  `Langlands.GroupScheme.Descent.GaloisHom`. For a Galois extension `L/k` and affine
  group schemes `G`, `H` over `k`, take a homomorphism `f : G_L ⟶ H_L` that is
  compatible with the canonical descent isomorphisms for every `σ`. Then `f` is the
  base change of a homomorphism `G ⟶ H` over `k`.
- `StarActionFiniteStage.towerIsoOf`, `towerCharacterOf` and
  `towerCharacterOf_transport` (module
  `Langlands.GroupScheme.Reductive.StarActionFiniteStageTower`). These give the
  character map `X^*(T_L) → X^*(T_Ω)` of a tower `Spec Ω → Spec L → Spec k`, and its
  compatibility with transport along compatible automorphisms of the two levels.
- `Diagonalizable.commBaseChangeIso`, `Diagonalizable.characterPointsEquiv_baseChangeIso_hom`
  (module `Langlands.GroupScheme.Torus.DiagonalizableBaseChange`),
  `DiagonalizableCharacter.evalCharacterEquiv`, `fieldExtension_fpqc` and
  `IsMultiplicativeType.isAffineHom`.

## Auxiliary declarations

- `exists_iso_diagonalizable T hT`: `T_Ω ≅ D_Ω(Λ)` for some `Λ`. It combines the two
  imported splitting results, since `Ω/k` is algebraic and `Ω` is separably closed.
- `baseChange_map_injective L`: scalar extension of commutative group schemes along any
  field extension `k → L` is injective on homomorphisms. Since `Spec L → Spec k` is
  surjective, flat and quasi-compact (`fieldExtension_fpqc`), the pullback functor of
  over-schemes is faithful. The equality is read off on the underlying morphisms.
- `descent_compat_of_equivariant L i' f hf σ`: assume the target of `f : T_L ⟶ T'_L`
  is isomorphic to a diagonalizable group, and `f`'s character pullback is
  `Gal(L/k)`-equivariant. Then `f` satisfies the descent compatibility required by
  `Descent.GaloisHom`. This rewrites `galoisHomTransport_eq_of_diagonalizable`, which
  conjugates `f` by the descent isomorphisms.
- `baseChange_evalCharacter b Λ m`: the base change of the evaluation character at `m`
  of `D_R(Λ)` along `b : Spec R' ⟶ Spec R` is evaluation at `m` on `D_{R'}(Λ)`,
  composed with `Diagonalizable.commBaseChangeIso`. It is checked on points with
  `characterLattice.ext_points` and `characterPointsEquiv_baseChangeIso_hom`.
- `algebraBaseMap_tower L Ω`: for a scalar tower `k → L → Ω`, the base maps compose:
  `Spec Ω → Spec L → Spec k` is `Spec Ω → Spec k`.
- `galoisBaseMap_restrictNormal L σ`: for a normal intermediate field `L` and `σ ∈ Γ`,
  the inclusion `Spec Ω → Spec L` intertwines `galoisBaseMap σ` with
  `galoisBaseMap (σ|_L)`. This is `AlgEquiv.restrictNormal_commutes`.
- `exists_absolute_realization L M ρ`: the realization result read over `Ω`. Let `L` be
  a finite Galois intermediate field of `Ω/k`, `M` a finitely generated abelian group
  and `ρ` a representation of `Gal(L/k)` on `M`. Then there are a group `T` of
  multiplicative type over `k` and `Φ : M ≃+ X^*(T_Ω)` with
  `Φ (ρ (σ|_L) m) = galoisRepresentation k Ω T σ (Φ m)` for all `σ ∈ Γ`.
  *Proof.* Take `T`, `i`, `e` from `multiplicativeTypeGaloisModuleRealization`. `T` is
  of multiplicative type because `i` is an isomorphism with `D_L(M)`, and `M` is
  finitely generated.
  - Define `Φ` as evaluation `M ≃+ X^*(D_Ω(M))` followed by pullback along the
    composite isomorphism `ψ : T_Ω ≅ (T_L)_Ω ≅ D_L(M)_Ω ≅ D_Ω(M)`. These steps are the
    tower isomorphism, the base change of `i` and `commBaseChangeIso`.
  - The realization theorem's formula over every test scheme gives
    `e m = i.hom ≫ eval_m` by character extensionality.
    With `baseChange_evalCharacter` this gives
    `towerCharacterOf (e m) = Φ m`.
  - The equivariance of `e` and `towerCharacterOf_transport` then give the required
    identity. `towerCharacterOf_transport` is applied with the automorphisms
    `galoisBaseMap σ` of `Spec Ω` and `galoisBaseMap (σ|_L)` of `Spec L`, which are
    compatible by `galoisBaseMap_restrictNormal`.

## The three instances

**Faithful.** Let `f, g : Y ⟶ X` be morphisms of groups of multiplicative type with the
same image. Choose `X_Ω ≅ D_Ω(Λ)` (`exists_iso_diagonalizable`). The images agree on
every character `χ`, so `f_Ω ≫ χ = g_Ω ≫ χ` (`characterFunctor_map_apply`). Hence
`f_Ω = g_Ω` by `hom_ext_of_iso_diagonalizable`, and `f = g` by
`baseChange_map_injective Ω`.

**Full.** Let `X`, `Y` be groups of multiplicative type and let
`φ : X^*(X_Ω) → X^*(Y_Ω)` be a morphism in `FGDiscreteGaloisModule k` from the image
of `op X` to the image of `op Y`. A preimage is a homomorphism `Y ⟶ X` over `k`.
1. Choose diagonalizable models of `X_Ω` and `Y_Ω`. Then `exists_hom_of_characterMap`
   gives `f : Y_Ω ⟶ X_Ω` whose character pullback is the underlying additive map
   of `φ`.
2. Equivariance of `φ` (`isIntertwining'`) makes this pullback `Γ`-equivariant.
3. `descent_compat_of_equivariant` turns that equivariance into the descent
   compatibility. Both groups have affine structure morphisms
   (`IsMultiplicativeType.isAffineHom`), so `Descent.GaloisHom.hom` produces
   `a : Y ⟶ X` over `k` with `a_Ω = f` (`baseChange_hom`).
4. The image of `a` is then `φ`, checked on each character.

**Essentially surjective.** Let `A` be a finitely generated discrete `Γ`-module.
1. `discreteGaloisFiniteFactorization` gives a finite Galois intermediate field `L` and
   `ρL : Representation ℤ (L ≃ₐ[k] L) A` with `ρL ∘ restrictNormalHom L` equal to the
   action of `A`.
2. The `Module.Finite ℤ` instance of `A` gives `AddGroup.FG A`. Its module structure
   equals `AddCommGroup.toIntModule` by subsingletonness of `ℤ`-module structures.
3. Construct a representation for `AddCommGroup.toIntModule` by sending `g` to
   `(ρL g).toAddMonoidHom.toIntLinearMap`; its action on elements is unchanged.
   Then `exists_absolute_realization` yields `T` of multiplicative type and
   `Φ : A ≃+ X^*(T_Ω)` intertwining the action of `A` with
   `galoisRepresentation k Ω T`.
4. Then `Φ⁻¹` and `Φ` are equivariant linear maps (`intertwiningMap_of_isIntertwiningMap`).
   They give mutually inverse morphisms between `(characterFunctor k).obj (op T)` and
   `A`, so `A` lies in the essential image.

## Scope

The proof covers every field `k` in universe `u`, with no characteristic, perfectness
or smoothness hypothesis. It also covers all groups of multiplicative type (including
finite and nonreduced ones such as `μ_p` in characteristic `p`) and all finitely
generated modules, including torsion ones. It proves exactly the statement: the
specific functor `characterFunctor k` is an equivalence. Exact-sequence
compatibility remains a separate assertion.
