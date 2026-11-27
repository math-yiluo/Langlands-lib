# Monodromy over a field: finite étale and ℓ-adic

Laumon (1987), (2.1.2), p. 152, calls a `G`-module a finite-dimensional `ℚ̄_ℓ`-vector space
with an action of the Galois group `G` defined over a finite extension of `ℚ_ℓ` in `ℚ̄_ℓ` and
continuous for the ℓ-adic topology. Remarque (2.1.2.1) says that the choice of the geometric
point `η̄` identifies `ℚ̄_ℓ`-sheaves on the generic point `η` with `G`-modules by the fibre
functor at `η̄`. For the spectrum of a field, the profinite identification of the
fundamental group with `Gal(K^sep/K)` is Stacks Project, Lemma 58.6.3 (Tag 0BNE), with the
functoriality of Theorem 58.6.2(3) (Tag 0BND) for a morphism of connected schemes, compatible
with base change of finite étale covers; the equivalence between étale sheaves on `Spec K`
and discrete Galois sets by the stalk with its transport-of-structure action is
Theorem 59.56.3 (Tag 03QT). Katz (1986) uses the same pattern for lisse sheaves on `𝔾_m`:
Lemma 1.5.3, p. 84, reads lisse sheaves of modules over a finite ring as representations on
finite modules of the special quotient of `π₁(𝔾_m)`, and Theorem 1.5.6, p. 85, passes to
profinite adic coefficient rings, through the finite quotient rings, for the
canonical-extension equivalence. This module states these identifications for an
arbitrary field `K` with an arbitrary separable closure `Ω` (Mathlib's `IsSepClosure K Ω`),
both in one universe `u`, with weil-conjectures's sheaves and the Library's ℓ-adic predicates.

## The geometric point and the Galois action

The lisse sheaves, fibre functors and monodromies of weil-conjectures use geometric points
valued in an algebraic closure. Here `Ω̄ = AlgebraicClosure Ω`.

- `fieldGeometricPoint K Ω` is `Spec Ω̄ → Spec Ω → Spec K`, i.e. weil-conjectures's
  `AlgebraicGeometry.Scheme.FiniteEtale.pointOfAlgebra Ω̄ (𝟙 (Spec K))`.
- `algebraicClosureRestriction K Ω` restricts `K`-automorphisms of `Ω̄` to `Ω`
  (Mathlib's `AlgEquiv.restrictNormalHom`; `Ω` is normal over `K`).
  `algebraicClosureRestriction_bijective` proves it bijective. Surjectivity holds because `Ω̄`
  is normal over `K`. Injectivity holds because `Ω̄` is purely inseparable over the separably
  closed field `Ω` (Mathlib's `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`), so
  two automorphisms that agree on `Ω` agree on `Ω̄`
  (`IsPurelyInseparable.injective_comp_algebraMap`).
- `fieldGaloisLift K Ω : Gal(Ω/K) ≃* Gal(Ω̄/K)` is the inverse equivalence: the unique
  extension of an automorphism of `Ω` to `Ω̄`.
- `fieldGaloisToAut K Ω` composes this lift with weil-conjectures's
  `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut`, through which `σ` acts on the fibre
  functor of finite étale `K`-schemes at the geometric point by precomposing a point
  `Spec Ω̄ → P` with `Spec σ`.

## The monodromy representation

- `fieldMonodromy ℓ K Ω G` is the representation of `Ω ≃ₐ[K] Ω` on the `E`-linear stalk
  `AlgebraicGeometry.ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G` of an
  arithmetic lisse sheaf `G : AlgebraicGeometry.ProEtale.LisseSheaf ℓ (Spec K)`, with
  `E = PadicAlgCl ℓ`. It is the monodromy `AlgebraicGeometry.ProEtale.LisseMonodromy.rep` of
  weil-conjectures's `AlgebraicGeometry.ProEtale.universalLisseMonodromy ℓ (Spec K) Ω`,
  composed with `fieldGaloisToAut K Ω`. The lift from `Ω` to `Ω̄` is the constructed
  `fieldGaloisLift K Ω`.
- `fieldMonodromyRepresentation ℓ K Ω G` bundles it with `Langlands.FiniteRepresentation.of`
  on the stalk itself, a carrier in universe `u + 1`. Finite-dimensionality is
  weil-conjectures's instance `finiteDimensional_stalkSpace`.
- `lisseStalkMap ℓ K Ω f` is the `E`-linear map of stalks of a morphism `f` of lisse sheaves.
  It intertwines the monodromy representations by weil-conjectures's `rep_naturality`.
  `fieldMonodromyFunctor ℓ K Ω` is the resulting functor from lisse sheaves to
  `Langlands.FiniteRepresentation.{0, u, u + 1} E (Ω ≃ₐ[K] Ω)`; its functor laws are proved
  from those of the stalk functor.
- `adicStalkMap ℓ K Ω f` is the stalk map at the same point of a morphism of arbitrary
  `ℓ`-adic sheaves `AlgebraicGeometry.ProEtale.AdicSheaf ℓ (Spec K)`.

## `FiniteEtaleFieldMonodromyStatement`

For every field `K` and separable closure `Ω`:

1. `fieldGaloisToAut K Ω` is a homeomorphism (`IsHomeomorph`) from `Ω ≃ₐ[K] Ω` with Mathlib's
   Krull topology onto the automorphism group of the finite étale fibre functor at
   `fieldGeometricPoint K Ω`, with Mathlib's topology on automorphism groups of fibre
   functors. Being a monoid homomorphism, it is an isomorphism of topological groups. This is
   the profinite identification of the fundamental group of `Spec K` (Stacks Project,
   Lemma 58.6.3) used in Laumon (2.1.2.1).
2. For every commutative ring `Λ` there are an equivalence `e` from étale sheaves of
   `Λ`-modules on `Spec K` to `Rep.DiscreteContinuousRep Λ (Ω ≃ₐ[K] Ω)` (weil-conjectures's
   category of representations with open stabilizers) and an isomorphism `i` from its
   underlying `Λ`-module to the stalk at the geometric point `Spec Ω → Spec K`
   (`AlgebraicGeometry.Scheme.pointSmallEtale` and its `sheafFiber`), such that `σ` sends the
   germ of a section `z` at a lift `x` to the germ of `z` at a lift `x'` with
   `x' = Spec σ ≫ x`. This is the transport-of-structure action of
   `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRepForgetIso_ρ`, which
   weil-conjectures proves for `Λ = ℤ` (Stacks Project, Theorem 59.56.3).
3. **Change of field.** For a field extension `L` of `K`, a separable closure `Ω_L` of `L` and
   a `K`-embedding `ι : Ω → Ω_L`, and every sheaf `F` of `Λ`-modules on `Spec K`, there is an
   isomorphism `c` from the stalk of `F` at `Spec Ω → Spec K` to its stalk at
   `Spec Ω_L → Spec L → Spec K` sending the germ at a lift `x` to the germ at the lift
   `Spec ι ≫ x`. Under `c` and the identification `i` of clause 2 (for the same equivalence
   `e`), the action of `σ` on `e F` corresponds to the transport action of any
   `τ ∈ Gal(Ω_L/L)` that restricts to `σ` along `ι` (`ι ∘ σ = τ ∘ ι`), which sends the germ at
   a lift `y` to the germ at `Spec τ ≫ y`. The stalk of `F` at `Spec Ω_L → Spec L → Spec K`
   with this action of `Gal(Ω_L/L)` is the stalk of the inverse image of `F` on `Spec L` at
   its geometric point, with the action of clause 2 for `L` (stalks of inverse images are
   stalks at the composite point). So inverse image along `Spec L → Spec K` corresponds to
   restriction along the continuous map `Gal(Ω_L/L) → Gal(Ω/K)`, compatibly with the
   identifications of the stalks (Stacks Project, Theorem 58.6.2(3) for finite étale covers,
   and Section 59.56).

The statement is more general than the finite-level identification asked for. It covers
every coefficient ring, not only finite ones, and every étale sheaf, not only the finite
locally constant ones. Through `i`, the finite locally constant sheaves of `Λ`-modules
correspond to the representations on finite `Λ`-modules, compatibly with the stalk and its
Galois action. Over a field no condition on `ℓ` is needed. The stalk is read at `Spec Ω`,
where weil-conjectures's points of the small étale site live; the finite étale fibre functor
is read at `Spec Ω̄`, as in weil-conjectures. Change of field is stated on stalks, as the
inverse-image functor of étale sheaves along `Spec L → Spec K` is not among the declarations
this module uses.

## `LadicFieldMonodromyStatement`

The first conjunct holds for every prime `ℓ`, every field `K` and every separable closure `Ω`:

1. Every `fieldMonodromyRepresentation ℓ K Ω G` satisfies the Library's
   `Langlands.Henniart.LocalNumerical.IsLadicContinuous` (continuity into the endomorphisms
   with their module topology) and
   `Langlands.Henniart.LocalNumerical.IsLadicDefinedOverFiniteExtension` (all matrix
   entries in one basis lie in a finite extension of `ℚ_ℓ`): Laumon's two conditions in
   (2.1.2).
2. `fieldMonodromyFunctor ℓ K Ω` is full and faithful, i.e. bijective on morphisms.
3. Every `A : FiniteRepresentation.{0, u, uW} E (Ω ≃ₐ[K] Ω)` satisfying both predicates, in
   any carrier universe `uW`, is equivalent to some `fieldMonodromyRepresentation ℓ K Ω G`.
4. Exactness: for a short exact sequence `S` in the abelian category of `ℓ`-adic sheaves on
   `Spec K` whose three terms are lisse, the stalk maps `adicStalkMap` form a short exact
   sequence of `E`-vector spaces.
5. Tensor products: for lisse `G` and `H`, the tensor product `G ⊗ H` over the constant sheaf
   `ℚ̄_ℓ` (weil-conjectures's `CategoryTheory.Mod.tensorLeft`, the tensor product of modules
   over a commutative monoid) is lisse, and there are `E`-linear isomorphisms `θ_{G,H}` from
   its stalk to the tensor product of the stalks that intertwine its monodromy with Mathlib's
   tensor product `Representation.tprod` of the two monodromy representations and are
   natural in both lisse sheaves: for morphisms `f : G → G'` and `g : H → H'`,
   `θ_{G',H'}` carries the stalk map of `f ⊗ g` (built from `Mod.tensorLeft` and
   `Mod.tensorLeftMap`) to `TensorProduct.map` of the stalk maps of `f` and `g`.
6. `G` is a simple object of the lisse category exactly when its monodromy representation is
   irreducible (`Representation.IsIrreducible`, which includes positive rank).

The second conjunct holds for every nonarchimedean local field `K`, separable closure `Ω` and
positive rank `n`. Every class `c` in the Library's `IrreducibleLadicClass K Ω ℓ n`, in any
carrier universe `uW`, is the class of the monodromy representation of a simple lisse sheaf:
it is equivalent to every representative of `ladicClassForget K Ω ℓ c`. Conversely, every
simple lisse sheaf of rank `n` has its monodromy representation in such a class.

Together, items 1–3 say that the monodromy is an equivalence from arithmetic lisse sheaves on
`Spec K` onto Laumon's `G`-modules, as in (2.1.2.1); item 4 is exactness and item 5 is the
compatibility with tensors. The statement holds for every prime `ℓ`, including `ℓ` equal to
the characteristic of `K`, because weil-conjectures's monodromy equivalence
`AlgebraicGeometry.ProEtale.universalLisseMonodromy_isEquivalenceAt` holds for every
connected regular Noetherian scheme without a condition on `ℓ`. This module does not prove
the statement; bridge (b1) of the
[design note on Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md)
describes a route through compact matrix descent and stable lattices.

## External declarations

The module imports `Langlands.MathlibBase`, `Langlands.Correspondence.HenniartLadicClasses`
and three modules of weil-conjectures. The following forty weil-conjectures declarations are
all those that occur directly in the elaborated types and values of the declarations of this
module, including the auxiliary `_proof_n` declarations generated by elaboration and the
synthesized instance arguments. Each depends only on `propext`, `Classical.choice` and `Quot.sound` under
`#print axioms`.

| Declarations | Use |
|---|---|
| `AlgebraicGeometry.Scheme.FiniteEtale`, `AlgebraicGeometry.Scheme.FiniteEtale.fiber` | category of finite étale schemes over `Spec K` and its fibre functor at the geometric point, whose automorphism group is the codomain of `fieldGaloisToAut` |
| `AlgebraicGeometry.Scheme.FiniteEtale.pointOfAlgebra`, `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut` | geometric point and Galois action on the fibre functor |
| `AlgebraicGeometry.ProEtale.LisseSheaf`, `AlgebraicGeometry.ProEtale.adicLisseSheaf`, `AlgebraicGeometry.ProEtale.lisseStalk`, `AlgebraicGeometry.ProEtale.stalkFunctor`, `AlgebraicGeometry.ProEtale.LisseMonodromy.StalkSpace` | lisse sheaves and stalks |
| `AlgebraicGeometry.ProEtale.universalLisseMonodromy`, `AlgebraicGeometry.ProEtale.LisseMonodromy.rep`, `AlgebraicGeometry.ProEtale.LisseMonodromy.rep_naturality`, `AlgebraicGeometry.ProEtale.LisseMonodromy.finiteDimensional_stalkSpace` | monodromy representation, its functoriality and the finite dimension of the stalk |
| `AlgebraicGeometry.IsRegular.spec_field`, `AlgebraicGeometry.Scheme.Modules.instNonemptyCarrierCarrierCommRingCatSpecOf_weilConjectures`, `AlgebraicGeometry.Scheme.Modules.instSubsingletonCarrierCarrierCommRingCatSpecOf_weilConjectures` | instances on `Spec K` (it is regular; its underlying space is nonempty with at most one point) synthesized for the regularity and topological hypotheses of `universalLisseMonodromy` in `fieldMonodromy` and the functor laws of `fieldMonodromyFunctor` |
| `IsRegularLocalRing.isDomain`, `IsStrictlyHenselianLocalRing.toHenselianLocalRing`, `AlgebraicGeometry.Scheme.isStrictlyHenselianLocalRing_of_isSepClosed` | instances synthesized in the proof of `algebraicClosureRestriction_bijective` |
| `AlgebraicGeometry.ProEtale.AdicSheaf`, `AlgebraicGeometry.ProEtale.AdicSheaf._proof_1`, `AlgebraicGeometry.ProEtale.AdicSheaf.forget`, `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf` | ℓ-adic sheaves (with the auxiliary proof generated by the definition of `AdicSheaf`), their underlying sheaves and lisseness |
| `AlgebraicGeometry.WeilCoefficients`, `AlgebraicGeometry.WeilCoefficients.toModuleCat` | coefficient category of the sheaves and its functor to modules, used for the stalk maps and stalk functors |
| `AlgebraicGeometry.ProEtale.adicConstantSheaf`, `AlgebraicGeometry.ProEtale.adicConstantSheaf.monObj`, `AlgebraicGeometry.ProEtale.adicConstantSheaf.isCommMonObj`, `AlgebraicGeometry.ProEtale.sheafMonoidalCategory`, `AlgebraicGeometry.ProEtale.sheafBraidedCategory` | the constant coefficient sheaf as a commutative monoid object of the monoidal sheaf category, over which `AdicSheaf` consists of modules |
| `CategoryTheory.Mod.tensorLeft`, `CategoryTheory.Mod.tensorLeftMap`, `CategoryTheory.Mod.instPreadditive`, `CategoryTheory.ConstantScalarRestriction.fixedPreadditive` | relative tensor product of ℓ-adic sheaves and the preadditive structures used in the exactness clause |
| `AlgebraicGeometry.ProEtale.EtaleChartComparison.Pro`, `AlgebraicGeometry.ProEtale.EtaleChartComparison.proMonoidalClosed`, `AlgebraicGeometry.ProEtale.EtaleChartComparison.proMonoidalPreadditive`, `AlgebraicGeometry.ProEtale.EtaleChartComparison.proWeakSheafify`, `ModuleCat.isGrothendieckAbelian_of_commRing` | the category `Pro` of pro-étale sheaves of modules and the instances synthesized for it in `LadicFieldMonodromyStatement` (monoidal closed, monoidal preadditive, weak sheafification), with the Grothendieck abelian structure of module categories |
| `Rep.DiscreteContinuousRep` | discrete continuous representations |

This page also cites, without the Lean using them,
`AlgebraicGeometry.ProEtale.universalLisseMonodromy_isEquivalenceAt`,
`AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRep` and
`AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRepForgetIso_ρ`, which have the
same axiom status. The stalk at `Spec Ω` uses Mathlib's `AlgebraicGeometry.Scheme.pointSmallEtale`.
Every declaration of this module depends only on the same three axioms.
