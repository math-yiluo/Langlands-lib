# Class functions vanishing on a maximal torus

Author: Worker 1804.

This module is a helper for the proof of
`Langlands.GroupScheme.SplitFundamentalCharacterGenerationStatement`. That proof
needs restriction of class functions to a split maximal torus to be injective.
Here the field `k` is algebraically closed of arbitrary characteristic. The
results are conditional on the Library statement
`Langlands.GroupScheme.BorelPointContainmentStatement` ("every rational point
lies in a Borel subgroup", Milne, Corollary 17.34). It is taken as the explicit
hypothesis `hP1`, because no proof of it is published yet. Everything is in
namespace `Langlands.GroupScheme.ClassFunctions`.

## Definition

- `VanishesOnTorusPoints jT f`, for `G : GroupScheme (Spec (CommRingCat.of k))`
  with `[IsAffineHom G.X.hom]`, `T : CommGroupScheme (Spec (CommRingCat.of k))`,
  a homomorphism `jT : T.toGrp ⟶ G` and `f : algebra G`, is the proposition
  `∀ s : Lie.AffinePoints T.toGrp k,
    Lie.pointCoordinates G (s ≫ jT.hom.hom) f.val = 0`.
  It says that `f` vanishes at the image under `jT` of every affine `k`-point
  of `T`. Here `algebra G` is the invariant subalgebra of the coordinate
  algebra, that is, the algebra of regular class functions.

## Main results

Both results assume:

- `hP1 : BorelPointContainmentStatement.{u}`;
- `k : Type u` is a field with `[IsAlgClosed k]`;
- `G : GroupScheme (Spec (CommRingCat.of k))` has `[IsAffineHom G.X.hom]` and
  `hG : IsConnectedReductive G`;
- `jT : T.toGrp ⟶ G` is a maximal torus (`hjT : IsMaximalTorus jT`), with
  `T : CommGroupScheme (Spec (CommRingCat.of k))`.

The torus `T` is not assumed split.

- `exists_torusPoint_rho_eq hP1 hG hjT y`: for every rational point
  `y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X` there is a rational point
  `t : 𝟙_ _ ⟶ T.X` such that `y ≫ rho G = (t ≫ jT.hom.hom) ≫ rho G`. So `y`
  and the torus point `t` have the same image in the canonical class-function
  quotient `rho G`.
- `eq_zero_of_vanishesOnTorusPoints hP1 hG hjT f hf`: let `f : algebra G` be
  a regular class function with `hf : VanishesOnTorusPoints jT f`, so `f`
  vanishes at every `k`-point of the maximal torus. Then `f = 0`.

## Proofs

`exists_torusPoint_rho_eq` adapts the opening steps of Worker 1531's published
proof `algClosedStronglyRegularFibres_of`, in
`Langlands/GroupScheme/Rational/ClassFunctionsAlgClosedStronglyRegularFibres.lean`.
The steps are:

1. `hP1` puts `y` in a Borel subgroup `B`.
2. `borelMaximalTorus` gives a maximal torus `T₁` of `G` inside `B`. It is
   split by `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites`.
3. `regularCocharacterBorel` gives a regular cocharacter `ν` of `T₁` whose
   dynamic parabolic is `B`. So `y` lies in the parabolic of
   `χ = ν ≫ jT₁`.
4. The dynamic limit `t = Dynamic.limit χ ⟨y, _⟩` lies in the centralizer of
   `χ`. By regularity (`centralizer_comp_eq_range_of_isRegular`) that
   centralizer is `T₁`, so `t` comes from a point `t₀` of `T₁`. By `rho_limit`,
   `y ≫ rho G = t ≫ rho G`.
5. The maximal tori `T₁` and `T` are conjugate, and
   `AlgClosedFibres.exists_conj_eq_comp_of_isTorus` turns this into
   `g * (t₀ ≫ jT₁) * g⁻¹ = t' ≫ jT` for a point `t'` of `T`.
6. `rho` is conjugation invariant (`rho_conjugation`), which gives the claim
   for `t'`.

`eq_zero_of_vanishesOnTorusPoints` has three steps:

1. *Every rational point.* An affine `k`-point `x : Lie.AffinePoints G k` is
   transported to a base point through the isomorphism
   `PointTopology.ringTestSelfIso k` between the affine test `Spec k` and the
   monoidal unit. `exists_torusPoint_rho_eq` then gives a torus point with the
   same `rho`-image. `evaluation_eq_of_rho_eq` and `hf` show that `f` vanishes
   at `x`.
2. *Nullstellensatz.* The coordinate algebra `Coord G` is a domain
   (`CharacterLatticeProof.isDomain_coord`, which uses smoothness and
   connectedness of `G`). It is of finite type over `k`
   (`Lie.coordinateAlgebraFiniteType`). Suppose `f.val ≠ 0`. Then
   `BorelFieldExtension.exists_algHom_ne_zero` gives a `k`-algebra map
   `φ : Coord G →ₐ[k] k` with `φ f.val ≠ 0`.
3. *Contradiction.* The point `(Lie.pointCoordinates G).symm φ` is a rational
   point at which `f` does not vanish, contradicting step 1. Hence `f = 0`, by
   `Subtype.ext`.

## Provenance

This is internal helper development for task `03d6e581` (proof of
`SplitFundamentalCharacterGenerationStatement`). The mathematical content is
standard: it is part of Chevalley's restriction theorem. A regular class
function on a connected reductive group over an algebraically closed field is
determined by its restriction to a maximal torus, because every element is
conjugate into a Borel subgroup and its semisimple part is conjugate into the
torus. The Lean route, through dynamic limits and the canonical quotient
`rho`, reuses the published Library argument named above. It is not claimed to
follow a specific text.
