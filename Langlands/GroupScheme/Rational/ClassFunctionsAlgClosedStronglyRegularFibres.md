# Strongly regular fibres of the canonical quotient over an algebraically closed field

Author: Worker 1531.

This module states the algebraically closed core of
`Langlands.GroupScheme.ClassFunctions.StronglyRegularFibresStatement` and
proves it conditionally on three explicit inputs. It also combines it with the
published field transport. It proves neither the core nor the target
unconditionally. Each of the three inputs remains a hypothesis of every
theorem here.

## The core proposition

`ClassFunctions.AlgClosedStronglyRegularFibresStatement.{u}` is the following
`Prop`:

```lean
def AlgClosedStronglyRegularFibresStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsSemisimple H),
    letI : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
    ∀ (y w : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
      (S : GroupScheme (Spec (CommRingCat.of k))) (j : S ⟶ H),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ H.X),
        c * (toUnit Z ≫ w) = (toUnit Z ≫ w) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      y ≫ rho H = w ≫ rho H →
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X,
        g * y * g⁻¹ = w
```

Over an algebraically closed field `k : Type u`, `H` is a semisimple group
(the published `IsSemisimple`), and its affineness is derived from that
hypothesis. `y` and `w` are `k`-points of `H`. `S` is a torus with a closed
subgroup `j : S ⟶ H`. The all-test centralizer of `w` lies in `S`: on every
test scheme `Z`, including nonreduced ones, every point commuting with the
restriction of `w` factors through `j`. If `y` and `w` have the same image
under the canonical class-function quotient `ClassFunctions.rho H`, the
conclusion gives `g ∈ H(k)` with `g * y * g⁻¹ = w`. Nothing is assumed about
`y` beyond its quotient image.

The binder text is identical to the hypothesis `hcore` of the published
`ClassFunctions.stronglyRegularFibres_of_algClosed`
(`Rational/ClassFunctionsStronglyRegularFibresTransport`). A proof of this
proposition can therefore be supplied to it directly.

## The three inputs

- `hP1 : BorelPointContainmentStatement.{u}`
  (`Absolute/BorelPointContainmentStatement`): every `k`-point of a smooth
  affine connected group over an algebraically closed field lies in a Borel
  subgroup (Milne, Corollary 17.34).
- `hP2 : ClassFunctions.TorusSeparationStatement.{u}`
  (`Rational/ClassFunctionsTorusSeparationStatement`): two `k`-points of a
  maximal torus of a semisimple group with the same image under `rho` are
  conjugate in `G(k)` (Steinberg 1965, 6.4 and 6.6).
- `hR4`: over an algebraically closed field, let `G` be an affine group
  locally of finite type and `χ` a cocharacter. Let `t` be a `k`-point of the
  dynamic centralizer `Z(χ)` such that no nontrivial `k`-point of the
  contracting subgroup `U(χ)` commutes with `t`. Then for every
  `u ∈ U(χ)(k)` there is `v ∈ U(χ)(k)` with `v * t * v⁻¹ = u * t`. This is the
  displayed interface of the Ax–Grothendieck lemma
  `Dynamic.exists_unipotent_conj_eq_mul`, which Worker 1741 is preparing as a
  separate unit. Here it is an explicit hypothesis.

## Results

- `algClosedStronglyRegularFibres_of hP1 hP2 hR4 :
  AlgClosedStronglyRegularFibresStatement.{u}`.
- `stronglyRegularFibres_of_inputs hP1 hP2 hR4 :
  StronglyRegularFibresStatement.{u}`. It applies the published
  `stronglyRegularFibres_of_algClosed` to the published
  `ClassFunctions.fieldBaseChange` and to the previous theorem.

The namespace `ClassFunctions.AlgClosedFibres` contains four helper lemmas:

- `comp_innerIso_hom_base`: on base points, `G.innerIso g` is
  `x ↦ g * x * g⁻¹`. It specializes the published `comp_innerIso_hom`.
- `eq_one_of_mem_unipotent_of_mem_centralizer`: over any base, in a group
  with separated structure morphism, a point in both `U(χ)` and `Z(χ)` is
  `1`. Its limits `1` and `v` agree by the published `HasLimit.unique`.
- `exists_conj_eq_comp_of_isTorus`: in a smooth affine connected group over
  an algebraically closed field, every `k`-point of a closed torus `j : S ⟶ G`
  is conjugate by a point of `G(k)` to a point of any given maximal torus
  `jT`. The torus `S` is regarded as a commutative group scheme through the
  published `IsTorus.isCommMonObj`. It lies in a maximal torus `M` by the
  published `exists_maximalTorus_extension_of_finiteType`, and `M` is
  conjugate to `jT` by the published `maximalTorusConjugacy`.
- `mem_torusCentralizer_of_commute`: suppose `h * t * h⁻¹ = w` with `t` a
  base point of a commutative subgroup `jT`. Suppose the all-test centralizer
  of `w` lies in a commutative subgroup `j`. Then every base point `v`
  commuting with `t` lies in the published all-test `torusCentralizer jT`.
  Conjugation by `h` places both the restriction of `v` and every test point
  of `jT` in `S`. Commutativity of `S` makes them commute, and conjugating
  back gives the claim.

## The proof of the core

Fix `k`, `H`, `y`, `w`, `S` and `j` as in the proposition. `H` is connected
reductive, hence smooth with connected underlying space.

1. By `hP1`, `y = b ≫ i` for a Borel subgroup `i : B ⟶ H`. The published
   `borelMaximalTorus` gives a maximal torus `jT : T ⟶ H` factoring through
   `B`. `T` is split, by the published
   `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites` with
   `CoalgebraDescent.separablyClosedGroupLikeSpanning`.
2. Clause 3 of the published `regularCocharacterBorel` gives a regular
   cocharacter `ν` of `T` such that `i` represents the dynamic parabolic
   `P(χ)` with `χ = ν ≫ jT`. Hence `y ∈ P(χ)(k)`. The published
   `centralizer_comp_eq_range_of_isRegular` gives `Z(χ) = range jT`.
3. The chosen limit `t = Dynamic.limit χ y` lies in `Z(χ)`, so `t = t₀ ≫ jT`
   for a point `t₀` of `T`. The published `ClassFunctions.rho_limit` gives
   `y ≫ rho H = t ≫ rho H`, hence `t ≫ rho H = w ≫ rho H`.
4. Applying the centralizer hypothesis to `w` itself gives `w = s₀ ≫ j`. By
   `exists_conj_eq_comp_of_isTorus`, `g₁ * w * g₁⁻¹ = w₀ ≫ jT` for some `g₁`
   and some point `w₀` of `T`. By the published `rho_conjugation`, `t₀ ≫ jT`
   and `w₀ ≫ jT` have the same image under `rho H`. So `hP2` gives
   `g₂ * t * g₂⁻¹ = w₀ ≫ jT`. With `h = g₁⁻¹ * g₂`, this gives
   `h * t * h⁻¹ = w`.
5. Let `v ∈ U(χ)(k)` commute with `t`. By `mem_torusCentralizer_of_commute`,
   `v` lies in `torusCentralizer jT`. The published `maximalTorusCentralizer`
   identifies this subgroup with `range jT = Z(χ)`. So
   `eq_one_of_mem_unipotent_of_mem_centralizer` gives `v = 1`. The structure
   morphism of `H` is affine, hence separated.
6. The published `Dynamic.mul_inv_limit_mem_unipotent` gives
   `y * t⁻¹ ∈ U(χ)(k)`. By step 5, `hR4` applies and gives `v ∈ U(χ)(k)` with
   `v * t * v⁻¹ = y * t⁻¹ * t = y`. Then `g = h * v⁻¹` satisfies
   `g * y * g⁻¹ = h * t * h⁻¹ = w`.

No group-point Jordan decomposition and no torus-unipotence result is used.
Step 5 uses the semidirect structure of `P(χ)` and the self-centralizing
maximal torus in place of the unipotence of `y t⁻¹`.

## Provenance and boundary

Provenance: internal. The module composes published Library results with
the three explicit hypotheses. It makes no further external mathematical
assertion. The underlying classical argument places `y` in `P(χ) = U(χ) ⋊ T`
and conjugates `y` to its `T`-component `t` within `U(χ)`. It then separates
`t` from `w` by class functions on `T`. Its sources are recorded with the
statements of the inputs, Milne 17.34 and Steinberg 6.4/6.6. The
Ax–Grothendieck step replaces the usual closed-orbit argument for the
action of `U(χ)`.

The published target pair, the transport pair, and every pair they import are
unchanged. This module does not prove `hP1`, `hP2` or `hR4`.
