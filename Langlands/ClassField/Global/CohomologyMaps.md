# Restriction, inflation and local maps of relative idele-class cohomology

This module supplies the maps of idele-class cohomology that the published
statement `Langlands.ClassField.Global.GlobalFundamentalClassStatement` writes
with explicit cochains. It proves the two equivariance facts that the
statement's Markdown lists as unproved boundaries. It then builds the maps on
Mathlib group cohomology and translates the three cochain relations
`FundamentalClass.Restriction`, `FundamentalClass.Inflation` and
`FundamentalClass.LocalCompatibility` into equations between cohomology
classes. All declarations are in `Langlands.ClassField.Global`; the last three
theorems are in its namespace `FundamentalClass`. All number fields are in one
universe `Type u`, as in the statement.

## Transport of local units

`ideleClassEquiv_ofAdicCompletion_of_eq` takes a ring isomorphism
`e : K ≃+* L`, a finite place `p` of `L` and a finite place `q` of `K` with
`finitePlaceEquiv e p = q`. It also takes a continuous ring homomorphism
`φ : K_q → L_p` that extends `e` on the image of `K`. The published idele-class
isomorphism `ideleClassEquiv e` then sends the image of a unit `x` of `K_q`
under Mathlib's `IdeleClassGroup.ofAdicCompletion` at `q` to the image of
`φ(x)` at `p`. The proof substitutes the equation of places and identifies `φ`
with the published `finiteCompletionEquiv e p`, since both are continuous and
agree on the dense image of `K`. It then applies the published
`ideleClassEquiv_ofAdicCompletion`.

`adicCompletion_coordinate_eq` is the coordinate form of the same density
argument. Two continuous maps to a Hausdorff space, out of the completions at
two equal finite places, take equal values on the two coordinates of any
family if they agree on the image of `K`.

## Equivariance along the decomposition map

Let `w` be a finite place of `E` over the finite place `v` of `F`, with the
published scoped algebra `F_v → E_w`, and let `σ` be an `F_v`-automorphism of
`E_w`.

- `continuous_localAut`: `σ` is continuous. It is `F_v`-linear and `E_w` is
  finite-dimensional over `F_v` (published `FiniteExtension.local_finite`).
  The proof uses the normed field structure that Mathlib gives a valued
  field with value group `WithZero (Multiplicative ℤ)`.
- `valued_lt_one_iff_tendsto`: an element of `E_w` has valuation `< 1`
  exactly when its powers tend to `0`.
- `valued_localAut_lt_one_iff`: hence `σ` preserves the open unit ball.
- `algebraMap_decompositionHom` (for `E / F` normal): the published
  `decompositionHom v w σ` is the restriction of `σ` to `E`.
- `finitePlaceEquiv_decompositionHom`: the automorphism
  `decompositionHom v w σ` of `E` fixes the place `w`. Membership in `w` is
  valuation `< 1` in `E_w`, which `σ` preserves.
- `relativeIdeleClassAut_decompositionHom_ofAdicCompletion`: the
  `w`-coordinate embedding `E_wˣ → C_E` is equivariant,
  `ρ(decompositionHom v w σ)(i_w(x)) = i_w(σ x)`. Here `ρ` is the published
  action `relativeIdeleClassAut F E` and `i_w` is
  `IdeleClassGroup.ofAdicCompletion (𝓞 E) E w`. This follows from the
  transport lemma with `φ = σ`.

## Equivariance of the idele-class inclusion

Let `e : E ≃+* E` and `f : L ≃+* L` be compatible with `algebraMap E L`, that
is `f (a) = e (a)` for `a ∈ E` viewed in `L`.

- `finitePlaceEquiv_under`: transport of finite places along `e` and `f`
  commutes with taking the place of `E` below a place of `L`.
- `finiteAdeleInclusion_finiteAdeleEquiv`: the finite-adele inclusion of the
  companion module `Langlands.Global.AdelicFunctoriality.Inclusion` commutes
  with the published transports `finiteAdeleEquiv`. The proof is
  coordinatewise, by `adicCompletion_coordinate_eq` at the two equal places
  given by `finitePlaceEquiv_under`.
- `infiniteAdeleMap_infiniteAdeleEquiv`: the infinite-adele map commutes with
  `infiniteAdeleEquiv`. The proof uses only the published functoriality
  `infiniteAdeleMap_comp` and the compatibility of `e` and `f`; no
  archimedean coordinates are used.
- `adeleInclusion_adeleEquiv` and `ideleClassInclusion_ideleClassEquiv`: the
  same for adeles and for idele classes.
- `ideleClassInclusion_relativeIdeleClassAut`: for `F ⊆ E ⊆ L` with `E / F`
  normal and `σ ∈ Gal(L/F)`, the idele-class inclusion `C_E → C_L` satisfies
  `incl(ρ_E(σ|_E)(a)) = ρ_L(σ)(incl(a))`. Here `σ|_E` is
  `AlgEquiv.restrictNormalHom E σ`.

## Cochain relations and second cohomology

`H2π_eq_H2π_iff`: for a representation `A` of a group `G` over a commutative
ring `k`, two degree-two cocycles `x` and `y` have the same class in Mathlib's
`H²(G, A)` exactly when some one-cochain `b : G → A` satisfies
`x(g,h) + b(gh) = b(g) + g • b(h) + y(g,h)` for all `g` and `h`. This is the
additive form of the convention of the statement and of the published
`RelativeIdeleCocycle.cohomologyClass_eq_of_cochain`. The proof rewrites
Mathlib's `H2π_eq_iff` and the range description of the two-coboundaries.

`map_H2π_eq_H2π_iff`: for `f : G →* H` and a morphism `φ` from the
restriction of an `H`-representation `A` along `f` to a `G`-representation
`B`, the map `groupCohomology.map f φ 2` sends `[x]` to `[y]` exactly when
some `b : G → B` satisfies `φ(x(f g, f h)) + b(gh) = b(g) + g • b(h) + y(g,h)`.

## The three maps

Each coefficient morphism is built with `Rep.ofHom` from a map of the
underlying additive groups that is linear over the lifted integers
`ULift ℤ`; integer scaling is `r • a = a ^ r.down` in multiplicative
notation. The maps of cohomology are Mathlib's `groupCohomology.map`, in
every degree `n`.

- Restriction. For `F ⊆ F' ⊆ E`, `ideleClassRestrictionCoefficients` is the
  identity of `C_E`, a morphism from the restriction of
  `relativeIdeleClassRepresentation F E` along
  `AlgEquiv.restrictScalarsHom F : Gal(E/F') → Gal(E/F)` to
  `relativeIdeleClassRepresentation F' E`. It is intertwining by
  reflexivity. `relativeIdeleClassRestriction F F' E n` is the induced map
  `Hⁿ(Gal(E/F), C_E) → Hⁿ(Gal(E/F'), C_E)`.
- Inflation. For `F ⊆ E ⊆ L` with `E / F` normal,
  `ideleClassInclusionLinear` is `ideleClassInclusion` on the additive
  carriers and `ideleClassInclusionLinear_apply` states its value.
  `ideleClassInflationCoefficients` is the resulting morphism from the
  restriction of `C_E` along `AlgEquiv.restrictNormalHom E` to `C_L`; it is
  intertwining by `ideleClassInclusion_relativeIdeleClassAut`.
  `relativeIdeleClassInflation F E L n` is the induced map
  `Hⁿ(Gal(E/F), C_E) → Hⁿ(Gal(L/F), C_L)`: inflation followed by the map of
  coefficients `C_E → C_L`.
- Local map and restriction to the decomposition map. For `w` over `v` and
  `E / F` normal, `localIdeleClassLinear` is `i_w` on the additive carriers
  (value in `localIdeleClassLinear_apply`), and
  `localIdeleClassCoefficients` is the morphism from the published local
  representation `unitsRepresentation F_v E_w` to the restriction of `C_E`
  along `decompositionHom v w`. It is intertwining by
  `relativeIdeleClassAut_decompositionHom_ofAdicCompletion`.
  `localIdeleClassMap v w n` is the induced map from the published
  `relativeCohomology F_v E_w n` to `Hⁿ(Gal(E_w/F_v), C_E)`, where `C_E` is
  restricted along `decompositionHom v w`.
  `decompositionRestriction v w n` is restriction
  `Hⁿ(Gal(E/F), C_E) → Hⁿ(Gal(E_w/F_v), C_E)` along `decompositionHom v w`,
  with the identity coefficient morphism. Here `F_v` is the published
  `padicField v`.

## The statement's relations as class equations

For individual cocycles, in degree two:

- `relativeIdeleClassRestriction_cohomologyClass_eq_iff`: for
  `x : RelativeIdeleCocycle F E` and `y : RelativeIdeleCocycle F' E`,
  `relativeIdeleClassRestriction F F' E 2 [x] = [y]` exactly when some
  `b : Gal(E/F') → C_E` satisfies
  `x(σ|_F, τ|_F) · b(στ) = b(σ) · ρ(σ)(b(τ)) · y(σ,τ)`. Here `σ|_F` is
  `σ.restrictScalars F`.
- `relativeIdeleClassInflation_cohomologyClass_eq_iff`: for every natural
  number `m`, `relativeIdeleClassInflation F E L 2 [x] = m • [y]` exactly
  when some `b : Gal(L/F) → C_L` satisfies
  `incl(x(σ|_E, τ|_E)) · b(στ) = b(σ) · ρ(σ)(b(τ)) · y(σ,τ)^m`.
- `localIdeleClassMap_eq_decompositionRestriction_iff`: for a local cocycle
  `z` and `y : RelativeIdeleCocycle F E`, the equation
  `localIdeleClassMap v w 2 [z] = decompositionRestriction v w 2 [y]` holds
  exactly when some `b : Gal(E_w/F_v) → C_E` satisfies
  `i_w(z(σ,τ)) · b(στ) = b(σ) · ρ(d σ)(b(τ)) · y(d σ, d τ)`, where
  `d = decompositionHom v w`.

These right-hand sides are literally the cochain relations used in the
published predicates. Consequently, for every class family
`c : ClassFamily`:

- `FundamentalClass.restriction_iff_classes`: `Restriction c` holds exactly
  when `relativeIdeleClassRestriction F F' E 2 (c F E) = c F' E` for all
  `F ⊆ F' ⊆ E` with `E / F` Galois.
- `FundamentalClass.inflation_iff_classes`: `Inflation c` holds exactly when
  `relativeIdeleClassInflation F E L 2 (c F E) = [L : E] • c F L` for all
  `F ⊆ E ⊆ L` with `E / F` and `L / F` Galois, where `[L : E]` is
  `Module.finrank E L`.
- `FundamentalClass.localCompatibility_iff_classes`: for every local family
  `I`, `LocalCompatibility I c` holds exactly when, for every finite Galois
  `E / F`, every finite place `w` of `E` over `v` with `E_w / F_v` Galois, and
  every class `a` in `H²(Gal(E_w/F_v), E_wˣ)` that is a fundamental class for
  `(I (residuePrime v)).relative`,
  `localIdeleClassMap v w 2 a = decompositionRestriction v w 2 (c F E)`.

Because the published predicates quantify over all representatives, the
forward directions choose representatives with the published
`RelativeIdeleCocycle.cohomologyClass_surjective`. The local direction uses
Mathlib's `H2_induction_on`, since the local class is quantified directly.

## Provenance and boundary

Derived. The equivariance proofs and the cochain translations are internal.
They use the published adelic transports and inclusions, Mathlib's group
cohomology functoriality, and the conventions of the published statement.
The maps themselves are the standard ones of Artin and Tate, *Class Field
Theory* (2009), registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`
(PDF page = printed page + 9):

- Preliminaries §1, printed pp.1–2: the imbeddings `J_k ⊂ J_K` and
  `C_k ⊂ C_K`, and the semilocal isomorphisms, which come from restriction
  from `G` to the decomposition group `G_P` and the `P`-factor.
- Chapter XIV §1, printed p.145: restriction `H^r(K/F) → H^r(K/E)` and
  inflation `H^r(G_F/G_K, A^{G_K}) → H^r(G_F/G_L, A^{G_L})` for the layers
  of a formation. The inflation changes coefficients through the inclusion
  `A^{G_K} ⊂ A^{G_L}`, here `C_E ⊂ C_L`.

The local map is the map of J. Tate, *Number theoretic background*, Proc.
Sympos. Pure Math. 33, Part II (1979), registered as
`tate-1979-number-theoretic-background` (PDF page = printed page + 9),
§1.6, Proposition (1.6.1), printed p.8: a unit of `E_v` goes to the class of
the idele with that `v`-component and all other components `1`. Tate uses it,
on printed pp.8–9, with the relationship between global and local canonical
classes.

Nothing here proves the vanishing of `H¹(Gal(E/F), C_E)`, any global
invariant, or the existence or uniqueness of fundamental classes. The
module only makes the published cochain conditions available as equations
of classes. It does not prove that `E_w / F_v` is Galois when `E / F` is,
and it does not identify `Gal(E_w/F_v)` with a decomposition subgroup of
`Gal(E/F)`.
