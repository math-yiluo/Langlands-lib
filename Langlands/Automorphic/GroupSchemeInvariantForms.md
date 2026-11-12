# Automorphic functions on `Γ \ G(𝔸)` for an arbitrary subgroup `Γ`

Module `Langlands.Automorphic.GroupSchemeInvariantForms` defines the
conditions of an automorphic form for complex functions on the actual adelic
points `G(𝔸)` of an affine group scheme `G` over a number field `F` that are
left invariant under an arbitrary subgroup `Γ ≤ G(𝔸)`. It is a definition
module and proves nothing.

Its purpose is the space `𝒜_P` of automorphic forms on
`X_P = U(𝔸)M(F) \ G(𝔸)` used by Bernstein–Lapid: take `Γ = U(𝔸)M(F)` for a
standard parabolic `P = MU`. With `Γ = G(F)` it gives the automorphic forms on
`G(F) \ G(𝔸)`, and the companion statement
`RationalAutomorphicFunctionComparisonStatement` asserts that they are exactly
the existing `IsAdelicAutomorphicForm` elements.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, Cambridge University Press, 1995, registered as
  `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (one-based PDF
  page = printed page − 17). I.2.17 (printed p.37): for a standard parabolic
  `P = MU`, a function `φ : U(𝔸)M(k) \ G → ℂ` is automorphic if (i) it has
  moderate growth, (ii) it is smooth (I.2.5), (iii) it is `K`-finite and
  (iv) it is `𝔷`-finite, `𝔷` the center of the enveloping algebra of the Lie
  algebra of `G_∞`. I.2.5 (printed p.26) defines smoothness and I.2.3
  (printed p.24) moderate growth for the height of I.2.2 (printed p.20).
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2 (journal
  p.191): `𝒜_P` is the space of automorphic forms on `X_P` in the sense of
  MW I.2.17.

## Existing objects reused

All analytic data are those of the existing forms on `G(F) \ G(𝔸)`
(`Langlands.Automorphic.GroupSchemeForms` and the modules it imports), so that
the two notions can be compared directly:

- `AdelicGroupPoints.pair F G a b` assembles an adelic point from its infinite
  component `a` and finite component `b`; `ofFinite` and `ofInfinite` are the
  inclusions of the two factors.
- `InfinitePlotSmoothFunctions F G` is the existing space of plot-smooth
  functions on the infinite adelic points `G(𝔸_∞)`, the Library's realization
  of smooth functions there.
- `AdelicEnvelopingCenter F G hsmooth` is the center of the complex enveloping
  algebra of the actual identity tangent Lie algebra of `G(𝔸_∞)`, for the
  atlas fixed by `hsmooth : SmoothOfRelativeDimension d G.X.hom`, and
  `plotSmoothCenterAction F G hsmooth hcalc` is its existing action on
  `InfinitePlotSmoothFunctions F G`, under the existing commutator premise
  `hcalc : AdelicDifferentialCommutator F G hsmooth`.
- `RepresentationGrowth.adelicSourceNorm F G rho` is the existing exact
  adelic norm of a matrix representation `rho : G → GL_N`.

## Definitions

Let `φ : G(𝔸) → ℂ`.

- `functionInfiniteSlice F G φ b` is the function `a ↦ φ(pair a b)` on
  `G(𝔸_∞)`, for a finite adelic point `b`.
- `IsLeftInvariantUnder F G Γ φ`: `φ(x g) = φ(g)` for all `x ∈ Γ` and
  `g ∈ G(𝔸)`.
- `IsAdelicSmoothFunction F G φ`: `φ` is continuous, every infinite slice
  belongs to `InfinitePlotSmoothFunctions F G`, and there is an open subgroup
  `L` of `G(𝔸_f)` with `φ(g l) = φ(g)` for all `l ∈ L` and all `g`.
- `IsInfiniteSubgroupFiniteFunction F G Kinf φ`: for a specified subgroup
  `Kinf` of `G(𝔸_∞)`, the complex span of the right translates
  `g ↦ φ(g k)`, `k ∈ Kinf`, is finite-dimensional.
- `IsCenterFiniteFunction F G hsmooth hcalc φ`: there is an ideal `J` of the
  center with finite-dimensional quotient such that every `z ∈ J` annihilates
  every infinite slice of `φ` (every slice that is plot-smooth) under
  `plotSmoothCenterAction`.
- `HasModerateGrowthFunction F G rho φ`: there are `C > 0` and a real `r`
  with `‖φ(g)‖ ≤ C · ‖g‖^r` for all `g`, where `‖g‖` is
  `adelicSourceNorm F G rho g`.
- `IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ` is the conjunction
  of the five conditions above.

## Correspondence with MW I.2.17

- (i) Moderate growth is `HasModerateGrowthFunction` with the specified
  representation's adelic norm, as in the existing `HasAdelicModerateGrowth`.
  Independence of the representation is not asserted here.
- (ii) and (iii). MW's smoothness (I.2.5) asks that `φ` be locally of the
  form `f(g_∞ g_f) = f_r(g_∞)` with `f_r` of class `C^∞`, and (iii) asks for
  finiteness under the maximal compact subgroup `K = K_∞ K_f` of `G(𝔸)`. As
  in the existing forms, these are expressed by plot-smooth infinite slices,
  one open subgroup of `G(𝔸_f)` fixing `φ`, and finiteness under a specified
  subgroup `Kinf` of `G(𝔸_∞)`. For continuous `φ` and compact `K_f`, a common
  open stabilizer gives `K_f`-finiteness, and `K_f`-finiteness of a locally
  constant function gives a common open stabilizer, so the two formulations
  agree when `Kinf = K_∞`. This equivalence is explanatory and not proved
  here; that `Kinf` is maximal compact is not part of the predicate.
- (iv) `𝔷`-finiteness is the existence of a finite-codimensional ideal of
  `𝔷` annihilating `φ`. Since `𝔷` acts in the infinite variable, it is
  imposed on every infinite slice with one common ideal. This is the
  equivalent "common ideal" form of the existing `IsAdelicCenterFinite`
  (`isAdelicCenterFinite_iff_exists_ideal`).
- Left invariance under `Γ` replaces functions on the quotient
  `Γ \ G(𝔸)`; `Γ = U(𝔸)M(F)` gives MW's functions on `U(𝔸)M(k) \ G`.

## Scope

No closure property (linear subspace, right `G(𝔸_f)`-stability), no
comparison with MW's own reduction to automorphic forms on `M(F) \ M(𝔸)`, and
no construction of the subgroup `U(𝔸)M(F)` is part of this module. The
central-character condition (v) of MW I.2.17 is not imposed.
