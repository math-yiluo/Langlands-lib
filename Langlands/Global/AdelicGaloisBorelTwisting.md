# Galois twisting of a split Borel pair on upper-field adelic points

Author: Worker 5268.

This module states, without proof, the Galois input of Springer's proof of
compactness (Springer 1994, §3.4–3.5). Let `G` be a connected reductive group
over a number field `F`, split by a finite Galois extension `L`. The Galois
group of `L/F` acts on `G(𝔸_L)`. Each `σ` carries the standard Borel pair of
`G_L` to a pair that is conjugate to it by a rational point `m_σ ∈ G(L)`. The
induced permutation of the simple roots is the based (`*`-)action, which
Springer writes `ι(s)`.
`GaloisBorelTwistingStatement` asserts that such data exist. It records only
the properties that the §3.5 argument uses.

## Notation

Throughout, `F` is a number field and `L` is a finite Galois extension of `F`
(a number field). `G` is an affine, locally finite-type group scheme over
`F`. `G_L = AffineWeil.unitBaseChange F L G` is its base change to `L`.

Inside `G_L` we fix:

- a commutative group scheme `T` over `L` with a homomorphism
  `i : T → G_L`;
- a cocharacter `ν : cocharacterLattice T`.

Write `Δ = simpleRelativeRoots i ν` and `B = Standard.parabolicScheme i ν ∅`,
with inclusion `j_B = Standard.parabolicHom i ν ∅`. For `H ⊆ Δ`,
`P_H = Standard.parabolicScheme i ν H`. For `β` a character of `T` and
`t ∈ T(𝔸_L)`, `|β(t)|` means `PositiveRealTorus.normCharacter L T β t`.
`G_L(𝔸_L)¹` is `normOneSubgroup L G_L`, and `B(𝔸_L)¹` is the norm-one subgroup
of `B`, defined by all characters of `B`.

## Definitions

**`rationalSection F L G m`.** For a rational point `m` of `G_L`, given as a
section over `Spec L`, this is its image in `G_L(𝔸_L)`. It is
`rational L G_L (rationalCoeffEquiv L G_L m)`.

**`IsGaloisBorelTwist F L G T i ν σ φ m a`.** Here `σ ∈ Gal(L/F)`,
`φ : G_L(𝔸_L) → G_L(𝔸_L)` is a continuous group homomorphism, `m` is a
rational point of `G_L`, and `a` is a map from characters of `T` to
characters of `T`. Write `M = rationalSection m`. The predicate is the
conjunction of five conditions.

1. **Rational points.** For every rational point `q` of `G_L`,
   `φ(rationalSection q) = rationalSection (rationalConjugate F L G σ q)`.
   So `φ` acts on `G(L)` by the actual Galois conjugation `σ`.
2. **Ground-field points.** `φ` fixes the image of every `g ∈ G(𝔸_F)¹` under
   `scalarExtensionNormOneMap F L G`, the scalar-extension map
   `G(𝔸_F)¹ → G_L(𝔸_L)¹`.
3. **Torus.** For every `t ∈ T(𝔸_L)` there is `t' ∈ T(𝔸_L)` with
   `φ(i(t)) = M · i(t') · M⁻¹`. Moreover:
   - if `i(t) ∈ G_L(𝔸_L)¹` then `i(t') ∈ G_L(𝔸_L)¹`;
   - for every `β ∈ Δ` there is `β' ∈ Δ` with `|β(t')| = |β'(t)|`.
4. **Borel subgroup.** For every `p ∈ B(𝔸_L)¹` there is `p' ∈ B(𝔸_L)¹` with
   `φ(j_B(p)) = M · j_B(p') · M⁻¹`.
5. **Maximal parabolics.** For every `β ∈ Δ`, `a β ∈ Δ`, and the Galois
   translate of `P_(Δ \ {β})` is the conjugate of `P_(Δ \ {a β})` by `m`.
   In Lean, the subgroup functor
   `SubgroupFunctor.range (radicalGaloisHom (Standard.parabolicHom i ν (Δ \ {β})) σ)`
   equals
   `SubgroupFunctor.range (Standard.parabolicHom i ν (Δ \ {a β}) ≫ (G_L.innerIso m).hom)`.
   `radicalGaloisHom f σ` is the canonical Galois translate of the subgroup
   `f`. On rational points it matches `rationalConjugate F L G σ`
   (`rationalConjugate_mem_galoisTransport_iff`). `innerIso m` is
   conjugation `x ↦ m x m⁻¹`.

**`HasGaloisBorelTwisting F L G T i ν`.** There are families
`φ_σ`, `m_σ`, `a_σ`, indexed by `σ ∈ Gal(L/F)`, such that:

- `IsGaloisBorelTwist F L G T i ν σ φ_σ m_σ a_σ` holds for every `σ`;
- `a_1 β = β` for every `β ∈ Δ`;
- `a_(στ) β = a_σ (a_τ β)` for all `σ, τ` and every `β ∈ Δ`.

So the `a_σ` restrict to an action of `Gal(L/F)` on `Δ`.

## The statement

`GaloisBorelTwistingStatement` quantifies in universe `u` over every number
field `F` and every affine, locally finite-type group scheme `G` over `F`
that is connected reductive. It asserts that there are:

- a finite Galois split maximal model `D : FiniteGaloisSplitMaximalModel G`.
  This consists of a finite Galois extension `L = D.carrier` of `F` and a
  split maximal torus `D.inclusion : D.torus → G_L`;
- a cocharacter `ν` of `D.torus` that is generic
  (`IsGenericCocharacter D.inclusion ν`);

such that `HasGaloisBorelTwisting F L G D.torus D.inclusion ν` holds.

## Intended witness

The intended witnesses come from the actual Galois action, as in Springer
§3.4. The statement does not depend on this description.

- `φ_σ` is the action of `σ` on `G_L(𝔸_L) = G(𝔸_F ⊗_F L)` through the second
  tensor factor. It is continuous. It acts on `G(L)` by `rationalConjugate σ`
  and fixes `G(𝔸_F)`.
- `σ` carries the Borel pair `(B, T)` of `G_L` to the Borel pair `(σB, σT)`,
  where `σT` is a split maximal torus. Split Borel pairs of `G_L` are
  conjugate under `G(L)`, so `(σB, σT) = Int(m_σ)(B, T)` for some
  `m_σ ∈ G(L)`. This `m_σ` is Springer's `ṅ_s`, with `s.B = Int(ṅ_s) B`.
- For `t ∈ T(𝔸_L)`, `t' = m_σ⁻¹ σ(i(t)) m_σ` lies in `T(𝔸_L)`. A simple root
  `β` composed with `Int(m_σ⁻¹)` is the `σ`-transport of a simple root `β'`.
  The full idele norm of `L` is Galois invariant, so `|β(t')| = |β'(t)|`. The
  `B(𝔸_L)¹` case is the same argument, applied to characters of `B`.
- `a_σ` is the based (`*`-)action of the Galois group on `Δ`, which Springer
  writes `ι(s)`. It is not Springer's ordinary action `s.α` of `s` on roots,
  which need not preserve `Δ`. The two are related by
  `s.α = w_s(ι(s).α)`, that is, `ι(s).α = w_s⁻¹(s.α)`, where `w_s` is the Weyl
  element represented by `ṅ_s`. Springer's identity
  `s.P_H = Int(ṅ_s) P_(ι(s).H)` with `H = Δ \ {β}` is condition 5, with
  `a_σ` in place of `ι(s)`. The based action is a group action, which gives
  the last two conditions.

## Provenance

This is an internal interface derived from T. A. Springer, *Reduction theory
over global fields* (1994), §3.4 and the first part of §3.5, printed p.215.
There Springer fixes:

- a maximal `k`-torus `T ⊇ S`;
- a Galois splitting field `l` with group `Γ`;
- representatives `ṅ_s` of Weyl elements `w_s` with `s.B = Int(ṅ_s) B`;
- an action `ι` of `Γ` on `Δ`, the based action, determined by
  `s.α = w_s(ι(s).α)` for `α ∈ Δ`. Here `s.α` is the ordinary Galois action
  on the roots of `(G, T)`, which need not preserve `Δ`.

He states `s.P_H = Int(ṅ_s) P_(ι(s).H)` for `H ⊆ Δ`. In §3.5 he uses three
facts:

- `Γ` acts on `G(𝔸, l)¹` and fixes `G(𝔸, k)¹`;
- the rewriting `s(xtuγ) = ((s.x)ṅ_s)(ṅ_s⁻¹(s.t)ṅ_s)u'(ṅ_s⁻¹(s.γ))`;
- the fact that `ṅ_s⁻¹(s.t)ṅ_s` again satisfies the root bounds of `T(c)`.

The formulation here differs from Springer's in three ways.

1. **Existential model.** Springer's `T` is defined over `k`. Here only some
   finite Galois splitting field, some split maximal torus of `G_L` and some
   generic cocharacter are asserted. When `σT ≠ T`, `m_σ` must also carry `T`
   to `σT`. This is possible because split Borel pairs over `L` are
   `G(L)`-conjugate.
2. **Galois action through its properties.** The action on `G_L(𝔸_L)` is not
   defined here. Conditions 1–4 record the properties of the action that
   §3.5 uses. Condition 1 pins `φ_σ` to the actual conjugation of rational
   points. Condition 2 pins it to the identity on ground-field points.
   Condition 3 makes explicit Springer's tacit fact that conjugation by
   `ṅ_s⁻¹` permutes the simple-root absolute values. Condition 4 is the
   rewriting of the unipotent factor `u' = Int(ṅ_s⁻¹)(s.u)`, stated for the
   norm-one Borel factor used by `HasRightAdelicFundamentalSet`.
3. **Maximal parabolics only.** Condition 5 is
   `s.P_H = Int(ṅ_s) P_(ι(s).H)`, with `a_σ` in place of `ι(s)`, for the
   maximal standard parabolics `H = Δ \ {β}`. These are the only ones §3.5
   uses.

The last two conditions of `HasGaloisBorelTwisting` say that `a` is an action
on `Δ`, as Springer's `ι` is.

## Use

This interface is the Galois input for proving
`CentralSplitCompactQuotientStatement` along Springer's §3.5. The other
inputs are:

- the split fundamental-set statement `SplitAdelicFundamentalSetStatement`;
- the split overlap estimate `SplitSiegelOverlapStatement` (Springer
  Prop. 2.6).

A factorization `h = x · i(t) · j_B(p) · γ` and its `φ_σ`-image give a second
factorization of the same point. Condition 3 keeps the upper root bounds,
and condition 4 keeps the norm-one Borel factor. The overlap estimate then
places `m_σ⁻¹ σ(γ) γ⁻¹` in a maximal parabolic. Condition 5 converts this
into the inverse-orbit matching premise of
`IsMaximalSplitTorus.eq_simpleRelativeRoots_of_inverse_orbit_matching`.

## Scope

This module contains only definitions and the proposition. It proves
nothing. Its only hypotheses on `G` are that it is affine, locally of finite
type and connected reductive.
