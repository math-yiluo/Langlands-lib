# Weakly induced tori over `K = F^ur` (Kaletha–Prasad Definition B.6.2)

This module belongs to the Library's Kaletha–Prasad Bruhat–Tits development.
It supplies the torus hypothesis of
condition (1) in KP §13.5, the hypothesis under which KP prove the
Moy–Prasad isomorphism (Theorem 13.5.1) for every `s ≤ 2r`. The module
contains three `Prop`-valued definitions and no theorems. The remarks below
explain where the definitions come from. They are not proved results.

Throughout, `F` is a nonarchimedean local field
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`).
`K = UnramifiedClosure F` is the maximal unramified extension of `F` inside
`F^sep = SeparableClosure F`, as in the module
`Langlands.Geometry.Building.KPZeroSubgroups`.

## The definitions

### `IsTamelyRamifiedOverUnramifiedClosure F L`

For an intermediate field `L : IntermediateField (UnramifiedClosure F)
(SeparableClosure F)`, the proposition says that there is a natural number
`e` such that

- `0 < e`,
- `e` is not divisible by `ringChar 𝓀[F]`, the characteristic `p` of the
  residue field of `F`, and
- for every nonzero `x : L` there is `a : F` with
  `intermediateValuation F L x ^ e = sepClosureValuation F (algebraMap F
  (SeparableClosure F) a)`.

`intermediateValuation F L` (from `KPZeroSubgroups`) is the restriction to `L`
of `LocalGalois.Separable.sepClosureValuation F`. That is the unique extension
of the valuation of `F` to `F^sep`. So the last condition says
`|x|^e ∈ |F^×|` for all `x ∈ L^×`: the `e`-th power of the value group of `L`
lies in the value group of `F`.

### `IsWeaklyInducedTorus F T`

For a commutative group scheme
`T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))`, the
proposition says that there is an intermediate field `L` of `F^sep/K` such
that

- `FiniteDimensional (UnramifiedClosure F) L`,
- `IsTamelyRamifiedOverUnramifiedClosure F L`, and
- `IsInducedTorus ((CommGroupScheme.baseChange (algebraBaseMap
  (UnramifiedClosure F) L)).obj T)`.

So the base change `T_L` is an induced torus in the sense of
`Langlands.GroupScheme.IsInducedTorus` (KP Definition 2.5.1).

### `HasWeaklyInducedMaximallySplitTorus F G`

For a group scheme `G : GroupScheme (Spec (CommRingCat.of F))`, the
proposition says that there are

- a commutative group scheme `T` over `Spec K`, and
- a morphism `i : T.toGrp ⟶ GaloisPointComparison.baseChanged F
  (UnramifiedClosure F) G` into the base change `G_K`,

such that `IsMaximallySplitMaximalTorus i` holds (KP Definition 2.6.2, as
formalized in `KPZeroSubgroups`) and `IsWeaklyInducedTorus F T` holds.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page numbers are the
PDF page numbers minus 31. The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`) change nothing in Definition B.6.2,
Remark B.6.3 or the conditions of §13.5.

- Definition B.6.2, printed p. 669, PDF p. 700: "We say that a `k`-torus `T`
  is weakly induced if there exists a tamely ramified extension `ℓ/k` such
  that `T_ℓ` is an induced torus." KP add that every induced `k`-torus is
  weakly induced.
- Remark B.6.3, printed p. 669, PDF p. 700: with `k^t` the maximal tamely
  ramified subextension of `k^s/k`, `T` is weakly induced if and only if
  `T_{k^t}` is induced.
- §13.5, condition (1), printed p. 474, PDF p. 505: "The maximally split
  maximal torus of `G_K` becomes induced after a tame base change (i.e. it is
  weakly induced in the sense of Definition B.6.2) and `s ⩽ 2r`."
  `HasWeaklyInducedMaximallySplitTorus F G` is the first half of this
  condition. The inequality `s ≤ 2r` is not part of this module; it belongs
  with the statement of Theorem 13.5.1.

## Derived formulation

KP state Definition B.6.2 for a general `k`. Here it is used only for
`k = K = F^ur`, the field over which condition (1) of §13.5 is posed. The
Lean formulation differs from KP's wording in the following ways.

**Tame ramification.** KP do not define "tamely ramified" in Appendix B. We
use the standard meaning for a finite separable extension `L/K` of
discretely valued Henselian fields: the residue field extension is separable
and the ramification index `e(L/K)` is prime to `p`. Over `K = F^ur` the
residue field is an algebraic closure of the residue field of `F`. So the
residue field extension of a finite `L/K` is trivial, and tameness reduces to
`p ∤ e(L/K)`. The Lean condition says that `p ∤ e(L/K)` in terms of value
groups. `K/F` is unramified, so the value group of `K` equals that of `F`.
The value group of a finite `L/K` contains it with cyclic quotient of order
`e(L/K)`. So some `e` prime to `p` satisfies `|L^×|^e ⊆ |F^×|` exactly when
`e(L/K)` divides such an `e`, that is, when `p ∤ e(L/K)`. This avoids a
separate notion of ramification index, which the Library does not define for
intermediate fields of `F^sep/K`. The condition on an infinite `L` is not
used here: `IsWeaklyInducedTorus` imposes it only together with
`FiniteDimensional K L`.

**Finite extensions inside `F^sep`.** KP allow any tamely ramified extension
`ℓ/k`. A tamely ramified extension is algebraic and separable, so it embeds
into `F^sep` over `K`, and being induced is preserved under isomorphism of
the base field. It may also be taken finite; KP themselves work with a finite
tame Galois `L/K` with `T_L` induced in the proofs of Proposition B.6.6 and
Lemma B.6.7 (printed pp. 671–672, PDF pp. 702–703). `T` splits over a finite Galois
extension `M/K`, and the Galois action on `X^*(T)` factors through
`Gal(M/K)`. If `T_ℓ` is induced, then `T_{M ∩ ℓ}` is induced, and `M ∩ ℓ`
is a finite tamely ramified extension of `K` (compare Remark B.6.3). This is
why the definition quantifies over finite intermediate fields `L` of
`F^sep/K`.

**`T` need not be assumed a torus.** The definition is stated for any
commutative `K`-group scheme `T`. It does not separately require `T` to be a
torus: the clause `IsInducedTorus T_L` makes `T_L` a torus (by
`IsInducedTorus.isTorus`). That `T` itself is then a torus, by descent along
field extensions, is standard but is not formalized here. In the one use in
this module, `T` comes with a maximal torus `i : T → G_K`.

**"The" maximally split maximal torus.** KP speak of *the* maximally split
maximal torus of `G_K`. Over `K` the connected reductive group `G_K` is
quasi-split (KP Corollary 2.3.8). Its maximally split maximal tori are the
centralizers of its maximal `K`-split tori, which are conjugate under `G(K)`.
Conjugate tori are isomorphic, so whether such a torus is weakly induced does
not depend on the choice. The definition therefore asks for one maximally
split maximal torus that is weakly induced. This independence argument is
provenance only. The module proves nothing about it, and the existential
form is the definition used downstream.

## Scope

The module defines no models or filtrations of tori. KP use weakly induced
tori to show that the standard filtration is schematic, connected and
congruent (Proposition B.6.4). Proposition B.6.9 gives the Moy–Prasad
isomorphism for tori: for `0 < r < s ≤ 2r` the functors
`T ↦ T(k)^std_r / T(k)^std_s` and `T ↦ t(k)^std_r / t(k)^std_s` on weakly
induced tori are isomorphic. Neither result is stated here.
