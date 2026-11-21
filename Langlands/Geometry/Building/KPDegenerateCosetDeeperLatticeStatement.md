# KP Proposition 13.6.7, first assertion: a degenerate coset lies in a deeper lattice

Author: Worker 3557.

This module belongs to the Kaletha–Prasad Bruhat–Tits program (task
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`). It states the first assertion of
KP Proposition 13.6.7 for the Library's supplied Lie filtrations, in two
versions. The first finds a point of the reduced building at which the
degenerate coset lies in a deeper lattice. The second also makes that point
optimal (KP Definition 13.4.2). The module has two statements and proves
nothing.

## Setting

`F` is a nonarchimedean local field with ring of integers `𝒪[F]`, and `G`
is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]`.
`P : ParahoricBuildingData G` is the Library's supplied building data. It
contains the connected reductive structure of `G`, the maximal split torus
`P.i : S → G`, the apartment `P.Apartment`, its affine roots
`P.affineRoots` (KP Definition 6.3.4), the reduced building
`P.ReducedBuilding` with its `G(F)`-action and the map
`P.apartmentMap : P.Apartment → P.ReducedBuilding`. The hypothesis
`P.SatisfiesApartmentAxioms` is the Library's package of KP's apartment
axioms for these data.

`L : P.LieFiltrationData` supplies the lattices `z_r` in `Lie(Z)` and `u_ψ`
in the root spaces (module `Langlands.Geometry.Building.KPLieFiltration`).
For a point `x` of the apartment and real `r`:

- `L.lieFiltrationReal x r` is `𝔤_{x,r}`, extended from `r ≥ 0` to real
  `r` as in KP 13.3.1 (module `Langlands.Geometry.Building.KPLieFiltrationDual`).
- `L.lieFiltrationPlusReal x r` is `𝔤_{x,r+}`, the supremum of the
  `𝔤_{x,s}` for `s > r`.
- `L.IsPeriodic` is KP's `𝔤_{x,r+1} = 𝔪 𝔤_{x,r}`. For periodic `L`,
  `𝔤_{x,r+}` is KP's union `⋃_{s>r} 𝔤_{x,s}` and lies in `𝔤_{x,r}`
  (`lieFiltrationPlusReal_le`), so `𝔤_{x,r}/𝔤_{x,r+}` is defined.

KP's lattices `𝔤_{y,s}` are needed at points `y` of the whole building.
They are `lieFiltrationOnBuilding hL y s` (module
`Langlands.Geometry.Building.KPLieFiltrationOnBuilding`). The hypothesis
`hL : L.IsAdjointCompatible` has two parts. Normalizer points `n` transport
the apartment lattices, `Ad(n) 𝔤_{x,r} = 𝔤_{n·x,r}`, and the group
`G(F)^♯_x` used in the reduced building quotient stabilizes `𝔤_{x,r}`
(`P.sharpFixer {x} ≤ L.filtrationStabilizer x`). Under these hypotheses the
apartment lattices descend to the reduced building. At `g · x` the lattice
is `Ad(g) 𝔤_{x,s}` (`lieFiltrationOnBuilding_smul_apartmentMap`), and at
apartment points it is the apartment lattice
(`lieFiltrationOnBuilding_apartmentMap`).

Nilpotence and degeneracy are those of KP Definition 13.6.5 (module
`Langlands.Geometry.Building.KPNilpotentCoset`).
`IsDegenerateLieCoset M X` says that `X + M` contains an element `Y` that
some 1-parameter subgroup `ν : 𝔾_m → G` over `F` contracts to `0`, i.e.
`Y ∈ 𝔤_{>0}(ν)`.

Optimal points are those of KP Definition 13.4.2 (module
`Langlands.Geometry.Building.KPOptimalPoints`).
`P.IsOptimalPoint y` says that `y = g · x` for some `g ∈ G(F)` and some
optimal point `x` of the apartment. An optimal point `x` of the apartment is
a rational point of the closure of some chamber `C` that maximizes
`min_{ψ ∈ S} ψ` on that closure. Here `S` is a nonempty finite subset of
KP's set `Σ` of affine roots `ψ` with `0 < ψ < ℓ` on `C`, and `ℓ` is the
root period of §13.4.

## The statements

### `DegenerateLieCosetInDeeperLatticeStatement`

For every `F`, `G` and `P` with `P.SatisfiesApartmentAxioms`, every `L` with
`hL : L.IsAdjointCompatible` and `L.IsPeriodic`, every `x : P.Apartment`
and real `r` such that `L.lieFiltrationPlusReal x r` is finitely generated
over `𝒪[F]`, and every `X ∈ L.lieFiltrationReal x r` with
`IsDegenerateLieCoset (L.lieFiltrationPlusReal x r) X`: there are
`y : P.ReducedBuilding` and a real `s` with `r < s` such that every `Y`
with `Y - X ∈ L.lieFiltrationPlusReal x r` lies in
`lieFiltrationOnBuilding hL y s`.

In KP's notation: if `Ξ = X + 𝔤_{x,r+}` is a degenerate coset in
`𝔤_{x,r}/𝔤_{x,r+}`, then `Ξ ⊆ 𝔤_{y,s}` for some `y ∈ B(G)` and some `s > r`.

### `DegenerateLieCosetInOptimalLatticeStatement`

The same, with the additional hypothesis `P.affineRoots.Nonempty` and the
additional conclusion `P.IsOptimalPoint y`. This is KP's assertion: the
point `y` can be chosen optimal.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page numbers are the
PDF page numbers minus 31.

- Proposition 13.6.7 ([MP94, Proposition 6.3]), printed p. 481, PDF p. 512:
  "Let Ξ = X + 𝔤_{x,r+} be a degenerate coset in 𝔤_{x,r}/𝔤_{x,r+} with X
  nilpotent. Then there is an optimal point y such that for some s > r,
  𝔤_{y,s} ⊃ Ξ. Moreover, Ξ considered as an element of 𝔤_{x,r}/𝔤_{x,r+} is
  'unstable' under the action of G_x, i.e., the closure of the G_x–orbit
  through it contains 0."
- Proof of the first assertion, same page. By Proposition 13.6.4 there are
  `p ∈ P_x` and a 1-parameter subgroup `ν : 𝔾_m → S` with
  `lim_{t→0} ν(t)(pX) = 0`. Writing `pX = Y_0 + Σ Y_ψ` along `z_r` and the
  `u_ψ` for absolute affine roots with `ψ(x) ≥ r`, contraction forces
  `Y_0 = 0` and `ψ̇(ν) > 0` for the roots with `ψ(x) = r` that contribute
  to the coset. For small `ε > 0` and
  `x' = εν + x` one gets `pΞ ⊆ 𝔤_{x',s}` for some `s > r`. With
  `y' = p⁻¹x'`, `𝔤_{y',s} ⊃ Ξ`. Finally Lemma 13.4.4 gives an optimal point
  `y` with `𝔤_{y,s} ⊃ 𝔤_{y',s}`.
- Definition 13.6.5, printed p. 480, PDF p. 511 (nilpotent elements,
  degenerate cosets). Definition 13.4.2 and Lemma 13.4.4 (optimal points).
- The authors' corrections of 1 November 2024
  (`kaletha-prasad-2024-corrections`), PDF p. 49: the Chapter 13 entries
  concern Proposition 13.5.2(1), the end of 13.6.2 and the proof of Theorem
  13.8.5. None concerns Proposition 13.6.7.

## Derived formulation

**The point `x`.** KP's `x` is any point of `B(G)`. Here `x` is a point of
the apartment, where the supplied lattices `L.lieFiltrationReal x r` are
defined. Points `g · x` of the reduced building are not treated here.

**The point `y`.** KP's `y` is a point of `B(G)`, the reduced building. Here
it is a point of `P.ReducedBuilding`, and `𝔤_{y,s}` is
`lieFiltrationOnBuilding hL y s`. In KP's proof `y' = p⁻¹ x'` is generally
not in the apartment, so the statement cannot be restricted to apartment
points without changing the argument.

**The coset and its representative.** KP choose the representative `X`
nilpotent. Here `X` is any element of `𝔤_{x,r}` whose translate
`X + 𝔤_{x,r+}` is degenerate. For periodic `L`, `𝔤_{x,r+} ⊆ 𝔤_{x,r}`
(`lieFiltrationPlusReal_le`). So a nilpotent element `Y` of the translate
lies in `𝔤_{x,r}` and `Y + 𝔤_{x,r+} = X + 𝔤_{x,r+}`. The two formulations
describe the same cosets. KP's `𝔤_{y,s} ⊃ Ξ` is written as "every `Y` with
`Y - X ∈ 𝔤_{x,r+}` lies in `lieFiltrationOnBuilding hL y s`".

**Supplied lattices.** KP's `𝔤_{x,r}` are the Lie lattices of their
integral models (§13.3). Here they come from the supplied `L`. KP's lattices
are periodic, compatible with the adjoint action of `G(F)`, and finitely
generated over `𝒪`. For supplied `L` these are the hypotheses
`L.IsPeriodic`, `L.IsAdjointCompatible` and finite generation of
`𝔤_{x,r+}`. KP's proof needs one depth `s > r` with `pΞ ⊆ 𝔤_{x',s}` for
the whole coset, not a depth depending on its element. For KP's lattices
this holds because `𝔤_{x,r+}` is a finitely generated lattice. For supplied
`L` the finite generation of `𝔤_{x,r+}` is assumed for this purpose. None
of these hypotheses is verified here for an actual construction of the
integral models.

**Why the optimal version assumes affine roots.** If `P.affineRoots = ∅`,
for example when `G` has no relative roots (a torus or an anisotropic
group), then there is no optimal point
(`ValuationBuildingData.not_isOptimalPoint_of_affineRoots_eq_empty`): KP
Definition 13.4.2 needs a nonempty subset of `Σ`. But the coset
`0 + 𝔤_{x,r+}` is always degenerate, because `0` is contracted by every
1-parameter subgroup. So KP's literal assertion fails for every such `P`
that admits an `L` satisfying the other hypotheses, and the optimal version
assumes `P.affineRoots.Nonempty`. The deeper-lattice version needs no such
hypothesis.

**Expected proof route (not part of the statement).** The deeper-lattice
version is meant to follow from three published targets and the gluing of
`KPLieFiltrationOnBuilding`. These are
`ParahoricContractionInApartmentStatement` (the contraction clause of KP
Proposition 13.6.4, with `p ∈ P.parahoricAt x` and `ν` a cocharacter of
`S`), `LieRootSupportOfApartmentCocharacterStatement` (the root support of
`pX` along `ν`), and `LieCosetPromotionOfPositiveRootSupportStatement` (the
choice of `ε` and `s`). The point is
`y = p⁻¹ · apartmentMap (ε v + x)`, where `v` is the image of `ν` in the
translation space. A private compiled check confirmed this assembly in Lean
from those three statements as hypotheses. The optimal version also needs
KP Lemma 13.4.4, which is not in the Library.

## Not included

- The second assertion of Proposition 13.6.7: `Ξ` is unstable under `G_x`,
  i.e. `0` lies in the closure of its `G_x`-orbit. The Library has no
  residue-field group `G_x` acting algebraically on `𝔤_{x,r}/𝔤_{x,r+}`.
- The dual version for `𝔤*` (KP state 13.6.7 only for `𝔤`).
- Points `x` outside the apartment.

## Provenance

Derived. The statements are the first assertion of KP Proposition 13.6.7
for the Library's supplied building data and supplied Lie filtrations. They
differ from KP in four ways: `x` is restricted to the apartment, the
lattices on the building come from `lieFiltrationOnBuilding` under
`IsAdjointCompatible`, periodicity and finite generation of `𝔤_{x,r+}` are
hypotheses, and the optimal version assumes a nonempty set of affine roots.
The names `DegenerateLieCosetInDeeperLatticeStatement` and
`DegenerateLieCosetInOptimalLatticeStatement` are internal. The module uses
Worker 13's `LieFiltrationData`, `lieFiltrationReal`,
`lieFiltrationPlusReal` and `IsOptimalPoint` (modules `KPLieFiltration`,
`KPLieFiltrationDual` and `KPOptimalPoints`), and `lieFiltrationOnBuilding`
and `IsDegenerateLieCoset` (modules `KPLieFiltrationOnBuilding` and
`KPNilpotentCoset`).
