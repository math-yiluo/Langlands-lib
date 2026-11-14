# Springer's compactness theorem from the split inputs and a Galois twisting

Author: Worker 5268.

This module derives Springer's compactness criterion, in its "if" direction,
from three published statements, which are hypotheses of the final theorem:

- `SplitAdelicFundamentalSetStatement`: the fundamental-set theorem (F) for
  split groups;
- `SplitSiegelOverlapStatement`: Springer's Proposition 2.6 for split groups;
- `GaloisBorelTwistingStatement`: a finite Galois splitting field with a Galois
  twisting of a split Borel pair (Springer §3.4).

The conclusion is
`Langlands.Global.AdelicSiegelFactors.CentralSplitCompactQuotientStatement`
(module `Langlands.Global.AdelicSiegelChamberReduction`). Suppose a connected
reductive group `G` over a number field `F` has a central maximal split
torus. Then `G(F) \ G(𝔸_F)¹` has a compact rational cover. The argument is
the second half of the proof of (C) in T. A. Springer, *Reduction theory over
global fields* (1994), §3.5. The first half is the theorem
`splitGaloisOverlapMatching` (module
`Langlands.Global.AdelicGaloisOverlapMatchingProof`).

Notation is that of `AdelicGaloisOverlapMatching`: `G_L`, `Δ`, `j_H`, `P_H` and
`|β(t)|`.

## The box lemma

`inv_mem_torusCharacterBox_of_bounds`: if `d < |β(t)| ≤ c` for every `β ∈ Δ`,
then `t⁻¹` lies in `torusCharacterBox L T Δ b` with
`b = max 1 (max c d⁻¹)`, that is, `b⁻¹ ≤ |β(t⁻¹)| ≤ b`. Since
`|β(t⁻¹)| = |β(t)|⁻¹`, the lower bound comes from `|β(t)| ≤ c ≤ b` and the
upper bound from `|β(t)|⁻¹ ≤ d⁻¹ ≤ b`. Both use `inv_anti₀`.

## No matching for a central maximal split torus

`hasBoundedRootScalarExtensionCover_of_hasTwistedOverlapMatching` assumes that
`G` has a central maximal split torus `s`, that `G` and `G_L` are connected
reductive, and that `i` is a maximal split torus of `G_L` with generic
cocharacter `ν`. Under these hypotheses `HasTwistedOverlapMatching F L G T i ν`
implies `HasBoundedRootScalarExtensionCover F L G T i ν` (module
`Langlands.Global.AdelicGaloisBoundedRootCompact`).

Proof. Let `C`, `c` and `d` come from the matching. Take the radius
`b = max 1 (max c d⁻¹)` and the compact set `C⁻¹`. Given `g`, factor `g⁻¹` as
`x · i(t) · j_∅(p) · rationalSection q`.

- *Every root norm exceeds `d`.* Suppose `|α(t)| ≤ d` for some `α ∈ Δ`. The
  matching gives a family `J` with `J 1 = Δ \ {α}` that satisfies the
  inverse-orbit matching condition for `innerIso q⁻¹`. The Library theorem
  `IsMaximalSplitTorus.eq_simpleRelativeRoots_of_inverse_orbit_matching`
  (module `Langlands.GroupScheme.Descent.GaloisParabolicOrbitMatching`) uses
  the central maximal split torus to conclude `J 1 = Δ`. Then
  `Δ \ {α} = Δ`, which contradicts `α ∈ Δ`.
- *Cover.* Invert the factorization of `g⁻¹`. With the rational point `q`,
  the product `q · g` (scalar extended) equals
  `j_∅(p⁻¹) · i(t⁻¹) · x⁻¹`. Here `j_∅(p⁻¹)` lies in the norm-one minimal
  parabolic, and `i(t⁻¹)` has norm one. By the box lemma, `t⁻¹` lies in the
  box of radius `b`, and `x⁻¹ ∈ C⁻¹`. This is the membership that
  `HasBoundedRootScalarExtensionCover` requires.

## The closing theorem

`centralSplitCompactQuotient_of_splitInputs (hF hO hT)` proves
`CentralSplitCompactQuotientStatement`. Given `F`, `G` and a central maximal
split torus, `hT` gives a model `D : FiniteGaloisSplitMaximalModel G`, a
generic `ν` and a Galois twisting. `splitGaloisOverlapMatching hF hO` gives the
twisted matching. The previous theorem turns it into a bounded-root cover.
Here `D.isMaximalTorus.isMaximalSplitTorus D.isSplitTorus` says that the split
torus is maximal split, and `D.isConnectedReductive` gives reductivity of
`G_L`. Finally, the Library theorem
`FiniteGaloisSplitMaximalModel.hasCompactNormOneRationalCover_of_boundedRootCover`
yields the compact rational cover.

The theorem keeps (F), Proposition 2.6 and the twisting as explicit
hypotheses. The module `AdelicSpringerCentralCompactnessProof` discharges them
with `splitAdelicFundamentalSet`, `splitSiegelOverlap` and
`galoisBorelTwisting_of` to obtain the unconditional theorem.

## Axioms

`#print axioms centralSplitCompactQuotient_of_splitInputs` reports only
`propext`, `Classical.choice` and `Quot.sound`.
