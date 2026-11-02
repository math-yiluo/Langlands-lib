# Representative maps into double cosets of standard parabolics

This module works with a group scheme `G` over a field `k` with `IsAffineHom G.X.hom`,
a homomorphism `i : T.toGrp ⟶ G` and a cocharacter `ν : cocharacterLattice T`. It needs
no reductivity, maximal-splitness or genericity hypothesis. Everything happens in the
categorical rational-point group `G(k) = (Over.mk (𝟙 (Spec k)) ⟶ G.X)`. The subgroups
used are the published ones:
- `normalizerPoints i` (`N(k)`);
- `centralizerPoints i` (`Z(k)`);
- `standardLeviPoints i ν J` (`L_J(k)`);
- `standardParabolicPoints i ν J` (`P_J(k)`);
- the quotient `relativeWeylGroup i = N(k)/Z(k)`;
- its image subgroup `standardRelativeWeylGroup i ν J`.

## Contents

- `centralizerPoints_le_standardLeviPoints` and
  `centralizerPoints_le_standardParabolicPoints`: `Z(k) ≤ L_J(k) ≤ P_J(k)` for every set
  `J` of characters. The proof rewrites `Z(k)` as the base points of the published
  `torusCentralizer i` (`torusCentralizer_carrier_base`). It then uses
  `torusCentralizer_le_standardLevi` and `standardLevi_le_standardParabolic`.
- `relativeWeylDoubleCoset i ν J K : relativeWeylGroup i → P_J(k) \ G(k) / P_K(k)`. This
  is the representative map. It sends the class of a normalizing point `n` to the double
  coset `P_J(k) n P_K(k)`, as an element of Mathlib's `DoubleCoset.Quotient`. It is
  defined by `Quotient.liftOn'`. The map is well defined because two representatives
  `a, b` of the same class satisfy `a⁻¹ b ∈ Z(k) ≤ P_K(k)`, hence `b = 1 · a · (a⁻¹ b)`.
  `relativeWeylDoubleCoset_mk` records the value on `QuotientGroup.mk n`; it holds by
  definition.
- `coe_mem_standardLeviPoints_of_mk_mem` and `coe_mem_standardParabolicPoints_of_mk_mem`:
  if the class of `n ∈ N(k)` lies in `standardRelativeWeylGroup i ν J`, then `n` lies in
  `L_J(k)` and hence in `P_J(k)`. Membership in `standardRelativeWeylGroup` provides a
  representative `m ∈ L_J(k)` of the same class (`mem_standardRelativeWeylGroup_iff`).
  Then `n = m · (m⁻¹ n)` with `m⁻¹ n ∈ Z(k) ≤ L_J(k)`.

These are unconditional consequences of the definitions. They assume no Bruhat
decomposition, Tits axiom or structure theorem. Write `π : N(k) → N(k)/Z(k)` for the
quotient map and `W_J = standardRelativeWeylGroup i ν J`. The last two lemmas prove an
inclusion inside the normalizer: `π⁻¹(W_J) ⊆ N(k) ∩ P_J(k)`. The converse inclusion
`N(k) ∩ P_J(k) ⊆ π⁻¹(W_J)` concerns only normalizing points; `P_J(k)` itself is not
contained in `N(k)`. That converse is a structural fact. It needs `G` connected
reductive, `i` maximal split, `ν` generic and `J` a set of simple relative roots. It is
not proved here. The companion statement module
`Langlands.GroupScheme.Rational.TitsStandardParabolicStatement` states both directions
together, for `n ∈ N(k)`, as `NormalizerStandardParabolicStatement`.

## Sources and provenance

- Borel–Tits, *Groupes réductifs* (1965), source `borel-tits-1965-groupes-reductifs`:
  - §5.15 (printed p.100, PDF p.47) indexes the double cosets `P_k · n · P_k` by classes
    `w ∈ ₖW = N_k/Z(S)_k`.
  - §5.20 (printed p.102, PDF p.49) describes `P_Θ,k \ G_k / P_Θ',k` through
    representatives `n ∈ N_k` of `w`.
  - Both rely on the representative-independence that `relativeWeylDoubleCoset` makes
    explicit.
- Renard, *Représentations des groupes réductifs p-adiques* (2026 version), source
  `renard-2026-representations-groupes-reductifs-padiques`, V.4.3 (printed p.119, PDF
  p.125). It notes that `w · M = g M g⁻¹` does not depend on the lift `g` of `w`, because
  `M_∅ = Z_G(A_∅) ⊂ M`. This is the same argument with the Levi `M` in place of `P_K`.

The use of Mathlib's `DoubleCoset.Quotient` and `Quotient.liftOn'` on the published
quotient is a **derived** packaging of the sources' "double coset of a representative".
The lemma names are internal.
