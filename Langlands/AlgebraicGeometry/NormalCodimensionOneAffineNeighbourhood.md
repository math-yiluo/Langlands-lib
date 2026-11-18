# Common affine neighbourhoods of finite normal codimension-one points

This file constructs the affine open in Bosch–Lütkebohmert–Raynaud,
*Néron Models* (Springer, 1990), §6.4 Lemma 4, printed p.155
(PDF p.162). The registered source is
`bosch-lutkebohmert-raynaud-1990-neron-models`, content SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.

For every universe `u`, let `R : Type u` be a noetherian commutative
ring, let `X : Scheme.{u}`, and let `p : X ⟶ Spec R` be locally of
finite type, quasi-compact and separated. Suppose every stalk of
`X` is a domain and integrally closed. For a finite `E : Set X`
whose stalk rings have `ringKrullDim ≤ 1`,
`normalCodimensionOneAffineNeighbourhood p hn E hE hd` returns

```lean
{U : X.Opens // IsAffineOpen U ∧ E ⊆ U}
```

The constructor has exactly these hypotheses. No integral,
connected, quasi-affine, quasi-projective or common-neighbourhood
premise is added. The empty selected set, disconnected or empty
scheme, arbitrary noetherian base ring, and generic points are included.

The implemented proof has the following steps.

1. In the integral separated locally noetherian case, a normal stalk
   of dimension at most one is a valuation ring in the function field;
   the field case is allowed. The actual ring
   `stalkIntersection X E` is their intersection.
2. For nonempty finite `E`, the finite-valuation intersection theorem
   makes the function field a fraction field of the intersection,
   and presents each maximal localization by one of the selected
   stalks, with the canonical ring maps. The theorem works for
   arbitrary finite valuation families, including the whole-field
   valuation at a generic point. If `E` is empty, choose an affine
   neighbourhood of the generic point directly.
3. Compatible maps from the spectra of those stalks extend a generic
   rational map from the intersection's spectrum into `X`. Its domain
   contains every maximal ideal and hence is the entire affine
   spectrum. This constructs an actual affine stalk model over the base.
4. Local finite presentation factors the model map through a finitely
   generated subalgebra. Inclusion of this subalgebra in the selected
   stalks gives a rational map back from `X` to that affine stage,
   defined at every selected point. It is dominant and is a section
   of the stage map on its domain.
5. A dominant section of a separated morphism from a reduced scheme
   is an open immersion. Finite prime avoidance in the affine stage
   then constructs one affine open containing the selected set.
6. Under the full base hypotheses, `X` is noetherian and its domain
   stalks give finite disjoint integral open irreducible components.
   Normality and the stalk-dimension bound restrict to those components.
   Apply the integral constructor and take the finite disjoint union
   of the resulting affine opens.

The source uses valuation approximation for the semilocal intersection
and cites EGA IV₃ 8.10.5 for its finite-type approximation step. Here
the intersection theorem is proved by a geometric-sum argument, and
the scheme construction uses maximal-domain rational maps,
local finite-presentation descent, and dominant sections.
`integralNormalCodimensionOneAffineNeighbourhood` exposes the integral
case; the final constructor supplies its proof to the component
reduction. No downstream DVR or group-scheme conclusion is used.
