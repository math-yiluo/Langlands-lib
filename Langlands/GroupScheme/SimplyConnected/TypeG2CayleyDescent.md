# Inner forms of the split Cayley automorphism group

The main theorem `TypeG2CayleyDescent.exists_iso_automorphismGroup` works
over any field `K` and finite Galois extension `L/K`. Write `H` for
`splitGroup K`, the actual automorphism group scheme
`(CayleyDatum.split K).automorphismGroup`. The theorem assumes:

- `hq`, a proof that the identity of `H` is an adjoint quotient;
- `e`, local isomorphisms from `H` to a group scheme `G` over the cover
  `Spec L → Spec K` (`LocalGroupIso H G (ringTest K L)`);
- a cocycle `ξ` with values in `H` such that `e` has discrepancy `ξ` for
  the inner action of `hq`.

It produces an actual `CayleyDatum K` `c` and a group-scheme isomorphism
`G ≅ c.automorphismGroup`. The isomorphism is an actual isomorphism of
group schemes over `Spec K`, obtained by fpqc descent, not a comparison of
rational points.

## Points of automorphism group schemes

- `CayleyDatum.points c T` identifies the points of `c.automorphismGroup`
  over any test scheme `T` with the automorphism subgroup of
  `GL₈(Γ(T))`. It is the published `Corepresented.pointsEquiv` of the
  cut-out functor from `CayleyAutomorphismGroup`. `points_naturality`
  says that restriction along `T' ⟶ T` acts on matrices by the
  global-section map.
- `points_comp`: for a point `s : V ⟶ Spec L` and a point `x` over
  `Spec L`, the matrix of `s ≫ x` is the matrix of `x` moved to `L` (by
  `Γ(Spec L) ≅ L`) and then along the scalar map `pointScalars s`.
  `pointScalars_id` and `gammaSpec_comp_algebraMap` are the corresponding
  facts for the identity point.

## Galois values

- `galoisValue ξ σ = ξ(1, σ)` is a point of `H` over `Spec L`.
  `galoisValue_mul` is the crossed-homomorphism identity, from the
  cocycle identity and naturality of `ξ` (as in the published special
  linear case).
- `galoisMatrix ξ σ ∈ GL₈(L)` is its matrix.
  `galoisMatrix_isAutomorphismMatrix` shows that it is an automorphism
  matrix of the split datum along `algebraMap K L`, using
  `IsAutomorphismMatrix.map`. `galoisMatrix_mul` gives the matrix cocycle
  identity `g_{στ} = g_σ σ(g_τ)`.

## Charts and descent

Assume `P ∈ GL₈(L)` with `IsTwist P`, and let `C` be the automorphism
group scheme of `datum hP` from `CayleyGaloisTwist`.

- `chartPoints hP s` is a group isomorphism from the points of `H` to the
  points of `C` over `V`, for each point `s : V ⟶ Spec L`. Its value on
  matrices is `h ↦ Q⁻¹ h Q`, where `Q` is the image of `P` along
  `pointScalars s` (`chartPoints_val`). It is built from
  `CayleyDatum.points`, `conjEquiv` and the equality
  `pointScalars s ∘ algebraMap K L = algebraMap K Γ(V)`.
- `chartLocalIso hP` packages these as local isomorphisms. Naturality
  holds because restriction maps both `Q` and the point matrix along the
  same global-section map.
- `chartPoints_galois`: assume `g_σ σ(P) = P` for all `σ`. Then the chart
  at `s` applied to the inner action of `s ≫ ξ(1, σ)` equals the chart at
  `s ≫ σ`. Since the adjoint quotient is the identity, the published
  `innerAction_act_lift` makes the inner action conjugation. With
  `g_σ = P σ(P)⁻¹` the identity reduces to a group computation.
- `chartLocalIso_hasDiscrepancy`: the charts have discrepancy `ξ`. This
  uses `hasDiscrepancy_iff_overlap` and the published Galois-pair
  criterion `hasOverlapDiscrepancy_of_galois`.
- `compareLocalIso` composes `e⁻¹` with the charts.
  `compareLocalIso_isIndependent` proves that it does not depend on the
  point of the cover, since `e` and the charts have the same discrepancy.
- `exists_iso_automorphismGroup`: `GeneralLinearGaloisFixedBasis` gives
  `P` with `g_σ σ(P) = P`. Then `IsTwist P` holds, since
  `P σ(P)⁻¹ = g_σ`. The published `LocalGroupIso.descend` along the fpqc
  cover `Spec L → Spec K` (`fieldExtension_fpqc`) gives
  `G ≅ (datum hP).automorphismGroup`.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`.
Theorem 26.19 (printed p.373 / PDF p.396) states that `C ↦ Aut_alg(C)` is
an equivalence from Cayley algebras to simple groups of type `G₂`. Its
proof has two steps:

- the field-extension functor on Cayley algebras satisfies the descent
  condition. This is Proposition 26.4 (printed pp.362–363) for the
  representation of `GL(C)` on `Hom(C ⊗ C, C)` and the multiplication
  tensor. Proposition 26.4 in turn uses the vector-space Galois descent
  of Lemma 18.1 (printed pp.279–280);
- Proposition 26.2 (printed p.361) then gives the equivalence, because
  every automorphism of a type-`G₂` group over a separably closed field is
  inner (Theorem 25.16).

This module does not formalize that groupoid argument. It formalizes the
step needed here, at a finite Galois level `L/K` and on the scheme level:
an inner twist of the split automorphism group by a cocycle `ξ` is the
automorphism group of an actual Cayley datum over `K`. The implemented
route is a coordinate one:

- the Galois values of `ξ` form a `GL₈(L)`-valued cocycle `g_σ`;
- `GeneralLinearGaloisFixedBasis` (Hilbert's Theorem 90 for `GL_n`) gives
  `P` with `g_σ σ(P) = P`;
- `CayleyGaloisTwist` builds the twisted datum, and the matrix-conjugation
  charts have discrepancy `ξ`;
- fpqc descent of local isomorphisms gives `G ≅ (datum hP).automorphismGroup`.

KMRT Proposition 29.1 (printed p.392 / PDF p.415), which describes twisted
forms of a tensor by Galois cohomology, and Theorem 29.2 (printed p.392),
Hilbert's Theorem 90 for `GL₁` of a separable algebra, are comparisons for
this construction; they are not the source's proof of Theorem 26.19. The
structure of the module follows the published special-linear inner-form
proof (`SpecialLinearInnerFormNormOneProof`).
