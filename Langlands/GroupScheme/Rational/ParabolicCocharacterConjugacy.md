# Conjugating cocharacters into a maximal split torus

This is derived infrastructure for `StandardParabolicClassificationStatement`.
It proves the first half of the "standardness by containment" input of that
classification. Let `i` be a maximal split torus and `ν` a cocharacter of it.
If a dynamic parabolic `P(ζ)` contains `P(groupHom ν ≫ i)`, then `P(ζ)` is the
dynamic parabolic of some cocharacter of the same torus `i`. The unit does not
show that this cocharacter is dominant, nor that `P(ζ)` is a standard parabolic
`standardParabolic i ν J`. It proves no structural statement about reductive
groups, and it does not prove any published `…Statement`.

## Setting and premises

The field `k : Type u` is arbitrary. `G` is a group scheme over `Spec k` with
the instances `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
`ConnectedSpace G.X.left`. No reductivity is assumed. `T` is an arbitrary
commutative group scheme, and `i : T.toGrp ⟶ G` satisfies
`IsMaximalSplitTorus i`.

The conditional results take the following published, still unproved
statements as explicit hypotheses:

- `hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}`. Maximal split tori of
  a smooth connected affine group are conjugate under its rational points
  (Conrad–Gabber–Prasad, Theorem C.2.3).
- `hsmooth : DynamicSmoothStatement.{u}` and
  `hconn : DynamicConnectedStatement.{u}`. These are needed only for the two
  results inside `P(ζ)`. They say that representatives of `P(ζ)` are smooth,
  and connected when `G` is connected.

Every cocharacter factors through some maximal split torus. This fact is used
through the published theorem `cocharacterMaximalSplitTorus`, not as a premise.

## Declarations

- `comp_innerIso_hom_comp`, over an arbitrary base scheme. For a homomorphism
  `j : H ⟶ G` and a section `p` of `H`,
  `j ≫ Int_G(p ≫ j) = Int_H(p) ≫ j`; that is, inner automorphisms are natural
  along homomorphisms. The proof checks equality on points (`hom_ext_points`)
  and rewrites with `comp_innerIso_hom`, the Library's `constantPoint_comp`,
  `MonObj.mul_comp` and `GrpObj.inv_comp`.
- `Dynamic.range_le_parabolic`, over an arbitrary base scheme. The image of a
  cocharacter `ζ` lies in `P(ζ)`. The image lies in the torus centralizer of
  `ζ` (`range_le_torusCentralizer`). For `Gm` this centralizer is the dynamic
  centralizer (`torusCentralizer_gm_eq_dynamicCentralizer`), which is
  contained in `P(ζ)` (`Dynamic.centralizer_le_parabolic`).
- `exists_innerIso_comp_eq_cocharacter` (premise `hconj`). For every cocharacter
  `ζ` of `G` there are `g ∈ G(k)` and `ξ ∈ X_*(T)` with
  `ζ ≫ Int(g) = groupHom ξ ≫ i`. Proof: `cocharacterMaximalSplitTorus` writes
  `ζ = groupHom ν₁ ≫ i₁` with `i₁` maximal. `hconj` gives `g` and an
  isomorphism `e` with `i₁ ≫ Int(g) = e ≫ i`. Then `ξ` is `ν₁` composed with
  `e`.
- `exists_parabolic_isRationallyConjugate_cocharacter` (premise `hconj`). Hence
  `P(ζ)` is rationally conjugate to `P(groupHom ξ ≫ i)`. This uses the published
  `Dynamic.parabolic_isRationallyConjugate`.
- `exists_mem_parabolic_innerIso_comp_eq_cocharacter` (premises `hconj`,
  `hsmooth`, `hconn`). Assume `P(groupHom ν ≫ i) ≤ P(ζ)`. Then the conjugating
  point `g` can be chosen in `P(ζ)(k)`. Proof: take the published closed
  representative `j = Dynamic.Affine.parabolicHom ζ` of `P(ζ)`
  (`isRepresentedBy_parabolicHom`, `isClosedSubgroup_parabolicHom`). Its source
  `H` is smooth by `hsmooth` and connected by `hconn`. It is affine over `k`
  because the closed immersion `j` composes with the affine structure morphism
  of `G`. By `Dynamic.range_le_parabolic`, `ζ` factors through `H`. The
  published `IsMaximalSplitTorus.exists_lift_of_parabolic_le` lifts `i` to a
  maximal split torus `iH` of `H` with `iH ≫ j = i`. Applying
  `cocharacterMaximalSplitTorus` and `hconj` inside `H` gives `p ∈ H(k)`. Then
  `g = p ≫ j` lies in `P(ζ)(k)`, and `comp_innerIso_hom_comp` gives
  `ζ ≫ Int(g) = groupHom ξ ≫ i`.
- `exists_parabolic_eq_cocharacter_of_parabolic_le` (premises `hconj`,
  `hsmooth`, `hconn`). Under the same containment there is `ξ ∈ X_*(T)` with
  `Dynamic.parabolic ζ = Dynamic.parabolic (groupHom ξ ≫ i)`. This is an
  equality of subgroup functors, so it holds on every test scheme. Proof: with
  `g` from the previous result, `Dynamic.parabolic_eq_comap_of_iso` gives
  `P(ζ) = P(groupHom ξ ≫ i).comap Int(g)`. `SubgroupFunctor.eq_comap_iso_iff`
  and `innerIso_inv_hom` turn this into
  `P(ζ).comap Int(g⁻¹) = P(groupHom ξ ≫ i)`. Since `g⁻¹ ∈ P(ζ)(k)`, the
  published `SubgroupFunctor.comap_innerIso_hom_eq_of_mem` shows that the
  left side is `P(ζ)` itself. No point-density or infinite-field argument is
  used.
- `parabolicCocharacterOfParabolicLE` (same premises). A cocharacter `ξ` of `i`
  with `P(ζ) = P(groupHom ξ ≫ i)`, chosen by `Classical.indefiniteDescription`
  and bundled with this equality. The choice is not canonical.

## Provenance

The argument is the one in the proof of Conrad–Gabber–Prasad, Proposition
C.2.4 (printed pp. 594–595). There, "by Theorem C.2.3 applied to P we can
replace λ with a suitable P(k)-conjugate to arrange that λ takes values in S".
The remark after the proof reads "by Theorem C.2.3 applied to P we can find
λ ∈ X_*(S) such that P = P_G(λ)".

The Lean unit follows the same route with three differences:

- It works with the dynamic parabolic `P(ζ)` itself rather than a
  pseudo-parabolic subgroup `P_G(λ) R_{u,k}(G)`.
- The containment `P(groupHom ν ≫ i) ≤ P(ζ)` replaces the source's assumption
  that the maximal split torus lies in `P`. The lifting lemma
  `exists_lift_of_parabolic_le` turns this containment into a maximal split
  torus of `P(ζ)`.
- Smoothness and connectedness of `P(ζ)` (CGP 2.1.8) enter as the premises
  `hsmooth` and `hconn`.

The functor equality in the last step is an internal derivation from the
published conjugation lemmas.
