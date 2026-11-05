# Coefficient action on actual scheme components

Author: Worker 1107.

This internal derived construction compares coefficient conjugation on ordinary
rational-component quotient groups with a constructed action on connected
components of the actual base-changed scheme. Its provenance is the pullback
universal property and the published point, spectrum-map and quotient
constructions in `IdentityComponentRationalGalois` and `Torus.LatticeGalois`,
together with Mathlib's functorial map on connected components. It introduces no
external structure theorem.

Let `k` and `L` be arbitrary fields in a common arbitrary universe, with a
`k`-algebra structure on `L`, and let `G` be an actual group scheme over `Spec k`.
Write `G_L` for the actual pullback `baseChanged k L G` and `b_sigma` for
`galoisBaseMap k L sigma`, the contravariant spectrum map of the coefficient
automorphism. There is no smoothness, affineness, finite-type, characteristic,
perfection, algebraicity or Galois-extension assumption on this part.

`coefficientSchemeMap k L G sigma` is the pullback-scheme endomorphism `a_sigma`
characterized by the following two equations, proved as
`coefficientSchemeMap_fst` and `coefficientSchemeMap_snd`:

- Its composition with the projection to `G` is that same projection.
- Its composition with the projection to `Spec L` is the projection followed by
  `b_(sigma inverse)`.

The inverse in this second equation ensures agreement with the published
coefficient conjugation on rational sections. Pullback extensionality and the
spectrum-map laws prove `coefficientSchemeMap_one` and
`coefficientSchemeMap_mul`. With diagrammatic composition, the latter says
`a_(sigma * tau) = a_tau ≫ a_sigma`.
`coefficientSchemeIso` uses `a_(sigma inverse)` as inverse. This is an actual
scheme isomorphism lying over the original group scheme, semilinear over
`Spec L`.

`rationalConjugate_left` proves the section equation
`conjugate(sigma, x).left = b_sigma ≫ x.left ≫ a_sigma`. Its first pullback
projection follows from `baseChangeCoeffEquiv_rationalConjugate`; its second
follows from the section condition and the inverse spectrum-map equation.
`rationalConjugate_point` evaluates this equation at `basePoint L`. Congruence
and the uniqueness of the point of a field spectrum remove `b_sigma` from the
point formula.

`coefficientComponents` is the permutation of all connected components of the
underlying topological space of `G_L`. Its forward and inverse maps are induced
by the continuous maps of `coefficientSchemeIso`. Their inverse laws are proved
on representative scheme points. `coefficientComponents_mk` gives its formula
on a point class; the one and multiplication lemmas give the group homomorphism
`schemeComponentGaloisAction : Aut_k(L) →* Equiv.Perm (ConnectedComponents G_L)`.
`coefficientComponents_pointComponent` identifies this action on the component
of a rational section with the component of its coefficient conjugate.

For the remaining comparisons, `H` is smooth and affine over `k`, as required by
the published ordinary quotient `RationalComponentQuotient H` and its embedding
`rationalComponentEmbedding`. This quotient is `H(k)/H^0(k)`, where `H^0` is the
actual identity-component group scheme. The new comparisons are:

- `rationalComponentEmbedding_conjugate`: the existing embedding of
  `H_L(L)/(H_L)^0(L)` into scheme components intertwines the published quotient
  automorphism `rationalComponentConjugate` and `coefficientComponents`.
  Surjectivity of the ordinary quotient projection reduces the proof to the
  rational-point formula.
- `rationalComponentEmbedding_fixed_iff`: a quotient class belongs to
  `rationalComponentFixedSubgroup` precisely when its embedded component is fixed
  by every coefficient permutation. The reverse implication uses injectivity
  of the embedding.
- `coefficientComponents_mem_range_rationalComponentEmbedding_iff`: each
  coefficient permutation preserves and reflects the image of that embedding.
  Equivariance supplies preservation; the inverse quotient automorphism and
  injectivity of the component permutation supply reflection.
- `coefficientComponents_rationalComponentBaseChange`: the actual scheme
  component of a quotient class extended from `k` is fixed by every coefficient
  permutation. This combines equivariance with the published fixedness of
  `rationalComponentBaseChange`.

These are set permutations of scheme components and comparisons with ordinary
quotient groups. The construction supplies no group law on all scheme
components, scheme or sheaf quotient, surjectivity of rational classes onto all
components, or descent of fixed classes to the base field. It equips neither
the coefficient-automorphism group nor its action with a topology or continuity
result. It does not construct a based-root-datum star action.
