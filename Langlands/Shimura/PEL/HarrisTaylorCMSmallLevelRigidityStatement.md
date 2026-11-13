# Small-level rigidity target for the normalized CM moduli problem

This pair states, without proof, that the actual coarse-level rigidity of the
normalized Harris–Taylor CM moduli problem holds at every sufficiently small
original level. It links two existing Library predicates that were previously
unrelated. It adds no new moduli objects.

## The statement

`CMSmallLevelRigidityStatement D C … h htor` is the proposition: for every
`U : HarrisLevel D` satisfying `D.rationalInvolution.LevelSufficientlySmall U`,
the existing predicate `CMGeometricCoarseRigidity D C … h htor U` holds.

The two predicates are used exactly as published:

- `LevelSufficientlySmall U` (module `Langlands.Shimura.Unitary.SufficientlySmallLevels`)
  holds when there is a finite place `x` of `ℚ` at which every element of `U`
  whose image in the local similitude group has finite order has trivial image.
  The image is taken by `pointsMap (finiteEvaluation x)`.
- `CMGeometricCoarseRigidity U` (module
  `Langlands.Shimura.PEL.HarrisTaylorCMSchemeStabilizers`) quantifies over every
  algebraically closed field `Ω` in universe zero and every point
  `p : Spec Ω ⟶ Spec F` that is an admissible CM base. At the identity
  geometric point of `Spec Ω` it asserts `CoarseLevelHasNoAutomorphisms` at
  the coarse level `U`. That predicate (module
  `Langlands.Shimura.PEL.HarrisTaylorCMClassStabilizers`) says the following.
  Let `X` be a positive polarized action satisfying the Kottwitz determinant
  and numerical conditions, and let `a` be a level-`U` orbit of compatible
  frames on `X`. Let `e` be a rational self-isogeny of the action object, with
  `q ∈ ℚˣ`, that pulls the polarization back to `q` times itself. If
  postcomposition with `e` fixes `a`, then `e` is the identity.

The parameters are exactly the named prerequisites of
`CMGeometricCoarseRigidity`:

- the arithmetic datum `D` and the signature charts `C`;
- the tensor-pullback comparison and coherence statements;
- the Picard-zero statements `stability`, `square` and `universality`;
- the finite Weil transition `compatibility`;
- the rational profinite integer/adele comparison `h`;
- torsion finite étaleness `htor`.

The definition records them as hypotheses and proves none of them.

`CMSmallLevelRigidityStatement.rigid` is the immediate consequence that a
proof of the target supplies the rigidity premise `CMGeometricCoarseRigidity …
U.obj` for every object `U` of the existing small-level category
`SmallCMLevel D`. This is the premise taken by the published CM torsor and
coefficient-sheaf constructions, for example `HarrisTaylorCMCoefficientSheaf`
and `HarrisTaylorCMNormalSmoothTorsor`. Its Lean proof applies the target to
`U.obj` and the membership proof `U.property`.

## Sources

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
Chapter III.1:

- Printed p.90 (one-based PDF p.98) defines a sufficiently small `U`: its
  projection to `G(ℚ_x)` for some prime `x` contains no element of finite order
  other than 1.
- Printed p.91 (PDF p.99) defines the functor `X_U`. Two quadruples are
  equivalent when an isogeny carries the polarization to a `ℚˣ` multiple and
  preserves the action and the level orbit. The same page states: "Because `U`
  is sufficiently small this functor is represented by a smooth projective
  scheme", citing Kottwitz. It also states that `X_V → X_U` is Galois with
  group `U/V` for normal `V ⊆ U`. Both claims need the absence of nontrivial
  automorphisms of the objects at sufficiently small level.

Kottwitz, *Points on some Shimura varieties over finite fields* (1992), source
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`, printed p.390 (PDF p.18) gives
the analogous equivalence of quadruples over `ℤ_(p)`, with scalars in `ℤ_(p)ˣ`. Section 6, printed p.392 (PDF p.20),
restricts to compact open subgroups "small enough so that the objects in the
moduli problem have no nontrivial automorphisms". Kottwitz does not give a
criterion there. The finite-order criterion is the one stated by Harris–Taylor.

## Expected proof and scope

The standard argument is outlined here as a guide for a proof task; it is not
formalized. Suppose `e` fixes the level orbit of a frame `η`. Then
`e ∘ η = η ∘ u` for some `u ∈ U`. Comparing Weil pairings, the similitude
factor of `u` is `q`. It lies in the compact image of `U`, hence in `Ẑˣ`, so
`q = ±1`. Positivity of the Rosati involution gives `q > 0`, so `q = 1`. Since
`U` is compact, `u` preserves a lattice. Then `e` is an automorphism of an
isogenous abelian variety preserving the induced polarization. Hence `e` lies
in a finite automorphism group, and has finite order. The local image of `u` at the small place `x` then has
finite order, so it is trivial. Hence `e` acts trivially on the rational
`x`-adic Tate module. Since that action is faithful, `e = 1`.

The argument uses only the PEL moduli data, not the division-algebra
hypothesis of Harris–Taylor I.7. The target is stated for the general
`CentralSimpleUnitaryData` of the host. Over a field `Ω` of characteristic
zero, as here, no prime is excluded.

The formal statement is the cited sources' requirement, specialized to the
Library's own rigidity predicate. That specialization is internal: the
quantification over admissible algebraically closed field points and the
identity geometric point comes from `CMGeometricCoarseRigidity`. No proof, no
representability and no existence of small levels is asserted. Code and prose
are by Worker 19. The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
