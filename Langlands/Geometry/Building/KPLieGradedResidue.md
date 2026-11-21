# Residue-field graded Lie pieces and the opposite-depth duality

This module continues `Langlands.Geometry.Building.KPLieGradedPairing`. That
module proves that the residue pairing between `𝔤*_{x,r}` and the graded piece
`𝔤_{x,-r}/𝔤_{x,(-r)+}` is surjective onto all `𝒪`-linear forms and has kernel
`𝔤*_{x,r+}`. It does not construct the resulting isomorphism, and it builds the
residue-field vector-space structure of the graded pieces only inside a proof.
This module supplies both as declarations, together with finiteness and the
compatibility with the stabilizer action.

## Setting

As in `KPLieGradedPairing`: `F` is a nonarchimedean local field with
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, valuation
ring `𝒪 = 𝒪[F]`, maximal ideal `𝔪 = 𝓂[F]` and residue field `𝔣 = 𝓀[F]`. The local-field
class covers mixed and equal characteristic. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]`, `𝔤 = GenericLie 𝒪[F] G` and
`𝔤* = Module.Dual F 𝔤`. `P : ParahoricBuildingData G` and
`L : P.LieFiltrationData` are supplied, `x : P.Apartment` and `r` is real. The
module uses the published `lieFiltrationReal`, `lieFiltrationPlusReal`,
`dualLieFiltration`, `dualLieFiltrationPlus` and `IsPeriodic`
(`KPLieFiltrationDual`), `gradedLie`, `dualGradedLie`, `gradedAdjoint`,
`dualGradedAdjoint`, `filtrationStabilizer`, `coadjoint` and
`IsLeftContinuousAt` (`KPLieGradedAction`), and `gradedLieDualPairing` with its
surjectivity, kernel, torsion and invariance theorems (`KPLieGradedPairing`).

Here `L.gradedLie x r` is `𝔤_{x,r}` modulo the inverse image of `𝔤_{x,r+}`.
`L.dualGradedLie x r` is the image of `𝔤*_{x,r}` in `𝔤* ⧸ 𝔤*_{x,r+}`; under the
periodicity hypothesis both are KP's quotients `𝔤_{x,r}/𝔤_{x,r+}` and
`𝔤*_{x,r}/𝔤*_{x,r+}` (see the Markdown of `KPLieGradedAction`).

All declarations are in
`Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData`.

## Declarations

### The projection onto the dual grade

- `dualGradedLieProjection x r : 𝔤*_{x,r} →ₗ[𝒪] dualGradedLie x r` is the
  inclusion into `𝔤*` followed by the quotient map, restricted to its image.
  `dualGradedLieProjection_surjective` holds by definition of the image.
  `ker_dualGradedLieProjection` identifies the kernel with
  `𝔤*_{x,r+} ∩ 𝔤*_{x,r}` (as a `comap` along the inclusion).
- `dualGradedLieRep x r Y` is a chosen preimage and
  `dualGradedLieProjection_rep` says that it projects to `Y`.

### Residue-field structures and finiteness

- `gradedLieResidueModule hL x r` is the `𝔣`-module structure on
  `gradedLie x r` given by Mathlib's `Module.IsTorsionBySet.module` applied to the
  published `isTorsionBySet_gradedLie` (periodicity implies that `𝔪` kills the
  grade). `gradedLieResidue_isScalarTower` says that the `𝒪`-action factors
  through it.
- `finite_gradedLie hL x r`: under periodicity and `Module.Finite 𝒪` for
  `𝔤_{x,r}`, the grade is a finite set. It is a finitely generated module over
  the finite field `𝔣` (`Module.Finite.of_restrictScalars_finite`,
  `Module.finite_of_finite`). A lattice instance supplies the finiteness
  hypothesis through Mathlib's `Submodule.IsLattice.finite`.
- `smul_mem_dualLieFiltration_add_one hL ha hX`: under periodicity, `a ∈ 𝔪`
  and `X ∈ 𝔤*_{x,r}` give `a • X ∈ 𝔤*_{x,r+1}`. For `t > -(r+1)` and
  `Y ∈ 𝔤_{x,t}`, `(aX)(Y) = X(aY)` and `aY ∈ 𝔤_{x,t+1}` with `t+1 > -r`
  (published `smul_mem_lieFiltrationReal_add_one`).
- `isTorsionBySet_dualGradedLie hL x r`: hence `𝔪` kills the dual grade,
  because `𝔤*_{x,r+1} ⊆ 𝔤*_{x,r+}`.
- `dualGradedLieResidueModule hL x r` and
  `dualGradedLieResidue_isScalarTower` are the corresponding `𝔣`-module
  structure on `dualGradedLie x r` and its scalar tower.

### The duality

The remaining declarations assume periodicity `hL`, left continuity
`hc : L.IsLeftContinuousAt x (-r)` and the lattice instance
`[Submodule.IsLattice F (L.lieFiltrationReal x (-r))]`. These are exactly the
hypotheses of the published surjectivity and left-kernel theorems.

- `gradedLieDualPairing_eq_of_projection_eq hL hc h` and
  `projection_eq_of_gradedLieDualPairing_eq hL hc h`: for `X, X' ∈ 𝔤*_{x,r}`,
  the two images in the dual grade agree exactly when the two graded pairings
  agree. Both directions only need periodicity and left continuity. Write
  `X = D + X'` with `D = X - X'` formed in `𝔤*`. Each condition says that `D`
  maps to zero, and both kernels are `𝔤*_{x,r+}` by `ker_dualGradedLieProjection`
  and the published `gradedLieDualPairing_eq_zero_iff`.
- `dualGradedLieToDual hL x r hc : dualGradedLie x r →ₗ[𝒪] (gradedLie x (-r) →ₗ[𝒪] 𝔣)`
  sends `Y` to the graded pairing of its chosen preimage. Additivity and
  `𝒪`-linearity follow from the first comparison. `dualGradedLieToDual_projection`
  says it sends the class of `X` to `gradedLieDualPairing hL x r X`, so the choice
  does not matter.
- `dualGradedLieToDual_bijective`: injectivity is the second comparison;
  surjectivity is the published `gradedLieDualPairing_surjective`.
- **`dualGradedLieLinearEquiv hL x r hc`** is the resulting `𝒪`-linear
  equivalence `𝔤*_{x,r}/𝔤*_{x,r+} ≃ Hom_𝒪(𝔤_{x,-r}/𝔤_{x,(-r)+}, 𝔣)`, with
  `dualGradedLieLinearEquiv_projection` giving its value on classes.
- `dualGradedLieLinearEquiv_dualGradedAdjoint hL x r hc g Y Z`: for `g` in the
  filtration stabilizer, the image of `g · Y` evaluated at `Z` is the image of `Y`
  evaluated at `Ad(g⁻¹) Z`. This is the published invariance
  `gradedLieDualPairing_gradedAdjoint` applied to `Ad(g⁻¹) Z`, with
  `gradedAdjoint` a group homomorphism. The equivalence thus identifies the
  coadjoint action on the dual grade with the contragredient of the graded
  adjoint action.
- **`dualGradedLieResidueEquiv hL x r hc`** is the same map as an `𝔣`-linear
  equivalence between the dual grade and `Module.Dual 𝔣 (gradedLie x (-r))`,
  for the two residue module structures above. Since `𝒪 → 𝔣` is surjective, the
  `𝒪`-linear forms into `𝔣` are the `𝔣`-linear forms, and an `𝒪`-linear
  equivalence is `𝔣`-linear (`LinearMap.extendScalarsOfSurjectiveEquiv`,
  `LinearEquiv.extendScalarsOfSurjective`).
- `finite_dualGradedLie hL x r hc`: the dual grade is finite, as the
  `𝔣`-dual of a finite `𝔣`-vector space.

### Implementation note

The equivalence is built from chosen representatives and
`LinearEquiv.ofBijective`, not from the first isomorphism theorem. Mathlib's
`LinearMap.quotKerEquivOfSurjective` needs a `Ring` instance on `𝒪[F]`, while
the published pairing's type uses the semiring obtained from the subring's
commutative semiring structure; the two do not unify at instance transparency.
For the same reason, differences of elements of `𝔤*_{x,r}` are formed in the
ambient `𝔤*`. The resulting declarations do not depend on the choice of
representatives (`dualGradedLieLinearEquiv_projection`).

## Comparison with Kaletha–Prasad

KP 13.3.1 (printed p. 470; PDF p. 501) defines, for any real `r`,
`𝔤*_{x,r} = {X ∈ 𝔤* | X(Y) ∈ 𝔪 for all Y ∈ 𝔤_{x,(-r)+}}` and the filtration
by `𝔤_{x,r+}`. KP 13.3.4 (printed p. 471; PDF p. 502) extends the conjugation
action to an action of `𝒢_x^0` on `𝒢_{x,r}`, hence on `𝔤_{x,r}` and `𝔤*_{x,r}`.
This descends to an `𝔣`-rational action of the special fibre on
`𝔤_{x,r} ⊗_𝔬 𝔣`, which induces an `𝔣`-rational action of the reductive quotient
`G_x` on `𝔤_{x,r}/𝔤_{x,r+}` and on `𝔤*_{x,r}/𝔤*_{x,r+}`. In particular both
quotients are treated there as `𝔣`-vector spaces. KP do not state the duality between
`𝔤*_{x,r}/𝔤*_{x,r+}` and `𝔤_{x,-r}/𝔤_{x,(-r)+}` in §13.3. This module derives it
from the definition of `𝔤*_{x,r}` under the stated hypotheses, constructs the
`𝔣`-structures on the two actual quotients, and records the compatibility with the
actions at the level of rational points that stabilize the supplied filtration.

The periodicity hypothesis is the identity `𝔤_{x,r+n} = 𝔪^n 𝔤_{x,r}` of KP 13.3.1
(Proposition 8.5.16, printed p. 319; PDF p. 350, for the models `𝒢_{x,r}`). The
lattice hypothesis is KP's statement that `𝔤_{x,r}` is an `𝔬`-lattice. Left
continuity is discussed in the Markdown of `KPLieGradedPairing`; the Library's
`KPLieFiltrationLeftContinuity` gives a sufficient criterion. The Library
normalization `ord(Fˣ) = ℤ` makes the depth shift by one correspond to `𝔪`.

The authors' corrections of 1 November 2024 have no entry for §13.3 or §8.5
(their Chapter 8 entries stop in §8.4; the Chapter 13 entries, PDF p. 49, concern
13.5.2, 13.6.2 and 13.8.5).

## Provenance

Derived. The residue structures, the finiteness statements and the duality are
internal consequences of KP's definition of `𝔤*_{x,r}`, the published pairing
theorems and the stated hypotheses; no published statement is transcribed.
Besides the Library declarations named above, the Lean code uses Mathlib's
`Module.IsTorsionBySet.module` and `.isScalarTower`,
`Module.Finite.of_restrictScalars_finite`, `Module.finite_of_finite`,
`LinearMap.codRestrict`, `Submodule.Quotient.mk_eq_zero`,
`LinearEquiv.ofBijective`, `LinearMap.extendScalarsOfSurjectiveEquiv`,
`LinearEquiv.extendScalarsOfSurjective` and
`IsLocalRing.ResidueField.algebraMap_eq`. No external code is adapted.

## Not claimed

- Periodicity, the lattice property at `-r` and left continuity at `-r` are
  hypotheses. None is derived from the supplied data, and Proposition 8.5.16 is
  not formalized.
- The equivariance concerns rational points in the filtration stabilizer. No
  algebraic action of `𝒢_x^0` or of the reductive quotient on these spaces, and
  no `𝔣`-rationality of such an action, is constructed.
- No duality between the full lattices `𝔤_{x,r}` and `𝔤*_{x,-r}` is stated,
  and no comparison of the grades with the group quotients
  `G(F)_{x,r}/G(F)_{x,r+}` (Theorem 13.5.1) is made.
