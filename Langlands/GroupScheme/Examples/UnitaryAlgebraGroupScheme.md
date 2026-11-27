# The special unitary group scheme of a central simple algebra with involution

Module `Langlands.GroupScheme.Examples.UnitaryAlgebraGroupScheme`, namespace
`Langlands.GroupScheme.UnitaryAlgebra`.

## Setting

`F` and `E` are fields in one universe `u` with `Algebra F E` and `FiniteDimensional F E`.
`B` is a ring with `Algebra E B`, `Algebra F B`, `IsScalarTower F E B`,
`FiniteDimensional E B`, `Algebra.IsCentral E B`, `IsSimpleRing B` and
`FiniteDimensional F B`. `τ : Quaternionic.FirstKindInvolution F B` is an `F`-linear
involution. These are the hypotheses of the Library's
`UnitaryPoints.specialUnitaryPoints E τ R`, the units `u ∈ (R ⊗_F B)ˣ` with
`u τ_R(u) = 1` and relative reduced norm `relativeNorm F E B R u = 1` in `E ⊗_F R`
(module `Langlands.Algebra.CentralSimple.UnitaryPoints`), plus the two finiteness
hypotheses over `F`.

## Equations

The Library's unit group scheme `FiniteAlgebraUnits.groupScheme` of `B` over `F` (with the
basis `IsometryCut.unitsBasis F B`) is corepresented by the algebra
`FiniteAlgebraUnits.candidateRing`, with universal unit `algebraicUniversalUnit`.

- `family E τ` (def): the subgroups `specialUnitaryPoints E τ R` of the values
  `(R ⊗_F B)ˣ` of the unit functor.
- `normCoord E R j : E ⊗_F R → R` (def): the `j`-th coordinate, transported through
  `E ⊗_F R ≅ R ⊗_F E`, of the Library's `IsometryCut.coord` for the zero subspace of `E`.
  `normCoord_map` is its naturality in `R`; `eq_zero_iff_normCoord`: an element vanishes
  exactly when all its coordinates vanish (from `IsometryCut.mem_baseChange_iff` and
  `Submodule.baseChange_bot`).
- `normGenerator E j` (def): the `j`-th coordinate of `relativeNorm(g) - 1` for the
  universal unit `g`.
- `ideal E τ` (def): `IsometryCut.ideal τ ⊥ 1 ⊔ span (range normGenerator)`. The first
  summand is the Library's ideal of coordinates of `g τ(g) - 1` (the isometry defect for the
  zero subspace and `Q = 1`; `defect_one_eq` records `defect τ 1 y = y τ_R(y) - 1`).
- `isCutOutBy`: `Corepresented.IsCutOutBy` holds for `family E τ` and `ideal E τ`. For a unit
  `x` over `R` with classifying map `φ`, the Library's `IsometryCut.isCutOutBy` handles the
  unitary condition. For the norm, `relativeNorm_naturality` gives
  `φ (normGenerator j) = normCoord j (relativeNorm x - 1)`, so `relativeNorm x = 1` exactly
  when `φ` kills the second summand. A map kills a sum of ideals exactly when it kills both.

## The group scheme and its points

- `groupScheme E τ` (abbrev): the Library's `Corepresented.cutGroupScheme (isCutOutBy E τ)`,
  the affine group scheme `Spec (candidateRing ⧸ ideal E τ)` over `Spec F`. The instance
  `IsAffineHom (groupScheme E τ).X.hom` holds because it is a morphism of spectra.
- `pointsEquiv E τ T : (T ⟶ (groupScheme E τ).X) ≃* specialUnitaryPoints E τ Γ(T)` for every
  scheme `T` over `Spec F`, where `Γ(T)` is the relative global-section algebra
  `((algΓ _).obj T).unop` (the Library's `Corepresented.pointsEquiv`), with
  `pointsEquiv_naturality`: restriction along `a : T' ⟶ T` corresponds to
  `specialUnitaryMap E τ` along the global-section map of `a`.
- `affinePointsEquiv E τ R : (groupScheme E τ).affinePoints R ≃* specialUnitaryPoints E τ R`
  for every commutative `F`-algebra `R` (the Library's `Corepresented.affinePointsEquiv`),
  with `affinePointsEquiv_naturality` for `affinePointMap` and `specialUnitaryMap`.
- `Presentation.ofIso E τ φ : Presentation E τ G` (def) for an isomorphism
  `φ : groupScheme E τ ≅ G` of group schemes over `Spec F`: the points equivalence on `R` is
  composition with `φ.inv` followed by `affinePointsEquiv`, and naturality follows from
  `affinePointsEquiv_naturality`. `Presentation` is the published structure of
  `Langlands.GroupScheme.Examples.UnitaryAlgebraPresentation`.

## Provenance

Internal. `SU(B, τ)` is the special unitary group of an algebra with unitary involution of
Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998), §23.A (paragraph
"Unitary involutions", printed p. 346): its points are the units `u` with `u τ(u) = 1` and
reduced norm `1`, as in the Library's `specialUnitaryPoints`. The construction as a closed
subgroup scheme of the unit group scheme specializes the Library's closed-subgroup criterion
`Corepresented.IsCutOutBy` to explicit equations; no further statement is taken from a source.
