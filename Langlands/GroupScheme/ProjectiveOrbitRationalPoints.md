# Homogeneous coordinates of rational points of projective orbits

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. Let `k` be a field, `G` a
group scheme over `Spec k`, and `ρ` a matrix representation of `G` on `k^(n+1)`. The
module computes the homogeneous coordinates of the rational points of the orbit of the
coordinate line `e_j` in `ProjectiveSpace k n`. It then proves the closed-orbit step:
when the orbit map factors through a proper quotient of `G`, a nonzero vector that
satisfies every homogeneous equation of the orbit vectors spans an orbit line.

Everything is in the namespace `Langlands.GroupScheme.ProjectiveOrbit`. Points use the
relative projective space `RelativeProjectiveSpace (Spec k) n`, the target of `orbitMap`.
They are compared with `ProjectiveSpace k n` through the isomorphism
`RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec k))`.

## Definition

- `fieldToGlobal k`: the ring map `k → Γ(Spec k, ⊤)` given by the inverse of
  `Scheme.ΓSpecIso`. It is an abbreviation, used as the coefficient map when rational
  points are written with `Proj.fromOfGlobalSections`.

## Results

- `toSpecΓ_fieldToGlobal`: `toSpecΓ ≫ Spec.map (fieldToGlobal k)` is the identity of
  `Spec k`.
- `matrixAction_toPolynomial`: over `Spec k`, the action `matrixAction n M` of an
  invertible matrix with entries in `Γ(Spec k, ⊤)` corresponds, under `toPolynomial`, to
  `ProjectiveSpace.linearAction k n` of the same matrix with entries moved to `k`. The
  proof writes `matrixAction` as a relative linear action and changes its coefficients
  with `RelativeProjectiveSpace.linearAction_coefficientMap`.
- `basisVector_ne_zero`: the basis vector `Pi.single j 1` is nonzero.
- `basisSection_toPolynomial_eq_fromOfGlobalSections`: the coordinate section `e_j`
  over `Spec k`, moved to `ProjectiveSpace k n`, is the rational point
  `Proj.fromOfGlobalSections` of `fieldToGlobal k ∘ eval (Pi.single j 1)`.
- `pullbackPoint_id`: pulling a section back along the identity of the base gives the
  same section.
- `hasCoordinates_orbitMap`: for a rational point `g` of `G`, the image of `g` under the
  orbit map of `e_j`, moved to `ProjectiveSpace k n`, has homogeneous coordinates
  `ρ(g) e_j`, where `ρ(g)` is `ρ.rationalMatrix g`. The proof writes that point as the
  rational point with coordinates `e_j` followed by `linearAction (ρ(g))`, using the three
  lemmas above. It then applies `hasCoordinates_fromOfGlobalSections` and
  `HasCoordinates.linearAction` from
  `Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointZeros`.
- The imported `Langlands.GroupScheme.exists_rationalPoint_lift_of_mem_range`: let `f : X ⟶ Y` be locally of finite type and `K` an
  algebraically closed field. If the closed point of a `K`-point `x : Spec K ⟶ Y` lies in
  the range of `f`, then `x` lifts through `f`. The pullback of `f` along `x` is nonempty,
  and it is locally of finite type over `Spec K`, so it is a Jacobson space and has a
  closed point. That closed point is a `K`-point because `K` is algebraically closed
  (`pointOfClosedPoint`).
- `fromOfGlobalSections_toSpec`: for `c ≠ 0`, the rational point with coordinates `c`,
  followed by the structure map `projectiveSpaceToSpec k n`, is the identity of `Spec k`.
  The proof uses `Proj.fromOfGlobalSections_toSpecZero` and `eval c (C r) = r`.
- `exists_eq_smul_orbit_of_isProper` (rational points in the closure of a projective
  orbit). The hypotheses are:
  - `k` is algebraically closed and `G` is locally of finite type over `Spec k`.
  - `q : G ⟶ Q` is a morphism over `Spec k` whose underlying morphism is flat,
    surjective, and quasi-compact, and `Q` is proper over `Spec k`.
  - `hq`: for all `T`-points `g, h` of `G` with `g ≫ q = h ≫ q`, there is a unit `a` of
    `Γ(T, ⊤)` with `ρ(g⁻¹h) e_j = a • e_j`.
  - `c` is a nonzero vector in `k^(n+1)`. Every homogeneous polynomial that vanishes at
    the orbit vectors `ρ(g) e_j` of all rational points `g` also vanishes at `c`.

  The conclusion is that there are a rational point `g` and a nonzero `a` in `k` with
  `c = a • ρ(g) e_j`.

  Proof. By `hq` and `orbitMap_fibers`, the orbit map of `e_j` takes equal values on
  points with the same image in `Q`. So it factors through `q` by
  `HomogeneousQuotientComparison.desc`, which uses that `q` is flat, surjective, and
  quasi-compact. Let `F : Q ⟶ ProjectiveSpace k n` be the factored map followed by
  `toPolynomial`. Then `F` lies over `Spec k`. Since `Q` is proper over `Spec k`, `F` is
  proper, so its range is closed. By `hasCoordinates_orbitMap`, each orbit vector
  `ρ(g) e_j` is a coordinate vector of a point in this range. `mem_of_isClosed` then shows
  that the rational point with coordinates `c` lies in the range. Since `q` is surjective,
  this point lies in the range of `q ≫ F`. That map is locally of finite type, because
  `G` is locally of finite type over `Spec k`. So `exists_rationalPoint_lift_of_mem_range` lifts
  the rational point to a `k`-point `g₀` of `G`. `g₀` lies over `Spec k` by
  `fromOfGlobalSections_toSpec`, so it is a rational point `g`. The image of `g` has the
  coordinates `ρ(g) e_j` by `hasCoordinates_orbitMap` and also the coordinates `c`. By
  `HasCoordinates.exists_eq_smul`, the two vectors differ by a nonzero scalar.

## Provenance

These are internal helper definitions and lemmas for the proof of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. They follow the
closed-orbit step in the proof of Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 17.65 (printed pp. 374-375, zero-based PDF pages
389-390). There, the points of the orbit `G · [v]` in `P(V)` are the lines `[ρ(g) v]`.
The orbit is closed because `G/B` is complete, so a point in its closure is again of the
form `[ρ(g) v]`. Here closedness comes from properness of `Q` and the factorization of the
orbit map through `q`. The closure condition is stated with homogeneous equations, and the
rational point in the closure is lifted to a rational point of `G`. The lifting step reuses
`Langlands.GroupScheme.exists_rationalPoint_lift_of_mem_range` from
`SchemeActionRationalOrbit`. It requires only the chosen point to lie in
the range of the locally finite type morphism.
