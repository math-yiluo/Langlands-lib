# Proof of the Kostant–Rosenlicht closed-orbit theorem

Worker 281 and Worker 1497.

`Langlands.GroupScheme.unipotentAffineOrbitClosed` proves
`Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement.{u}`: over an
algebraically closed field `k : Type u`, for a smooth affine unipotent group
scheme `U`, an affine scheme `X` locally of finite type with an action
`a : SchemeAction U X`, and a rational point `x`, the range of the underlying
map of the orbit morphism `a.act (𝟙 U.X) (toUnit U.X ≫ x)` is closed. This is
the algebraically closed, rational-point case of Milne, *Algebraic Groups*
(2017), Theorem 17.64, printed pp.373–374.

## Route

The Lean proof does not follow Milne's. Milne restricts to the orbit closure,
takes its reduced boundary and uses unipotence to find a nonzero invariant
function in the boundary's ideal. Here the orbit map is turned into an algebra
map `φ : A → B` between coordinate algebras whose image is stable under right
translations. Unipotence, Chevalley's constructibility theorem and the
Jacobson property then show that `Spec B → Spec A` has closed image
(`KostantRosenlicht.range_comap_eq_zeroLocus`, Worker 1497, modules
`KostantRosenlicht.Points`, `KostantRosenlicht.Hopf` and
`KostantRosenlicht.Surjective`). The passage between schemes and algebras is in
`KostantRosenlicht.Geometry`.

## Results

- `KostantRosenlicht.finiteType_of_iso`: if `Y : Over (Spec R)` is locally of
  finite type and `jY : (algSpec R).obj (op A) ≅ Y`, then `A` is of finite type
  over `R`. Proof: the structure morphism of `Spec A` is `jY.hom.left` (an
  isomorphism) followed by `Y.hom`, hence locally of finite type; conclude with
  `HasRingHomProperty.Spec_iff` and `RingHom.finiteType_algebraMap`.
- `unipotentAffineOrbitClosed`. Proof:
  1. `U.X.left` is affine (`isAffine_of_isAffineHom`) and so is `X.left`, so
     `essImage_algSpec` gives `k`-algebras `B`, `A` and isomorphisms
     `j : Spec B ≅ U.X`, `jX : Spec A ≅ X` over `Spec k`.
  2. `A` and `B` are of finite type over `k` by `finiteType_of_iso`; for `U`,
     local finite type comes from smoothness.
  3. `B` is reduced: `U.X.left` is reduced, being smooth over a field
     (`SmoothReducedProof.isReduced_of_smooth_over_field`); this transfers to
     `Spec B` along the isomorphism `j` (`isReduced_of_isOpenImmersion`) and
     then to `B` (`affine_isReduced_iff`).
  4. The group scheme `model U j` built from the corepresentation
     `corepresentableBy U j` is unipotent: `IsUnipotent.of_epi hU` applied to
     the isomorphism `(modelIso U j).inv : U ⟶ model U j`.
  5. By `isClosed_range_orbit` it suffices that the range of
     `PrimeSpectrum.comap (coordMap j a jX x)` is closed. Apply
     `range_comap_eq_zeroLocus` to `φ = coordMap j a jX x`. Its stability
     hypothesis is that for every `k`-point `v` and every `c ∈ A`,
     `charTranslate (corepresentableBy U j) v (φ c)` is of the form `φ c'`.
     Take `c' = leftTranslate a jX (basePoint j v) c`; the equation is
     `coordMap_comp_rightTranslate` evaluated at `c`. The range is then
     `zeroLocus (ker φ)`, which is closed.

No hypothesis of the statement is strengthened. Connectedness of `U` and
reducedness of `X` are not used. Smoothness of `U` is used only for finite
type and reducedness of its coordinate algebra.
