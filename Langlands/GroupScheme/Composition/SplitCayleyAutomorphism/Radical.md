# The split Cayley automorphism group scheme is connected reductive

Notation as in `Points.md` and `RadicalAlgebra.md`. For a field `K`, `Aut_K` is the automorphism
group scheme of Zorn's split Cayley algebra over `K`, a closed subgroup scheme of `GL₈`. For a
test scheme `T` over `Spec K`, `pointsEquiv K T` identifies `T`-points of `Aut_K` with
automorphism matrices over `Γ(T, 𝒪_T)`. The unit of Zorn's algebra is
`unit = (1, 0, …, 0, 1)`.

## The quotient representation

- `mulVec_unit_of_mem`: an automorphism matrix fixes the unit.
- `quotHom φ`: an automorphism matrix `g` over `A` acts on the quotient of `A⁸` by the line of the
  unit, with matrix `quotMatrix g` (`RadicalAlgebra.md`). Because `g` fixes the unit,
  `quotMatrix (g h) = quotMatrix g · quotMatrix h` (`quotMatrix_mul`), so this is a group
  homomorphism from the automorphism subgroup into `GL₇(A)`. `quotHom_val` gives its matrix.
- `quotPoints K T`: the induced map from `T`-points of `Aut_K` to `T`-points of `GL₇`, and
  `pointsEquiv_quotPoints` gives its matrix.
- `quotPoints_naturality`: pulling back along `a : T' ⟶ T` commutes with `quotPoints`. Both
  sides change coefficients entrywise, and `quotMatrix` commutes with changing coefficients
  (`quotMatrix_map`).
- `quotRep K`: the seven-dimensional representation `Aut_K ⟶ GL₇`, built from the natural
  family `quotPoints K` by the published `homOfPoints`. `pointsEquiv_quotRep` says the matrix of
  the image of a point `x` is `quotMatrix` of the matrix of `x`.

## Rational points over every test scheme

- `map_mem_automorphismSubgroup`: an automorphism matrix over `K` stays an automorphism matrix
  after changing coefficients along any ring homomorphism `f : K →+* A`. This uses the
  compatibility of the unit and multiplication defects with changing coefficients
  (`CayleyDatum.map_unitDefect`, `CayleyDatum.map_multiplicationDefect` in
  `CayleyAutomorphismGroup.lean`).
- `constantPoint T g`: the `T`-point of `Aut_K` with matrix `g` mapped to `Γ(T, 𝒪_T)`, for an
  automorphism matrix `g` over `K`. `pointsEquiv_constantPoint` gives its matrix.
- `quotMatrix_mulVec_mem_fixedSubmodule`: let `i : H ⟶ Aut_K` have normal range. Then for every
  automorphism matrix `g` over `K`, `quotMatrix g` maps the fixed vectors of the representation
  `i ≫ quotRep K` of `H` to fixed vectors. Fix a point `h` of `H` over `T` and let `G` be the
  quotient matrix of `constantPoint T g` and `M` that of `h`. By normality,
  `(constantPoint T g)⁻¹ · i(h) · constantPoint T g` is `i(h')` for some point `h'`, so
  `G⁻¹ M G` fixes `v`. Hence `M (G v) = G (G⁻¹ M G v) = G v`. This is the argument of the
  published `mulVec_mem_fixedSubmodule` for `GL_n`, applied to the quotient representation.
- `mem_automorphismSubgroup_id_iff`: over `K` itself, membership in the automorphism subgroup is
  `IsAutomorphism` of the matrix.

## The unipotent radical

`hasTrivialUnipotentRadical_of_isAlgClosed k`: if `k` is algebraically closed, then `Aut_k` has
trivial unipotent radical (the published `HasTrivialUnipotentRadical`). Let `i : H ⟶ Aut_k` be
the inclusion of a smooth connected unipotent subgroup with normal range.

1. `H` is unipotent, so the representation `ρ = i ≫ quotRep k` has a nonzero fixed vector
   `v ∈ k⁷`.
2. Let `W ⊆ k⁸` be the preimage of the fixed vectors of `ρ` under the projection
   `projLin k : k⁸ → k⁷`. Since `projLin (g x) = quotMatrix g (projLin x)` for automorphism
   matrices `g` (`quotMatrix_mulVec_projLin`), `W` is stable under every automorphism matrix
   over `k` by the previous section, in particular under all root elements `x_α(r)` and torus
   elements.
3. The lift `sectLin k v` lies in `W` and is not a multiple of the unit, because
   `projLin (sectLin v) = v ≠ 0` and `projLin unit = 0`. By `stableSubspace`
   (`RadicalAlgebra.md`), `W` contains `e₁, …, e₆`, so `projLin eⱼ` is fixed by `ρ` for
   `j = 1, …, 6`.
4. Let `g` be the matrix of the image of a point of `H` over `T`. For `j = 1, …, 6`, the fixed
   vector condition gives `projLin (g eⱼ - eⱼ) = 0`, so `g eⱼ = eⱼ + c · unit` for
   `c = (g eⱼ - eⱼ)₀` (`eq_smul_unit_of_projLin_eq_zero`). By `unitRigidity`
   (`RadicalAlgebra.md`), `g = 1`.
5. Since points of `Aut_k` are determined by their matrices, the range of `i` is the trivial
   subgroup functor.

## Connected reductive

`isConnectedReductive K`: for every field `K`, `Aut_K` is connected reductive (the published
`IsConnectedReductive`):

- smooth: `smooth_automorphismGroup` (`Smooth.md`);
- affine structure morphism: by instance, since `Aut_K` is a closed subgroup of `GL₈`;
- connected: `connectedSpace_automorphismGroup K` (`Connected.md`);
- trivial geometric unipotent radical: the base change of `Aut_K` to the algebraic closure
  `AlgebraicClosure K` is isomorphic to `Aut` of the algebraic closure (`baseChangeModelIso`,
  `BaseChange.md`), which has trivial unipotent radical by the previous section. The published
  `HasTrivialUnipotentRadical.of_iso` transfers this along the isomorphism.

## Provenance

The literature proves reductivity of the automorphism group of an octonion algebra from an
irreducible representation. Springer and Veldkamp, *Octonions, Jordan Algebras and Exceptional
Groups* (Springer, 2000, Chapter 2, https://doi.org/10.1007/978-3-662-12622-6_2), Corollary 2.3.4
(p. 32), distinguish two cases by characteristic:

- If the characteristic is not `2`, the automorphism group acts irreducibly on the
  seven-dimensional space of trace-zero octonions.
- In characteristic `2` the unit has trace `1 + 1 = 0`. For Zorn's algebra the unit is
  `(1, 0, …, 0, 1)`, whose trace is `a + b = 1 + 1`. So the unit spans a proper invariant line
  in the trace-zero space, which is therefore reducible. The source then uses the
  six-dimensional quotient of the trace-zero space by the line of the unit.

The Lean proof uses neither the trace-zero space nor irreducibility. In every characteristic it
uses the seven-dimensional quotient `k⁸ / k · 1` of the whole algebra by the line of the unit
(`quotRep`, with `projLin` and `quotMatrix` from `RadicalAlgebra.md`). Two explicit lemmas of
`RadicalAlgebra.md` replace irreducibility:

- `stableSubspace`: over an algebraically closed field `k`, a subspace of `k⁸` that is stable
  under the root and torus elements and contains a vector off the unit line contains
  `e₁, …, e₆`;
- `unitRigidity`: an automorphism matrix that moves each of `e₁, …, e₆` only by a multiple of the
  unit is the identity.

Step 3 of the previous section applies `stableSubspace` to the preimage `W` of the fixed vectors.
Step 4 applies `unitRigidity` on every test scheme. The structure of the argument follows the
published proofs of trivial unipotent radical for `GL_n`
(`hasTrivialUnipotentRadical_generalLinear`) and for the split symplectic group.
