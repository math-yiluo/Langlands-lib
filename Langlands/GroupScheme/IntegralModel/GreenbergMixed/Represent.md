# Corepresenting `B ↦ Hom_R(O, ℛ(B))`

This is the Weil-restriction step of Greenberg's construction (Greenberg 1961, §1;
KP §A.4), for an arbitrary Greenberg ring scheme `ℛ` with `d` coordinates.

Fix an `R`-algebra `O` and a surjection `f : R[x_1, …, x_N] → O`. Let
`Poly N = k[x_{m,j}]` (`m < N`, `j < d`) and let `univ m ∈ ℛ(Poly N)` be the point with
coordinates `x_{m,1}, …, x_{m,d}` (the universal `N`-tuple of points).

- `relations`: the polynomials `coord(g(univ)) j - coord(0) j` for `g ∈ ker f` and
  `j < d`. (`coord(0)` is subtracted because the coordinates of `0` need not vanish.)
- `repAlg = Poly N ⧸ (relations)`, a `k`-algebra.
- `pointsOf φ m = ℛ(φ)(univ m)` for a `k`-algebra map `φ : Poly N → S`. Its coordinates
  are `φ(x_{m,j})` (`coord_pointsOf`), and `g(pointsOf φ) = ℛ(φ)(g(univ))`
  (`aeval_pointsOf`).
- `aeval_pointsOf_eq_zero_iff`, `repIdeal_le_ker_iff`: `φ` kills the relations iff
  `g(pointsOf φ) = 0` for all `g ∈ ker f`.
- `classify ψ : O →ₐ[R] ℛ(S)` for `ψ : repAlg ⟶ S`: descend `g ↦ g(pointsOf (ψ ∘ mk))`
  along `f` (`AlgHom.liftOfSurjective`). It is natural (`classify_comp`, from functoriality
  of `ℛ`). It is injective, because `ψ(x_{m,j})` is the `j`-th coordinate of
  `classify ψ (f x_m)`. It is surjective: for `q : O → ℛ(S)`, the map
  `x_{m,j} ↦ coord(q(f x_m)) j` kills the relations.
- `repEquiv`: the resulting natural bijection `(repAlg ⟶ S) ≃ (O ⟶ ℛ(S))`.
- `corepresentableBy`: if a functor `G` on `R`-algebras is corepresented by `O`, then
  `ℛ ⋙ G` is corepresented by `repAlg`.
- `finitePresentation_repAlg`: `repAlg` is of finite presentation over `k`. It is a quotient
  of a polynomial ring in finitely many variables, and `k` is noetherian.
- `formallySmooth_repAlg`: if `O` is formally smooth over `R`, then `repAlg` is formally
  smooth over `k`. A map `repAlg → C ⧸ I` with `I² = 0` classifies `q : O → ℛ(C ⧸ I)`.
  The map `ℛ(C) → ℛ(C ⧸ I)` is surjective with nilpotent kernel (`map_surjective`,
  `ker_map_nilpotent`), so `q` lifts to `O → ℛ(C)` by
  `Algebra.FormallySmooth.liftOfSurjective`. The lift classifies a map `repAlg → C`, which
  lifts the given map by naturality and injectivity of `classify`.
