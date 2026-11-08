# Inner discrepancies on finite Galois covers from Galois-pair values

Module `Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy`.

Throughout, `K` and `L` are fields in one universe `u`, `L` is a finite Galois
extension of `K`, and `ringTest K L` is the cover `Spec L → Spec K` as an object of
`Over (Spec K)`. Its double cover is the product
`ringTest K L ⊗ ringTest K L`, the actual fibre product `Spec L ×_K Spec L`.
For a `K`-automorphism `σ` of `L`, the Library's `Cocycle.galoisPair σ` is the map
`Spec L → Spec L ×_K Spec L` with first coordinate the identity and second
coordinate `Spec σ` (`ringTestMap K σ.toAlgHom`).

## Statements

### Assembling maps out of the double cover

- `Cocycle.finiteGaloisComponent_eq_galoisPair i`: the `i`-th actual component
  `Descent.finiteGaloisComponent K L i` of the Library's finite Galois tensor
  decomposition is the underlying scheme map of `galoisPair σᵢ`, where
  `σᵢ = Descent.galoisIndexEquiv K L i`.
- `Cocycle.galoisPair_ext_tensor`: two maps
  `(ringTest K L ⊗ ringTest K L) ⊗ Y ⟶ Z` in `Over (Spec K)` are equal as soon
  as they agree after precomposition with every `lift (s ≫ galoisPair σ) y`, for
  all `σ`, all tests `V`, all `s : V ⟶ ringTest K L` and all `y : V ⟶ Y`.
- `Cocycle.galoisComponentInv` (definition): the inverse of the isomorphism
  `Sigma.desc (Descent.finiteGaloisComponent K L)` from the finite coproduct of
  copies of `Spec L` to the overlap, with the simp lemmas
  `finiteGaloisComponent_comp_galoisComponentInv`,
  `desc_comp_galoisComponentInv` and `galoisComponentInv_comp_desc`.
- `Cocycle.galoisPairDesc x` (definition): for any family
  `x : (L ≃ₐ[K] L) → (ringTest K L ⟶ W)`, the map
  `ringTest K L ⊗ ringTest K L ⟶ W` obtained by applying `galoisComponentInv`
  and then the coproduct map with components `(x σᵢ).left`.
- `Cocycle.galoisPair_comp_galoisPairDesc`: `galoisPair σ ≫ galoisPairDesc x = x σ`
  for every `σ`.

### Discrepancies

Let `G H A` be group schemes over `Spec K`, `e : LocalGroupIso G H (ringTest K L)` a
local isomorphism over the cover, and `a : AutomorphicAction A G`.

- `LocalGroupIso.hasOverlapDiscrepancy_of_galois`: for `δ` a map from the double
  cover to `A.X`, the universal overlap equation `e.HasOverlapDiscrepancy a δ`
  holds provided, for every `σ`, every test `V`, every `s : V ⟶ ringTest K L` and
  every `g : V ⟶ G.X`,
  `e.toFun s (a.act (s ≫ galoisPair σ ≫ δ) g) = e.toFun (s ≫ ringTestMap K σ.toAlgHom) g`.
- `LocalGroupIso.hasInnerDiscrepancy_of_galois`: if a family
  `x : (L ≃ₐ[K] L) → (ringTest K L ⟶ A.X)` satisfies
  `e.toFun s (a.act (s ≫ x σ) g) = e.toFun (s ≫ ringTestMap K σ.toAlgHom) g`
  for all `σ`, `V`, `s` and `g`, then `e.HasInnerDiscrepancy a`, the Library's
  all-test inner-discrepancy property.

Nothing here constructs a Galois cocycle for a particular group, a quasi-split
inner form, or the host existence theorem; this is a supporting unit for the
inner-discrepancy step.

## Proofs

`finiteGaloisComponent_eq_galoisPair` checks both pullback projections, using the
Library equations `finiteGaloisComponent_fst/snd` and `galoisPair_fst/snd`.

`galoisPair_ext_tensor`: the first projection
`f : ((ringTest ⊗ ringTest) ⊗ Y).left ⟶ (ringTest ⊗ ringTest).left` is pulled back
along the finitely many components; because schemes are finitary pre-extensive and
the components give an isomorphism from their coproduct
(`finiteGaloisComponent_isIso_desc`), `FinitaryPreExtensive.isIso_sigmaDesc_fst`
shows that the induced map from the coproduct of the pullbacks is an isomorphism, so
it can be cancelled. On the `i`-th summand the pullback is made into a test `V`,
with `s` its second projection; the inclusion of the summand equals
`lift (s ≫ galoisPair σᵢ) y` with `y` its `Y`-coordinate, so the hypothesis gives
equality there.

`galoisPairDesc` is well defined over `Spec K` after cancelling the epimorphism
`Sigma.desc (finiteGaloisComponent K L)` and checking each component with
`Over.w`. `galoisPair_comp_galoisPairDesc` rewrites `galoisPair σᵢ` as the `i`-th
component, which cancels against `galoisComponentInv` to the coproduct inclusion.

`hasOverlapDiscrepancy_of_galois` applies `galoisPair_ext_tensor` to the two sides of
the universal overlap equation; after naturality of `e.toFun` and `a.act` the
restricted equation is exactly the hypothesis, using `galoisPair_fst/snd`.

`hasInnerDiscrepancy_of_galois` applies the previous theorem to
`δ = galoisPairDesc x` (whose Galois-pair values are `x σ`) and then the Library
theorem `hasInnerDiscrepancy_of_overlap`.

## Provenance

Internal. The decomposition `L ⊗_K L ≅ ∏_σ L` of a finite Galois extension is
standard; the Lean route uses the Library's actual tensor-component isomorphism and
the Library's universal overlap formulation of inner discrepancy.
