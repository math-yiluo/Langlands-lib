# Unipotent corepresented group schemes and their coordinate bialgebras

Worker 1395 wrote this module. It connects the Library's `IsUnipotent` (every nonzero
finite-dimensional matrix representation has a nonzero fixed vector) with the internal
coordinate predicate `OneMemStable` from `Langlands.GroupScheme.Unipotent.HopfFixed`. It does so
for a group scheme `Corepresented.groupScheme F e` over a field `k`, where
`F : CommAlgCat k ⥤ GrpCat` is corepresented by `B` via `e`. The coordinate bialgebra is the
Library's `AffineLinearEmbedding.bialgebra e`. The two directions together are the
coordinate-ring form of Milne, *Algebraic Groups* (2017), Proposition 14.3 / Theorem 14.5 for
this definition of unipotence. They are proved directly from the Library definitions, not by
citation, and need no finite-type hypothesis.

## `oneMemStable_of_isUnipotent`

If `Corepresented.groupScheme F e` is unipotent, then `OneMemStable k B` holds for the coordinate
bialgebra. Let `V ⊆ B` be a nonzero finite-dimensional right-translation stable subspace with a
basis `b`. The Library's `Chevalley.regularRepresentation e hR V b hV` is a matrix representation
of dimension `finrank V`. Unipotence gives a nonzero fixed vector `v`. Evaluate the fixed-vector
equation at the universal point `𝟙 : Spec B ⟶ G`. Its matrix is the Library's `subspaceMatrix V b`
moved along the injective section comparison `Corepresented.affineSectionsIso B`; the helper
`homEquiv_symm_pointsEquiv_affine` identifies the coordinates of an affine point. This gives
`∑ⱼ vⱼ • subspaceMatrix i j = vᵢ • 1` for each row `i`. With `comul_basis` it follows that
`y = ∑ⱼ vⱼ • bⱼ` satisfies `comul y = y ⊗ 1`, so `y` is right-translation invariant. Then
`y = c • 1` by `eq_counit_smul_one_of_invariant`, where `c ≠ 0` because the `bⱼ` are linearly
independent and `v ≠ 0`. Therefore `1 = c⁻¹ • y ∈ V`.

## `isUnipotent_of_oneMemStable`

Conversely, suppose `OneMemStable k B` holds and `ρ` is a matrix representation indexed by a
nonempty finite type `n`. Some notation:

* `classifiedPoint e f` is the point `Spec S ⟶ G` classified by an algebra map `f : B ⟶ S`.
* `universalMatrix e ρ` is the matrix `N` of `ρ` at the universal point, with entries in `B`.

`affineMatrix_classifiedPoint` (naturality of `affineMatrix`) shows that `ρ` at
`classifiedPoint e f` is `N.map f`. Apply this to the three maps `comul`, `includeLeft` and
`includeRight : B → B ⊗ B`, which classify the product of the two projection points (the Library's
`pt_comul`). Multiplicativity of `ρ` then gives `comul_universalMatrix`:
`comul (N i j) = ∑ₗ N i l ⊗ N l j`. Similarly, `counit_universalMatrix` gives `ε (N i j) = δᵢⱼ`.

On `kⁿ`, let `T g = (N.map g).mulVec`, and let `π i v = ∑ⱼ vⱼ • N i j`. Then
`π i ∘ T g = rightAct g ∘ π i`, and the counit shows that the `π i` are jointly injective.
`exists_invariant` applied to `⊤ ⊆ kⁿ` gives a nonzero `w` with `T g w = g 1 • w` for every
functional `g`. Separating by functionals gives `∑ⱼ wⱼ • N i j = wᵢ • 1`. Finally, at an arbitrary
point `g : T' ⟶ G`, the matrix of `ρ` is `N` mapped along the ring map `B → Γ(T', ⊤)` of `g`
(`pointMatrix_naturality`, `pointMatrix_eq_affineMatrix`). So the row identity, mapped along this
ring map, is exactly the fixed-vector equation for `w`.
