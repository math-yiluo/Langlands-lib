# The coordinate coalgebra and matrix coefficients of an affine group scheme

Module `Langlands.GroupScheme.Rational.TorusUnipotence.MatrixCoefficients`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

This module connects the pure-algebra module `TopWeight` to group schemes. Let `k` be a field
and `G` a group scheme over `Spec k` whose structure morphism is affine (`IsAffineHom G.X.hom`).
Write `A = CharacterUnits.Coord G` for its chosen coordinate algebra (`Lie.coordinateAlgebra G`).
The module makes `A` a `k`-coalgebra, attaches to every matrix representation `ρ` of `G` its
coefficient matrix in `A`, and reduces `IsUnipotent G` to a statement about these coefficient
matrices. Its last theorem feeds `exists_fixed_vector_of_graded'` from `TopWeight`.

## Points

* `pt G f`: the `B`-point of `G` with coordinates `f : A →ₐ B`, i.e.
  `(Lie.pointCoordinates G).symm f`. `pt_injective` says `f` is determined by `pt G f`.
* `pt_comp`: `pt G (g ∘ f)` is the image of `pt G f` under `Lie.affineMap G g`.
* `pt_comul`: the point classified by `CharacterUnits.comul G : A → A ⊗ A` is the product of the
  points classified by the two inclusions `inclLeft`, `inclRight : A → A ⊗ A`.
* `pt_comp_comul`: if `l : A ⊗ A →ₐ C` restricts to `f` and `g` along the two inclusions, then
  `pt G (l ∘ comul) = pt G f * pt G g`.
* `pt_comp_coordinateOrigin`: an algebra map that factors through the augmentation
  `Lie.coordinateOrigin G : A → k` classifies the identity point.

## The coalgebra structure

* `comul_coassoc`, `comul_rTensor_counit`, `comul_lTensor_counit`: coassociativity of
  `CharacterUnits.comul G` and the two counit laws for `Lie.coordinateOrigin G`. They are stated
  as equalities of algebra maps over `CommRingCat.of k`, with
  `Algebra.TensorProduct.assoc`, `lid` and `rid`.
* `coordComul G : A →ₐ[k] A ⊗[k] A` and `coordCounit G : A →ₐ[k] k` are these two maps read as
  `k`-algebra maps. `coordComul_coassoc`, `coordCounit_rTensor` and `coordCounit_lTensor` restate
  the three laws over `k`.
* `lid_comp_coordCounit`: `lid ∘ (ε ⊗ id) ∘ Δ = id`, and `rid_comp_coordCounit`:
  `rid ∘ (id ⊗ ε) ∘ Δ = id`, as `k`-algebra maps.
* `coordBialgebra G`: the `Bialgebra k A` instance built by `Bialgebra.ofAlgHom` from
  `coordComul` and `coordCounit`. It is an `abbrev` and not a global instance.
* `coordComul_coassoc_linear`, `coordCounit_rTensor_linear`, `coordCounit_lTensor_linear`: the
  three laws as equalities of linear maps, in the form of Mathlib's `Coalgebra` fields
  `coassoc`, `rTensor_counit_comp_comul` and `lTensor_counit_comp_comul`. This is the form that
  `exists_fixed_vector_of_graded'` takes.

## Matrix coefficients

Let `n` be a finite type with decidable equality and `ρ : MatrixRepresentation G n`.

* `coeffMatrix ρ : Matrix n n A`: the matrix of `ρ` at the universal point
  `CharacterUnits.universalPoint G` of `G` with coefficients in `A`.
* `affineMatrix_pt`: the matrix of `ρ` at the point `pt G f` is `coeffMatrix ρ` with `f` applied
  to each entry.
* `comul_coeffMatrix` and `coordComul_coeffMatrix`:
  `Δ (coeffMatrix ρ i j) = ∑ l, coeffMatrix ρ i l ⊗ coeffMatrix ρ l j`, over `CommRingCat.of k`
  and over `k`.
* `coordCounit_coeffMatrix`: `ε (coeffMatrix ρ i j) = (1 : Matrix n n k) i j`.
* `isFixedVector_of_coeffMatrix`: let `v : n → k` satisfy
  `∑ j, v j • coeffMatrix ρ i j = v i • 1` in `A` for every `i`. Then `ρ.IsFixedVector v`.

## Unipotence criteria

* `isUnipotent_of_coord`: suppose every matrix representation `ρ` of `G` on a nonempty finite
  type `n` has some `v : n → k` with `v ≠ 0` and `∑ j, v j • coeffMatrix ρ i j = v i • 1` for every
  `i`. Then `IsUnipotent G`.
* `isUnipotent_of_graded`: let `Γ` be a linearly ordered abelian group and
  `𝒜 : Γ → Submodule k A` an internal direct sum decomposition (`DirectSum.IsInternal 𝒜`).
  Assume:
  * `hΔ`: `coordComul G` maps `𝒜 χ` into `⨆ α, 𝒜 α ⊗ 𝒜 (χ - α)`;
  * `h1`: `1 ∈ 𝒜 0`;
  * `hrigid`: let `a ∈ 𝒜 0`, and suppose `rid ((id ⊗ m) (Δ a)) = 0` for every functional `m` on
    `A` that vanishes on `𝒜 χ` for all `χ ≥ 0`. Then `a = c • 1` for some `c : k`.

  Then `IsUnipotent G`.

## Proof

*Coalgebra laws.* `pt_injective` reduces each law to an equality of points. `pt_comp_comul`
turns each side into a product of points, and the law becomes associativity of
multiplication of points, or the unit law with `pt_comp_coordinateOrigin`. The restriction
hypotheses of `pt_comp_comul` are checked on elements with `simp`. The `k`-versions are the same
terms, since `CommRingCat.of k` has carrier `k`. The algebra-map laws for `lid` and `rid` follow
by rewriting with the counit laws and `ext`. The linear-map laws are the `Coalgebra` fields of
`coordBialgebra`.

*Coefficients.* `affineMatrix_pt` follows from
`CharacterUnits.affinePointMap_universalPoint_eq` and the naturality of `affineMatrix`. For
`comul_coeffMatrix`, apply `affineMatrix_pt` to `comul`, rewrite `pt G comul` with `pt_comul`,
and use multiplicativity of `affineMatrix`. Then apply `affineMatrix_pt` to the two inclusions and
read off entry `(i, j)` of the matrix product. `coordCounit_coeffMatrix` is the same argument with
`pt_comp_coordinateOrigin`: the identity point has the identity matrix.

*Fixed vectors.* Let `T` be a scheme over `Spec k` and `g : T ⟶ G.X`. Then `g` factors as
`a ≫ universalPoint G` with `a = g ≫ (Lie.coordinateIso G).inv`. Let `ψ : A → Γ(T, 𝒪_T)` be the
ring map induced by `a`. By naturality of `pointMatrix` and `pointMatrix_eq_affineMatrix`, the
matrix of `ρ` at `g` is `(coeffMatrix ρ).map ψ`. By `scalarMap_naturality`, `scalarMap T c` is
`ψ (algebraMap k A c)`. So `ρ(g) v` is `ψ` applied to `coeffMatrix ρ *ᵥ (algebraMap ∘ v)`
(`RingHom.map_mulVec`). Its `i`-th entry is `∑ j, v j • coeffMatrix ρ i j = v i • 1`, which `ψ`
maps to `scalarMap T (v i)`. `isUnipotent_of_coord` follows at once.

*Graded criterion.* Apply `isUnipotent_of_coord`. For `ρ`, apply `exists_fixed_vector_of_graded'`
with `Δ = coordComul G`, `ε = coordCounit G` (as linear maps), the three `_linear` laws, the
grouplike element `e = 1` (`Δ 1 = 1 ⊗ 1` and `ε 1 = 1`, since both are algebra maps), and the
matrix `coeffMatrix ρ` with `coordComul_coeffMatrix` and `coordCounit_coeffMatrix`.

## Provenance

These are internal interfaces for the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. The mathematics is
standard: the coordinate ring of an affine group scheme is a Hopf algebra, and a
finite-dimensional representation corresponds to a matrix comodule whose entries are its matrix
coefficients. See J. S. Milne, *Algebraic Groups* (Cambridge, 2017), Chapter 3, sections b–c
(Hopf algebras and algebraic groups, pp. 65–66), and Chapter 4, section a (representations and
comodules, p. 83). In this module, the coalgebra laws are derived from the
group law on points of `G`, not taken from a Hopf algebra structure in the Library.
`isUnipotent_of_graded` packages the hypotheses that the rest of the proof establishes for the
coordinate ring of the group in the target statement.
