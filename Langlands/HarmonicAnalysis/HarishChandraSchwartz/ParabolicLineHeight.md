# Heights on opposite unipotent points bounded by a Chevalley line for the parabolic

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineHeight`.
All declarations are in the namespace `Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. The module `OppositeUnipotentHeight` proves
`exists_rationalMatrixNorm_le_of_weightVector` under two hypotheses on the vector `v`: it is an
eigenvector of every `ρ(χ(t))`, and only the identity of `Ū(F)` fixes it. This module supplies
both hypotheses for a vector constructed from the group. It takes a Chevalley line whose
stabilizer is exactly the dynamic parabolic `P(χ)`. This is the injectivity input (4) used
for the height comparison II.2 (6) in J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra* (2003), printed pp. 253–254 (PDF pp. 19–20).
Waldspurger works with a vector whose orbit map on the opposite unipotent radical is injective;
the route here instead uses the following two facts:

- the exact line stabilizer of a closed subgroup (public `Chevalley.exists_line_stabilizer`),
  applied to the closed subgroup representing `P(χ)` (public
  `Dynamic.Affine.parabolicHom`);
- the intersection `P(χ) ∩ U(χ⁻¹) = 1` at the level of points (public
  `Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`).

No Lie-algebra argument and no hypothesis on the characteristic is used.

## Setting and notation

- `k` is a field and `G` a group scheme over `Spec k`. The existence results assume that the
  structure morphism of `G` is affine and locally of finite type
  (`[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`).
- `rationalPoints G` is the group `G(k)` of points `Spec k ⟶ G` over `Spec k`. For a subgroup
  functor `P`, `P.rationalPoints` is the corresponding subgroup of `G(k)`.
- `ρ.rationalMatrix x` is the matrix in `GL_n(k)` of the rational point `x` in the matrix
  representation `ρ`. `e j` is the basis vector `Pi.single j 1`.
- `χ : 𝔾_m ⟶ G` is a cocharacter. `Dynamic.parabolic χ` is the dynamic parabolic `P(χ)`
  (points `g` such that `t ↦ χ(t) g χ(t)⁻¹` extends to `𝔸¹`).
  `Dynamic.oppositeCocharacter χ` is `t ↦ χ(t⁻¹)`, and
  `Dynamic.unipotent (Dynamic.oppositeCocharacter χ)` is the opposite unipotent subgroup
  `Ū = U(χ⁻¹)`.
- `gmRationalPoint t` is the rational point of `𝔾_m` given by `t : kˣ`, so that
  `gmRationalPoint t ≫ χ.hom.hom` is the point `χ(t)` of `G`.
- In the local-field part, `F` carries `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`. `rationalVectorNorm F` is the sup norm of vectors for the
  residue-normalized absolute value. `rationalMatrixNorm F ρ₀ x` is the largest absolute value of
  an entry of `ρ₀(x)` or of `ρ₀(x)⁻¹`.

## Declarations

### Line stabilizers

- `exists_mulVec_single_eq_smul_map_iff`: for a ring isomorphism `φ : A ≃+* B`, a square matrix
  `M` over `A` and an index `j`, there is a unit `u` of `B` with
  `M.map φ *ᵥ e j = u • e j` exactly when there is a unit `u` of `A` with
  `M *ᵥ e j = u • e j`.
- `IsRationalLineStabilizer ρ j S` (definition, a proposition). Here `ρ` is a representation of
  `G` on a finite type `n`, `j : n`, and `S` is a subgroup of `G(k)`. It states: for every
  `x : G(k)`, `x ∈ S` exactly when there is `u : kˣ` with
  `ρ.rationalMatrix x *ᵥ e j = u • e j`. In words, `S` is the stabilizer in `G(k)` of the line
  `k · e j`.
- `IsRationalLineStabilizer.exists_unit_of_mem`: every `x ∈ S` satisfies
  `ρ(x) e j = u • e j` for some `u : kˣ`.
- `IsRationalLineStabilizer.mem_of_mulVec_eq`: if `ρ(x) e j = e j`, then `x ∈ S`.
- `exists_rationalMatrix_line_stabilizer`: let `i : H ⟶ G` be a closed subgroup
  (`IsClosedSubgroup i`), with `G` affine and locally of finite type over `k`. Then there are
  `n : ℕ`, `j : Fin (n + 1)` and a representation `ρ` of `G` on `Fin (n + 1)` with
  `IsRationalLineStabilizer ρ j (SubgroupFunctor.range i).rationalPoints`.

### The dynamic parabolic

- `gmRationalPoint_comp_mem_parabolic`: for every `t : kˣ`, the point `χ(t)` lies in
  `P(χ)(k)`.
- `exists_parabolic_line`: for a cocharacter `χ` of `G`, affine and locally of finite type over
  `k`, there are `n`, `j : Fin (n + 1)` and `ρ` on `Fin (n + 1)` with
  `IsRationalLineStabilizer ρ j (Dynamic.parabolic χ).rationalPoints`.

### Local fields

`exists_parabolic_line_rationalMatrixNorm_le` (main theorem). Let `G` be affine and locally of
finite type over `F`, `χ` a cocharacter of `G`, and `ρ₀` a closed representation
(`IsClosedSubgroup ρ₀`) on `Fin N` with `N` positive. Then there are `n`, `j : Fin (n + 1)` and
a representation `ρ` on `Fin (n + 1)` such that:

- `IsRationalLineStabilizer ρ j (Dynamic.parabolic χ).rationalPoints`, and
- there are `C > 0` and `D : ℕ` with
  `rationalMatrixNorm F ρ₀ x ≤ C * max 1 (rationalVectorNorm F (ρ.rationalMatrix x *ᵥ e j)) ^ D`
  for every `x ∈ Ū(F)`.

## Proofs as implemented

**Transport along a ring isomorphism.** For a unit `u` of `A`, write `φ(u)` for its image unit
in `B`. Coordinatewise, `M.map φ *ᵥ e j = φ ∘ (M *ᵥ e j)` and
`φ(u) • e j = φ ∘ (u • e j)`. Since `φ` is injective, so is composition with `φ`. Hence
`M.map φ *ᵥ e j = φ(u) • e j` exactly when `M *ᵥ e j = u • e j`. This gives the backward
direction directly. For the forward direction, a unit `v` of `B` is `φ(φ⁻¹(v))`, checked by
extensionality of units.

**Line-stabilizer lemmas.** `exists_unit_of_mem` is the forward direction of the definition,
and `mem_of_mulVec_eq` is the backward direction with `u = 1`.

**Rational line stabilizers.** `Chevalley.exists_line_stabilizer` gives `n`, `j` and `ρ` such
that, for every test scheme `T` over `Spec k`, a point `x : T ⟶ G` lies in the range of `i`
exactly when `ρ(x) e j = u • e j` for a unit `u` of `Γ(T, 𝒪)`. Specialize to `T = Spec k` with
the identity structure map. `ρ.rationalMatrix x` is the matrix over `Γ(Spec k, 𝒪)` mapped along
`Γ(Spec k, 𝒪) ≅ k` (`Scheme.ΓSpecIso`). The transport lemma above, for this ring isomorphism,
converts the condition into the one in `IsRationalLineStabilizer`.

**Cocharacter points in the parabolic.** By `Dynamic.range_comp_le_centralizer_comp` (with
identity maps), the range of `χ` lies in the centralizer of `χ`. By
`Dynamic.centralizer_le_parabolic`, the centralizer lies in `P(χ)`. The point `χ(t)` is in the
range of `χ`, as the image of `gmRationalPoint t`.

**Parabolic line.** `G.X.left` is affine, since `G.X.hom` is an affine morphism to an affine
scheme. `Dynamic.Affine.parabolicHom χ` is a closed subgroup
(`Dynamic.Affine.isClosedSubgroup_parabolicHom`), so `exists_rationalMatrix_line_stabilizer`
applies to it. Its range is `Dynamic.parabolic χ`, because `parabolicHom χ` represents that
subgroup functor (`Dynamic.Affine.isRepresentedBy_parabolicHom`).

**Main theorem.** Take `n`, `j` and `ρ` from `exists_parabolic_line`. The two hypotheses of
`exists_rationalMatrixNorm_le_of_weightVector` (`OppositeUnipotentHeight`) for `v = e j`:

1. `IsCocharacterEigenvector χ ρ (e j)`: for `t : Fˣ` the point `χ(t)` lies in `P(χ)(F)`
   (`gmRationalPoint_comp_mem_parabolic`). By `exists_unit_of_mem`,
   `ρ(χ(t)) e j = u • e j` for a unit `u`.
2. Trivial stabilizer in `Ū(F)`: if `x ∈ Ū(F)` and `ρ(x) e j = e j`, then `x ∈ P(χ)(F)` by
   `mem_of_mulVec_eq`. `Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic` then gives
   `x = 1`.

That theorem then yields `C > 0` and `D` with the stated bound.

## Scope

The representation `ρ` and the index `j` are chosen by the existence theorem and are not
explicit. The constants `C` and `D` come from `exists_rationalMatrixNorm_le_of_weightVector`.
The result is the inverse polynomial bound on heights in Waldspurger II.2. It does not give the
comparison of `‖ρ(x) e j‖` with the modulus character of `P`, the two-sided logarithmic
estimate (6), or anything about Haar measures. It does not prove the host conditional
intertwining theorem.
