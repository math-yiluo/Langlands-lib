# Proof: closed subgroups of diagonalizable groups are diagonalizable

`Langlands.GroupScheme.Diagonalizable.closedSubgroupPresentation` proves
`Langlands.GroupScheme.Diagonalizable.ClosedSubgroupPresentationStatement.{u}`
from `Langlands.GroupScheme.Torus.ClosedSubgroupPresentationStatement`, at
arbitrary universe `u`. For every field `k : Type u`, every finitely generated
abelian group `Λ : Type u` and every closed subgroup
`i : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`, it produces a
finitely generated abelian group `Λ' : Type u` and an isomorphism of group
schemes over `Spec k` between `H` and `D(Λ')`. The proof assumes nothing more
about `H`: torsion character groups and finite nonreduced subgroups such as
`μ_p ⊆ 𝔾_m` are covered.

## Source

J. S. Milne, *Algebraic Groups* (corrected reprint 2022), registered as
`milne-2022-algebraic-groups`: Theorems 12.8 and 12.9(c), printed pp.233–234
(zero-based PDF indices 243–244), and Proposition 4.23 (printed p.93). Milne's
proof of 12.9(c): the coordinate map `O(D(Λ)) → O(H)` is a surjective Hopf
map, so the images of the group-like elements of `O(D(Λ))` are group-like and
span `O(H)`. The Lean proof follows this route and makes the finite generation
of the character group explicit.

## Auxiliary results

- `surjective_of_isClosedSubgroup_hopfSpec`: over any commutative ring `R`, if
  `φ : A ⟶ B` is a map of commutative Hopf algebras and the induced morphism
  `(hopfSpec R).map φ.op` of relative Hopf spectra is a closed subgroup, then
  `φ` is surjective. The underlying scheme morphism is `Spec.map` of the
  algebra map. A closed immersion of affine schemes is surjective on global
  sections (`IsClosedImmersion.isAffine_surjective_of_isAffine`), and the
  `Scheme.ΓSpecIso` naturality square transfers this to the algebra map.
- `groupLike_mem_of_span_eq_top`: in a coalgebra `C` over a field `k`, if a set
  `T` of group-like elements spans `C`, then every group-like element of `C`
  lies in `T`. Otherwise `insert g T` is still a set of group-like elements, so
  it is linearly independent (Mathlib's `linearIndepOn_isGroupLikeElem`, which
  is Milne's Proposition 4.23). Then `g` is not in the span of `T`,
  contradicting `span k T = ⊤`.

## The main proof

1. **Affineness.** `D(Λ)` is affine over `Spec k`, and the closed immersion `i`
   is an affine morphism, so the underlying scheme of `H` is affine. This lets
   the proof use the actual coordinate Hopf algebra
   `B := AffineCoordinates.hopfAlgebra H` and the comparison
   `e₂ := AffineCoordinates.hopfSpecIso H` of `H` with its Hopf spectrum. On
   the ambient side, `e₁ := Diagonalizable.hopfSpecIso R Λ` compares `D(Λ)`
   with the Hopf spectrum of `AddMonoidAlgebra k Λ`.
2. **Coordinate map.** The composite `e₂.hom ≫ i ≫ e₁.inv` is a morphism of
   Hopf spectra. Full faithfulness of `hopfSpec` gives a Hopf map
   `φ : k[Λ] ⟶ B` whose spectrum is this composite. Composing a closed subgroup
   with isomorphisms on either side keeps it closed
   (`IsClosedSubgroup.iso_comp`, `IsClosedSubgroup.comp_iso`), so
   `surjective_of_isClosedSubgroup_hopfSpec` makes `φ` surjective.
3. **Spanning.** The group-like elements of `k[Λ]` span it
   (`AddMonoidAlgebra.span_isGroupLikeElem`). Their images `T` under the
   surjection `φ` are group-like and span `B`. In particular the group-like
   elements of `B` span `B`.
4. **Finite generation.** The map `ψ : Λ →+ Additive (GroupLike k B)`,
   `l ↦ φ (single l 1)`, is additive because `single a 1 * single b 1 =
   single (a + b) 1`. It is surjective: by `groupLike_mem_of_span_eq_top`,
   every group-like element of `B` lies in `T`. It is therefore `φ a` for a
   group-like `a ∈ k[Λ]`, and `a = single l 1` for some `l`
   (`AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`). Hence
   `Λ' := Additive (GroupLike k B)` is a quotient of `Λ`, so it is finitely
   generated (`AddGroup.fg_of_surjective`) and lies in `Type u`.
5. **Presentation.** Since the group-like elements span `B`,
   `Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` identifies `B` with the
   group algebra of `GroupLike k B`. `MonoidAlgebra.toAdditiveBialgEquiv` turns
   that into `AddMonoidAlgebra k Λ'`. `AffineCoordinates.isoOfBialgEquiv`
   converts this bialgebra equivalence into an isomorphism of group schemes
   between `H` and the Hopf spectrum of `k[Λ']`. Composing with
   `Diagonalizable.hopfSpecIso R Λ'` gives `H ≅ D(Λ')`. This step follows the
   same pattern as `AffineCoordinates.splitIsoOfGroupLikeSpan`.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Scope

The isomorphism is only asserted to exist, as the statement requires. The
proof constructs `Λ'` as the character group `GroupLike k B` of `H`, but it
does not prove any compatibility between the isomorphism and `i`, nor that
`D(Λ') ≅ H ⟶ D(Λ)` is induced by `ψ`.
