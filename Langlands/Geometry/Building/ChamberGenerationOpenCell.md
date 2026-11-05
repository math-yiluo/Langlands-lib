# Chamber generation from opposite cells over the local field

This internal assembly uses the proved local-field rational-density theorem
and the proved opposite open cell. It requires neither the global rational
Bruhat proposition nor the global ordered-root-product proposition. All fields
and groups use their actual Library constructions at arbitrary universe `u`.

`exists_cell_points_mul_eq_of_dense` concerns any group scheme over a field
whose underlying scheme is irreducible and whose rational points are Zariski
dense. For an open immersion `f : X → G` with a rational point in its source,
and any `g ∈ G(k)`, the intersection of the open image of `f` with its inverse
image under right translation by `g` is nonempty. Density supplies a rational
point in this intersection. Since `Spec k` has one underlying point, its
entire image, and that of its translate, lie in the image of `f`. The universal
property of the open immersion lifts both to rational points `x,y` of `X`,
with `(x f) g = y f`.

`subgroup_le_sup_normalizer_inf_of_localField` assumes a connected reductive
group over an actual nonarchimedean local field, a maximal split torus, and a
generic cocharacter. For any two subgroups `R` and `B` containing the complete
dynamic radicals of the torus cocharacters, it proves
`R ≤ B ⊔ (N(F) ∩ R)`.

Smoothness and connectedness imply irreducibility through the published
`CharacterLatticeProof.isIntegral_of_smooth`. The published
`hasDenseRationalPoints_of_localField` supplies density. Apply the preceding
lemma to the actual opposite cell `U(-ν) × P(ν) → G`. The dynamic Levi
decomposition writes its two points as `a z b` and `c z' d`, with `a,c` in
`U(-ν)`, `b,d` in `U(ν)`, and `z,z'` in the generic dynamic centralizer.
The proved generic-centralizer theorem identifies this with the whole-torus
centralizer.

For `g = (a z b)⁻¹ (c z' d)`, regroup as

`g = b⁻¹ · (z⁻¹ (a⁻¹ c) z) · (z⁻¹ z') · d`.

The second factor lies in `U(-ν)` because the torus centralizer normalizes
that radical. The first, second, and fourth factors therefore lie in both
`R` and `B`. The third factor lies in the torus normalizer; because `g ∈ R`,
it also lies in `R`. This proves the stated join inclusion without assuming
normality of `R` or `B`.

`ParahoricBuildingData.zeroSubgroup_le_chamber_sup_of_dynamicRadicals`
specializes to `R = P.zeroSubgroup` and
`B = P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup)`. Under the
unchanged apartment axioms, the published parahoric inclusion puts `B` inside
`R`. The remaining premise places every complete dynamic radical in `B`;
it then lies in `R` as well. The extra normalizer join is absorbed into `B`.
The local assembly works for every subset `C`; the separate radical-containment
proof is where the chamber condition is used.

The provenance is internal. This is a deduction from the Library's proved
density, opposite-cell, generic-centralizer, and dynamic Levi results. It
introduces no external source assertion. The radical-containment premise
remains explicit, so this module alone does not prove the unconditional
`ChamberParahoricGenerationStatement`.
