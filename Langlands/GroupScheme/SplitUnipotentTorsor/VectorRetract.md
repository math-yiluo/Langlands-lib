# Affine cocycles and torsors under retracts of finite vector groups

Worker 645.

This is an internal, derived helper for the affine vanishing argument in relative
Levi existence. It imports the published additive cocycle and group-valued torsor
constructions and does not change their declarations.

`IsFiniteVectorGroupRetract V` supplies an actual group scheme `W`, an integer
`n`, group-scheme homomorphisms `j : V ⟶ W` and `p : W ⟶ V`, the published
`RelativeRoot.IsVectorGroupOfDimension W n`, and the equation `j ≫ p = 𝟙 V`.
It imposes this equation on actual homomorphisms, hence on all scheme tests. It is
a sufficient retraction witness for vanishing, not a definition or a
characterization of the additive group of a vector bundle. In particular, the
module does not construct linear transition data or produce retractions from
finite projective modules.

`Cocycle.IsTrivial.of_map_retract` sends a coboundary for the image cocycle under
`j` back along `p`. The retraction equation identifies the resulting cocycle
with the original one.

`Cocycle.isTrivial_of_isVectorGroupOfDimension` works for every finite dimension
`n`, including zero. It uses the published natural coordinates of the vector
group after base change. For each coordinate it applies
`AffineAdditiveCocycle.AddCocycle.exists_coboundary`, then assembles the
primitives into one vector-group point. The hypotheses are an arbitrary base
scheme `B`, an affine test `T` over `B`, and an affine flat surjective cover of
`T`. No field hypothesis occurs.

`Cocycle.isTrivial_of_isFiniteVectorGroupRetract` applies the preceding two
results after base changing the actual retraction maps to `T`.

`exists_section_of_isFiniteVectorGroupRetract` treats an actual torsor with
`ModObj`, invertible `ModObj.leftSMul`, and flat, surjective, quasi-compact
structure map over an affine test `T`. Quasi-compactness supplies an affine flat
surjective cover of its total space. Its composite cover of `T` is an effective
epimorphism. The resulting torsor cocycle is trivial by the retraction result,
and the published `exists_section_of_isTrivial` descends its adjusted point to a
section. The total space need not be assumed affine.

All schemes and group schemes are in the same arbitrary universe `u`.

The provenance is internal: these are formal consequences of the published
`SplitUnipotentTorsor.VectorCocycle`, `AffineAdditiveCocycle`, and `TorsorCocycle`
modules. They extend the implemented rank-one coordinate proof to finitely many
coordinates and transport vanishing along a supplied retraction. They do not
prove relative Levi existence, radical filtration, or vanishing for a general
vector bundle without a retraction witness.
