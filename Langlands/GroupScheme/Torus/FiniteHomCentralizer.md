# Torus centralizer containment under a finite surjection

This is a derived construction over every field `k : Type u`. It uses the
published all-test centralizer, finite-map cancellation, rational-point lifting,
closed-containment detection, and schematic factor-descent APIs. It is an
intermediate transport result for Cartan generation; it does not establish
Cartan generation or construct a finite isogeny or a torus lift.

The entry `torusCentralizerImageFactor` has the following data. A finite
surjective group-scheme homomorphism `q : G → H` fits in a commuting square
`t ≫ q = f ≫ s`, where `t : T → G`, `s : S → H`, and `f : T → S` are group
homomorphisms, `T` is an actual torus, and `S` is a commutative group scheme.
Maps `c : C → G` and `c' : C' → H` represent the full torus centralizers of
`t` and `s`. The target centralizer `C'` is smooth over `k`. For any closed
subgroup `d : D → H` containing the all-test range of `c ≫ q`, the entry
constructs a group homomorphism `C' → D`. Its companion
`torusCentralizerImageFactor_comp` proves that composing it with `d` gives
`c'`. The construction uses the representing-subgroup factorization API;
monicity of the closed inclusion makes this factor unique.

Neither `G` nor `H` is required to be smooth, connected, or affine here.
No separability or surjectivity hypothesis is imposed on `f`, and `S` is
not required to be a torus. Smoothness of `C'` is an explicit assumption.
The closed competitor `D` may be nonsmooth and nonreduced. All range
containments refer to morphisms from every test scheme, including
nonreduced test schemes.

The proof is implemented in three steps. First,
`mem_torusCentralizer_of_finiteHom` treats a base-field point `g` of `G`.
If `q(g)` centralizes `t ≫ q`, its inner automorphism fixes this composite.
Naturality of inner automorphisms and `finiteHom_cancel` show that the
inner automorphism of `g` fixes `t`. The source of the cancelled maps is
the torus, which is smooth, connected, and affine by the published torus
geometry and affineness-descent results. This argument does not cancel
`q` on arbitrary test-scheme points.

Second, over an algebraically closed field,
`range_torusCentralizer_le_of_finiteSurjective_algClosed` lifts a rational
point of the target centralizer through the finite surjective map `q`.
The commuting square and the first step put its lift in the source
centralizer. The assumed range containment therefore puts the original
point in `D`. The published `range_le_of_algClosed_points` promotes this
to all-test containment when `C'` is reduced and locally of finite type;
these are the exact assumptions of the algebraically closed helper.

Third, `range_torusCentralizer_le_of_finiteSurjective` passes to an
algebraic closure. Centralizer representations and closedness commute
with base change, and smoothness makes the base-changed `C'` reduced
and locally of finite type. Apply the second step, then descend closed
containment with the new `SubgroupFunctor.range_le_of_fieldExtension`.
This last helper applies to any group homomorphisms `a` and closed `d`
whose base-changed ranges are contained, with no reducedness assumption.
The field-extension projection onto the source is schematically dominant:
the extension of fields is surjective with reduced target, and the source
is flat over the field. The universal base-changed source point factors
through the closed subgroup. Schematic factor descent produces a
factorization over `k`, which gives containment on every test scheme.

The provenance is the combination of these Library results, rather than
a claim to reproduce a separately numbered result in the literature.
