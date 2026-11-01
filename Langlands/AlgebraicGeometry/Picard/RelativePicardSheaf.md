# The fppf relative Picard sheaf

For any morphism `f : X → S` of schemes in universe `u`,
`RelativePicard.sheaf f` is the fppf sheaf associated to the actual ordinary
relative Picard presheaf `T ↦ Pic(T ×_S X)`. It is a sheaf of abelian
groups on `Scheme.fppfTopology.over S`. No compactness, separation,
section, or representability hypothesis is required.

`sheafPresheaf f` exposes its underlying abelian-group-valued presheaf,
and `toSheaf f` is the natural sheafification unit from `presheaf f`.
The group at every test scheme and each group homomorphism come from
Mathlib's proved abelian-group sheafification. The construction uses
`presheafToSheaf`; existence is obtained from Mathlib's limits and
filtered-colimit instances for `AddCommGrpCat.{u+1}` and its forgetful
functor. There is no supplied sheafification-existence hypothesis.

`classSheaf f` is the sheafification in `Type (u+1)` of the ordinary class
presheaf `classPresheaf f`. The definitions `classSheafPresheaf f` and
`toClassSheaf f` expose its underlying presheaf and natural unit. Both
constructions use the same fppf topology on `Over S`. The class universe
remains `u+1`, as for the actual module-sheaf isomorphism classes; no
universe reduction is asserted.

`forgetSheafIso f` proves that forgetting the group structure after
group-valued sheafification is naturally isomorphic to the set-valued
sheafification. The proof compares each chosen left adjoint with
Mathlib's concrete double-plus construction and uses the compatibility
of that construction with `forget AddCommGrpCat`. That forgetful functor
preserves the limits and filtered colimits needed here.
`toSheaf_forgetSheafIso_hom` proves the unit compatibility equation:
forgetting `toSheaf f` and then applying the comparison equals
`toClassSheaf f`. The equation follows from the unit equations for the
double-plus comparisons and for sheafification composed with a functor.

`lift f F η` extends any map from `presheaf f` to the presheaf underlying
an abelian-group-valued fppf sheaf `F`. The equation `toSheaf_lift`
proves the factorization, and `lift_unique` proves uniqueness among all
such natural transformations. `classLift`, `toClassSheaf_classLift`, and
`classLift_unique` give the same universal property for every
`Type (u+1)`-valued fppf sheaf. These are applications of Mathlib's proved
sheafification adjunction and its uniqueness theorem.

For an actual line bundle `L` on `T ×_S X`, `sheafClassOf f T L`
is its ordinary class followed by the set-valued unit.
`toClassSheaf_app_classOf` records this evaluation formula.
`map_sheafClassOf` proves compatibility with actual line-bundle pullback
along every morphism of test schemes, using naturality of the unit and
the ordinary presheaf's proved pullback formula. This does not assert
that the unit is injective or that every sheaf section has a global
line-bundle representative.

The source definition is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, Chapter VI §1, Definition (6.1), printed
p.87 (PDF p.91). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Worker 144 read this page directly. The universal properties, canonical
comparison, and evaluation lemmas are internal consequences and packaging
of this source definition using Mathlib's proved sheafification
construction. The fibre product is parameter first; the published
`relativeSpaceSymmetry` identifies it with the source's `X ×_S T`.
Comparison with rigidified classes and representability are separate work.
