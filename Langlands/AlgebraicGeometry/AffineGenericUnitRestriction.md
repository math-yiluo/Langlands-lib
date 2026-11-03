# Detecting total units on affine closed-fibre neighbourhoods

This internal construction connects scalar-localization unit descent to
actual section maps of schemes. For affine opens `V ≤ U` in a scheme `X`
over `Spec R`, `affineSectionRestrictionAlgHom` equips the actual
restriction map `Γ(X,U) → Γ(X,V)` with its `R`-algebra structure. Both
coefficient algebras are `affineSectionAlgebra` for the original structure
morphism `p`. The proof of scalar compatibility uses the naturality of
the affine charts and faithfulness of `Spec`.

Let `R` be any valuation domain, `K` any supplied fraction field, and
let an actual cartesian square identify `q : Y → X` with base change along
`Spec K → Spec R`. Suppose `p` is smooth with geometrically connected
fibres. Let `V ≤ U` be affine opens, with `V` meeting the actual closed
fibre, and assume explicitly that `Γ(X,U)` with its chosen coefficient
algebra is projective over `R`.

`exists_unit_of_affine_generic_restriction` proves that a unit `b` on
`q⁻¹(U)` lifts to a unit on `U` whenever its restriction to `q⁻¹(V)`
is the image of a unit `c` on `V`. The resulting lift maps to precisely
the original `b` under `q.app U`. `affineGenericUnitOfRestriction`
chooses this lift and retains the equality in a subtype.

The implemented proof installs the actual section-map localization
structures supplied by `isLocalization_pullbackSectionAlgebra`.
Smoothness supplies flatness, and hence torsionfreeness, for the section
algebra on `V`. The nonempty closed fibre of `V`, also contained in `U`,
gives prime extended maximal ideals on both affine section algebras.
The restriction maps form a commuting square by naturality of `q.app`.
The scalar-localization descent theorem then supplies the required unit.

The scope retains arbitrary universe, arbitrary-rank valuation domains
including fields, the supplied fraction field, and the original cartesian
square and section maps. Projectivity on `U` is an explicit hypothesis;
this construction does not establish the separate projectivity theorem,
normalize frames, or prove global bundle extension.

