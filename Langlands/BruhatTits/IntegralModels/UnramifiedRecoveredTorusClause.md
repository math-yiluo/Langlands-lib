# Torus clauses in recovered apartment fixer models

This derived supporting module constructs the prescribed lower integral torus
in supplied recovered apartment models and proves its complete torus clause.
It also proves maximality of the prescribed upper torus in the full and neutral
special fibres. All declarations work at arbitrary universe `u`.

`IntegralTorusData.satisfiesTorusClause_of_generic` applies over a Henselian
local domain `R` with fraction field `K`. Supply relative-component model data
`D`, a connected reductive generic group `G`, and integral torus data `A` whose
generic inclusion is a maximal split torus. If `A.IsClosedSplit`, then
`A.SatisfiesTorusClause`: the actual residue inclusion is maximal split in the
neutral special fibre. No reductivity of that special fibre is assumed.
The proof transports generic maximality through `A.genericIso` and the neutral
model's generic identification, then applies the published
`isMaximalSplitTorus_residue_of_generic` to the smooth affine neutral model.

For the recovered apartment constructions, let `F` be a nonarchimedean local
field, `K = inertiaFixedField F`, and `G` an affine group scheme over `F`.
Supply a commutative group scheme `T` with inclusion `iT`, monomorphic after
extension to `K`, an actual upper apartment `D`, a centralizer `C`, and their
full integer-valued omega compatibility. For any subset `Ω` of that apartment,
supply `M : RecoveredApartmentFixerModels D Ω`. This structure includes the
actual lower and upper model pairs, their compatible full and neutral
unramified recovery, and the exact upper full integral-point equality with
the character-valuation kernel intersected with the pointwise fixer of `Ω`.

If `iS : S → G` is a maximal `F`-split torus and `f : S → T` satisfies
`f ≫ iT = iS`, then `M.lowerApartmentTorus C hDC hiS hf` is integral torus data
in `M.lower.neutral` with prescribed generic torus `S` and inclusion `iS`.
It is the published `integralTorusOfFullRecovery` applied to the fields of `M`.
`lowerApartmentTorus_isClosedSplit` retains the published closedness and
integral splitting. If `G` is connected reductive,
`lowerApartmentTorus_satisfiesTorusClause` applies the general lemma above over
the Henselian integer ring of `F`, proving maximal splitness in the lower
neutral special fibre as well.

For the upper conclusions, assume `G` is connected reductive and the supplied
`T_K → G_K` is maximal split. The constructions
`M.upperFullApartmentTorus hG hiT C hDC` and
`M.upperNeutralApartmentTorus hG hiT C hDC` retain the original upper generic
torus and inclusion. The two `specialInclusion_isMaximalTorus` lemmas assert
maximality of these actual residue inclusions in the full and neutral special
fibres, respectively. They apply the published general
`IntegralSplitTorusData.specialInclusion_isMaximalTorus`, using smoothness of
the respective models, Henselianity of the upper integer ring, its algebraically
closed residue field, and connected reductivity after algebraic extension.

The provenance is entirely internal composition of the named Library
constructions and generic-to-residue maximality proofs. There is no new
literature assertion. No equality describing all neutral integral points,
zero datum, nonemptiness or boundedness of `Ω` is required. The lower
construction does not require maximality of `T_K`. Model existence, a
morphism between the lower and upper integral tori, quotient-root survival,
and `UnramifiedSpecialApartmentChamberStatement` remain outside this module.
