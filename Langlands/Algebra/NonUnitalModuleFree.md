# Actual free nonunital modules

This construction follows Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.5.3, printed p.27 / PDF p.33.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source defines a free object as one isomorphic to a direct sum of
copies of its regular algebra module and uses the maps a ↦ a m.

The construction uses only the original nonunital ring and additive action
laws, so it extends the cited complex-algebra construction to arbitrary
nonunital rings. No complex structure, unit law, finite dimension or
projectivity premise is required. Nondegeneracy of the regular object and
its sum requires the stated `IsIdempotented A`.

`Regular` is a universe lift of A with multiplication action
a · x = up(a * down(x)). `regularDown` and `regularUp` are mutually
inverse original intertwiners to and from the published
`NonUnitalModule.regular A`, which is literally left multiplication.
Their composition equations are equalities of the entire original maps.
A two-sided local idempotent for down(x), supplied by the published
corner characterization, proves `regular_isNondegenerate`.
`regularAction` reuses
`NondegenerateModuleNaturalEndEvaluation.liftedAction`, and `regularObject`
reuses its `liftedRegularObject`. These retain the same lifted carrier,
additive group and multiplication action.

`Carrier` is the dependent finite-support sum of these regular carriers.
Its additive group and `carrierAction` use the constant family of the
specified regular additive groups and actions. `smul_apply` exposes
the original coordinate formula. `object` bundles this carrier and
action with the nondegeneracy proved by `NonUnitalModuleDirectSum`.
Its exposed carrier and action equations are definitional.
`inclusion` is that construction's actual singleton intertwiner;
`inclusion_apply` exposes its finitely supported function formula.
The coefficient universe uA, lift universe uL and
index universe uI remain independent; the sum carrier lies in
max uI (max uA uL).

`orbit m` maps each lifted a to a · m in any original target module.
`fromFamily v` descends those maps on the actual sum, so a singleton
with coefficient a in summand i maps to a · v(i). The target carrier
universe uM is independent of all three preceding universes. These
maps do not require target nondegeneracy or a fixed choice of local
idempotents.

`IsFree hA M` means that an object M with carrier universe max uA uM
is isomorphic in the actual nondegenerate category to `object hA I`
for some I in that same universe, using lift parameter uM. The
canonical inverse regular maps explain the harmless universe lift:
the summands retain actual A and its multiplication. This is the
source's module-theoretic direct-sum definition of freeness, with
the index size stated explicitly.
`object_isFree` records the reflexive isomorphism for such a displayed
sum in the stated universe.

This construction proves only its intrinsic laws. The assertion that
every nondegenerate module is a quotient of a free object and the
assertion that every projective is a direct summand of a free object
remain separate statement and proof obligations. It makes no converse
projectivity assertion: the source explicitly warns that the regular
module need not be projective for a nonunital idempotented algebra.
