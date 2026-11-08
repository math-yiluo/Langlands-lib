# Compact-open completion under a topological group isomorphism

This is a derived transport construction for the compatible-family completion
used in Renard, *Représentations des groupes réductifs p-adiques* (2026),
I.1.4–I.1.5 and VI.9.7 (printed pp.9–10, 205–206 / PDF pp.15–16, 211–212).
The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The explicit transport through a topological group isomorphism is an internal
construction, rather than a separately numbered assertion in the source.

Let `G` and `H` be topological groups in independent universes, let
`e : H ≃ₜ* G`, and let `ρ` be a smooth complex representation of `G` on an
arbitrary complex module `V` in a third universe. No local compactness or
nonarchimedean group assumption is required. The pulled-back representation
is the actual representation `ρ.comp e.toMonoidHom`; its smoothness is
available from the imported `isSmooth_comp`. The averaging and completion
results accept any proof of this smoothness.

`compactIndexComap e K` is the preimage of the compact open subgroup `K`.
It is open by continuity and compact because `e` is a homeomorphism.
Membership is literal preimage membership, and preimages preserve inclusion.
Preimage under `e.symm` reverses this construction, as proved by the two
inverse identities. `compactIndexEquiv` packages these maps into a bijection
of the existing compact-open index types.

`Compact.averageMap_comp_equiv` identifies the actual normalized compact
average of the pullback at `J` with that of `ρ` at
`compactIndexComap e.symm J`. The proof identifies their orbit sets: the
subgroup elements correspond by `e` and `e.symm`, and their actions on `V`
agree. Both orbit means are the same expression in that set. Thus no Haar
measure comparison or assumed averaging identity enters the construction.

`pullbackEquiv` sends a compatible family `v` to
`J ↦ v (compactIndexComap e.symm J)`. Its inverse sends `w` to
`K ↦ w (compactIndexComap e K)`. The average identity and preservation of
inclusions prove compatibility in both directions. The inverse identities
for compact indices prove the two maps inverse; pointwise operations prove
linearity. The two component formulas are definitional.

This unit supplies a change of group for the completion. It does not assert
the structural contraction basis, stationarity, Jacquet comparison, or
either exact represented-parabolic proposition of the parent task.
