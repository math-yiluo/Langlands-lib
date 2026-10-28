# Harris trace-form comparison on compact open level towers

Author: Worker 57. This internal construction carries the proved topological
regular-module trace-form comparison through actual compact open subgroups,
transporter arrows, double quotients and the CM-compatible Harris tower.
It derives the comparison from the existing groups and spaces; it does not
store a supplied space or a supplied comparison theorem.

For topological groups `G` and `H` and a continuous multiplicative equivalence
`e : G ≃ₜ* H`, `CompactOpenLevel.transport e U` is the image of the actual
compact open subgroup `U`, implemented as its inverse image under `e.symm`.
Openness follows by continuous inverse image and compactness by the inverse
homeomorphism. Membership is exactly `h ∈ transport e U ↔ e.symm h ∈ U`;
in particular `e g` belongs to the transported subgroup exactly when `g`
belongs to `U`. Transporting back gives the original compact open level.
Only the existing group and topology instances are needed for these facts.

`transportFunctor e` carries each transporter arrow represented by `g` to
the arrow represented by `e g`. The condition `g⁻¹ U g ⊆ V`, identity and
composition laws are proved from the group equivalence. If both groups are
topological groups, `transport_heckeLevel` identifies the intermediate
level `U ∩ g V g⁻¹` with the corresponding intermediate level after transport.
`transport_heckeLeft` and `transport_heckeRight` prove equality of both legs
as arrows, using `eqToHom` for that identification of their source levels.

For a group `Γ` acting on `X` and a homomorphism `ι : Γ →* G`,
`LevelSpace.transportEquiv ι e U` changes the finite coordinate by
`(x,a) ↦ (x,e a)` and changes the diagonal to `e.toMonoidHom.comp ι`.
The source is `Γ \ (X × G) / U` and the target is
`Γ \ (X × H) / (U.comap e.symm.toMonoidHom)`.
The relation proofs transport the same rational element and the same level
element through `e` and `e.symm`. Quotient induction proves the two inverse
identities. With topologies on `X`, `G` and `H`,
`transportHomeomorph` is a homeomorphism for the existing quotient topologies:
continuity descends from the continuous product maps in each direction.
Neither a topology on `Γ` nor continuity of its action is required here.

`transport_translate` proves that these homeomorphisms commute with every
transporter map. If multiplication is continuous in both finite groups,
`transportTowerIso` packages them as a natural isomorphism from `tower ι`
to `transportFunctor e ⋙ tower (e.toMonoidHom.comp ι)`. In this natural
isomorphism the two finite groups lie in the same universe so that both
functors land in the same `TopCat` universe. The preceding subgroup and
individual quotient-space constructions allow independent group universes.

For the actual Harris specialization, retain the fields, algebras,
scalar towers, central-simple datum `D`, skew-adjoint unit `β` and
`hβ : D.involution β = -β` of `PEL.TraceSimilitudesTopology`. Its
`HarrisBilinearPoints β hβ S` is the group of left-`S ⊗[ℚ] A`-linear
similitudes for the scalar extension of
`ψ(x,y) = Tr(x β⁻¹ τ(y))`, with `τ = β σ β⁻¹` and the normalized regular
rational trace of the imported construction. The right-adjoint involution
is the original `σ`, as proved in `TraceSimilitudesBaseChange`.

`harrisPELFiniteAdelicEquiv` is a continuous group equivalence

`G(𝔸_f) ≃ₜ* (D.HarrisBilinearPoints β hβ (FiniteAdeles ℚ))ᵐᵒᵖ`.

It takes the opposite of the published comparison from `G(𝔸_f)ᵐᵒᵖ`,
using the canonical double-opposite equivalence. This retains the original
group multiplication, right-translation order and scalar multiplier. Its
unop acts on a vector by `x ↦ x * g.val.1`; its multiplier is exactly
`g.val.2`. The finite adeles are the actual restricted product from
`Langlands.Global`. The diagonal compatibility theorem identifies the
transported rational diagonal with `MulOpposite.op` of the published
`harrisBilinearDiagonal`, after the proved rational trace-form comparison.

`harrisPELLevelFunctor` applies the subgroup/arrow construction to this
actual continuous group equivalence. Its image-membership and arrow-element
formulas are explicit Lean theorems. `harrisPELLevelTower` uses the existing
corrected domain `(HarrisSignatureCharts.ofSignature h hΦ).Domain` and its
existing rational action, for a specified CM section `Φ`. Its rational
diagonal is the composite just identified with the actual bilinear diagonal.
`harrisPELLevelTowerIso` identifies `unitaryLevelTower D h Φ hΦ` naturally
with this tower pulled back along `harrisPELLevelFunctor`. Rational finite
dimensionality is derived from `D.totallyRealBasis`, so none is added as
an arbitrary extra premise. The theorem `harrisPELLevelTowerIso_hom_app_mk`
gives the component formula on representatives `(x,a) ↦ (x,e a)`.

For an imaginary quadratic field `F`, an embedding `ιF : F →+* K` and a
chosen complex embedding `τ₀`, `harrisCMPELLevelTower` uses the already
constructed `harrisCMSection E ιF τ₀`. The isomorphism
`harrisCMPELLevelTowerIso` specializes the comparison to
`harrisUnitaryLevelTower D h ιF τ₀`, the CM type in Harris (1999), Section 4.
The generic Hecke-intermediate and two-leg theorems, and naturality for all
transporter arrows, apply to this specialization.

The contribution has internal provenance. Its new arguments are subgroup
transport, quotient descent, product continuity, opposite-group functoriality
and naturality applied to existing published mathematical constructions.
The original group, CM-type, domain and trace conventions are inherited from
`Unitary.HarrisLevels` and `PEL.TraceSimilitudesTopology`, together with
`PEL.TraceSimilitudesBaseChange` and `PEL.TraceSimilitudesNaturality`.
Their original-source locators include Harris (1999), Section 1 p.301 and
Section 4 pp.308–309; Harris (1997), Section 2 pp.88–90, corrected by Harris
(1998), Erratum pp.180–182; Kottwitz (1992), pp.654–655; and Harris–Taylor
(2001), I.6 p.45 and I.7 p.52. No new existence or comparison theorem from
that literature is supplied as a premise in this unit.

This constructs a comparison of the actual topological double-quotient
towers. Neatness, stabilizer freeness, finite torsor fibers, local-system
descent, Hodge positivity, PEL representability and algebraic scheme levels
remain separate mathematical obligations of the host task.
