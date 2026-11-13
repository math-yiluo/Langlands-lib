# Proof of Levi sharp transport from membership in an unramified apartment

Author: Worker 118.

Lean module: `Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportProof`.

The theorem `Langlands.Geometry.Building.unramifiedLeviSharpApartmentTransport` proves
`UnramifiedLeviSharpApartmentTransportStatement.{u}` at an arbitrary universe `u`. Its
hypotheses are unchanged.

## Proof

The proof specializes the general infinite-field theorem
`KPApartmentData.exists_leviSharp_transport` from the helper module
`Langlands.Geometry.Building.LeviSharpTransport` (see `LeviSharpTransport.md`). Write `K`
for `inertiaFixedField F` and the subscript `K` for base change along
`algebraBaseMap F K`. After introducing the binders and the instances fixed by the
statement, the proof checks the hypotheses of that theorem:

- `G_K` is connected reductive: `IsConnectedReductive.baseChange_of_algebraicExtension`.
- `iT_K` is a maximal split torus of `G_K`: the hypothesis `hiT`.
- `K` is infinite: `F` is infinite (`LocalField.infinite_of_isNonarchimedeanLocalField`)
  and the field map `F → K` is injective.
- `S_K` is a split torus: base change of the split torus `S`
  (`IsSplitTorus.baseChange` applied to the split-torus part of `hiS`).
- `CommGroupScheme.groupHom f_K ≫ iT_K = iS_K`: the Library lemma
  `baseChange_groupHom_comp_of_factorization` applied to `f` and the factorization
  hypothesis.
- `n` normalizes `iS_K`: the membership proof carried by
  `n : normalizerPoints iS_K`.
- `D.apartmentMap y = n • D.apartmentMap x`: the witness `y` of the chart-membership
  hypothesis.

`exists_leviSharp_transport` then returns `h` with exactly the three conclusions of the
statement: `h` centralizes `iS_K`; `h` lies in the supremum of `D.filtration x χ 0` over
the relative roots `χ` of `T_K` with `f_K ≫ χ = 0`; and `n * h` normalizes `iT_K`.

The centralizer datum `C`, the `ω`-compatibility hypothesis and the specific valuation of
the maximal unramified extension are not used. The general theorem holds for apartment
data with an arbitrary `ω` over any infinite field. The maximality of `iS` is used only to
know that `S` is split and that `iS` is a monomorphism, which the statement uses to set
up its binders.

## Relation to the source argument

The statement's Markdown sketches a geometric proof via the Levi building
(Kaletha–Prasad, Propositions 7.6.4(2), 7.7.5(4) and §9.7.4). The implemented proof
follows a different, purely group-theoretic route. It decomposes the sharp fixer
element `n⁻¹ m` according to a cocharacter of `S_K` adapted to the Levi. Conjugation by
the points of `S_K` then shows that the non-Levi factors are trivial, which uses the
infinite field `K` (details in `LeviSharpTransport.md`). No building comparison, Levi
quotient comparison or parahoric transitivity is assumed.
