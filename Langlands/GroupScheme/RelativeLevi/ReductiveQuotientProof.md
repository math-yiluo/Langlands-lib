# The universal reductive quotient of a relative parabolic subgroup

`Langlands.GroupScheme.relativeParabolicReductiveQuotient` proves exactly
the unchanged `RelativeParabolicReductiveQuotientStatement.{u}`. The
universe is arbitrary, and the base is any scheme. For every reductive
group scheme `G`, relative parabolic inclusion `i : P → G`, and supplied
relative unipotent radical `r : U → P`, it gives a reductive group scheme
`M` and a represented fppf quotient `q : P → M` whose full kernel is the
all-test range of `r`. Every homomorphism from `P` onto a reductive group,
surjective on underlying schemes, factors through `q` uniquely as a group
scheme homomorphism. The theorem has no additional premises.

The proof is an internal composition of the following constructions.
`relativeParabolicEtaleLocalDynamic` supplies a genuine etale covering
family on which the actual pulled-back parabolic inclusion represents a
dynamic parabolic. The cover bridge
`RelativeLevi.pointwise_dynamic_of_etaleLocalDynamic` chooses, for each
base point, a cover member and a point above it. Thus the presentations
have exactly the pointwise form required by both geometric helpers. The
dynamic relative Levi input in those helpers is supplied by
`dynamicRelativeLevi`.

For quotient existence,
`RelativeLevi.exists_reductiveQuotient_of_pointwise_dynamic` identifies
the etale pullback of the supplied radical with the contracting subgroup
of each local cocharacter. The dynamic limit map constructs a reductive
fppf quotient with that full kernel. Etale gluing of normal quotients and
reflection of reductivity give the quotient over the original base.
The gluing construction uses finite affine refinements and affine fpqc
descent on affine charts, followed by open-cover gluing; it requires no
affineness or quasi-compactness assumption on the base.

For radical annihilation,
`RelativeLevi.annihilates_radical_of_pointwise_dynamic` uses the same local
identification. The dynamic annihilation theorem makes the composite of
the local radical inclusion and every scheme-surjective homomorphism to a
reductive group zero. Fppf equality descent proves that the original
composite `r ≫ f` is zero over the whole base.

Finally, `relativeParabolicReductiveQuotientReduction` combines these
two results. Relative affineness makes the quotient map quasi-compact.
The full-kernel assertion and radical annihilation imply that `f` kills
the scheme-theoretic kernel of `q`; fpqc descent of actual group scheme
homomorphisms then supplies its unique factorization. This proves the
universal property as well as quotient existence.

This proof introduces no new assertion from external literature. Its
provenance is the explicit composition above; the original-source
correspondence belongs to the unchanged statement Markdown. The
pointwise quotient and annihilation lemmas retain their conditional
interfaces, and this final theorem discharges both inputs. The radical
comparison and transport helpers used by those constructions are in
`DynamicRadicalIdentification` and `UnipotentRadicalDescent`.
