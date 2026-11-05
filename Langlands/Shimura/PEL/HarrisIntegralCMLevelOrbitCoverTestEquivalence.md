# Direct levels on arbitrary connected tests of a finite Harris orbit cover

This is an internal deduction from the published actual finite-etale cover,
continuous-action, and Harris restriction comparisons. It extends the
Hom-to-direct-level comparison to arbitrary connected locally noetherian test
schemes over the fixed base. The test morphism is an arbitrary scheme morphism.

The ambient number fields and algebra have universe zero and the same Harris CM,
central simple unitary, signature-chart, and scalar-tower hypotheses as
`HarrisIntegralCMLevelOrbitCovers`. The supplied inputs are the actual abelian
family `B`, dual witness `W`, dual-valued homomorphism `lam`, and integral order
action `a` over `T`. The construction retains `Prerequisites`, finite Weil
transition compatibility, the rational profinite-integer/adele comparison,
torsion finite etaleness, invertibility of torsion orders, and the stated finite
etale roots-of-unity hypotheses. It supplies no additional moduli or
representability hypothesis.

The base `T.left` is quasi-separated, connected, and locally noetherian. A point
`s : Spec Ω → T.left` is supplied over an algebraically closed field, together
with finiteness of all finite-etale geometric fibres. For the actual selected
orbit cover at level `V`, the construction retains a level `U` and a nonempty
original fixed-level set at `U`; these are the published hypotheses proving
finiteness of each raw monodromy orbit. For a test `T'` the hypotheses are
quasi-separatedness, connectedness, local noetherianity, a morphism `f : T' → T`
in `Over S`, a point `t`, a propositional equality `t ≫ f.left = s`, and
finiteness of all finite-etale fibres at `t`. Direct-level constructions also
retain invertible torsion orders and finite etale roots of unity over `T'`.
The test need not be finite etale over `T`.

The private helper `sectionFixedFiberEquiv` identifies sections of a finite-etale
cover over a connected locally noetherian scheme with elements of its actual
geometric fibre fixed by the entire fundamental group. The proof uses the
published `geometricContinuousActionEquivalence`. The identity cover has a
unique geometric lift; evaluation of a section at that lift is fixed by
naturality. Full faithfulness proves injectivity. A fixed fibre element gives a
constant equivariant map from the identity fibre; fullness reconstructs the
section and the map/preimage identity gives its value. This is an actual section
of a scheme cover, rather than an assumed realization of a set-valued functor.

The private `testSectionEquiv` explicitly identifies a morphism from
`Over.mk f.left` into a cover with a section of its pullback. It uses the
pullback lift in one direction and the first projection in the other; the
pullback universal property proves both inverse laws. `testFixedFiberEquiv`
composes this with `sectionFixedFiberEquiv` over the test, then the inverse of
`pullbackFiberEquiv`. The published equivariance formula
`pullbackFiberEquiv_smul` transports fixedness to the original fibre under the
actual `fundamentalGroupMap`. The two private apply lemmas identify the result's
underlying scheme morphism with `t ≫ k.left`. No finite-etale hypothesis on the
test morphism enters these steps.

`harrisIntegralCMFiniteOrbitCoverTestRawEquiv` specializes this construction to
the actual Harris orbit cover and composes it with the existing
`harrisIntegralCMFiniteOrbitCoverFiberEquiv`. Its target is precisely

`{z : RawOrbits V // z ∈ orbit Gamma q ∧ ∀ g, alpha g • z = z}`,

where `Gamma` is the actual base fundamental group, `q` is the chosen original
raw class, and `alpha` is the actual fundamental-group map induced by `f` and
the supplied point equation. The fibre comparison's published equivariance
proves fixedness in both directions; its inverse laws prove the new inverse
laws. `harrisIntegralCMFiniteOrbitCoverTestRawEquiv_apply_val` identifies the
forward value with the existing fibre comparison applied to the actual lift
whose underlying map is `t ≫ k.left`.

`harrisIntegralCMTestLevelOrbitEvaluationEquiv` identifies direct fixed levels
on the original restricted family, with the literal integral action
`(relativeEndRestrict B f).comp a`, whose raw restriction value lies in the
chosen orbit, with the same orbit-and-image-fixed subtype. It uses the
published `harrisIntegralCMRestrictionImageFixedEquivAt`, including its actual
restriction-value formula. The forward map is literally the old
`harrisIntegralCMRestrictionRawClass`. Injectivity follows from that published
equivalence. For surjectivity, its inverse reconstructs a direct level from the
image-fixed class; the apply/inverse identity proves the raw value and hence
the required orbit membership. This intermediate equivalence itself requires
no reference level `U` or nonempty set of base fixed levels.

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv` composes the raw Hom
correspondence with the inverse of the direct-level evaluation equivalence.
Its source is the actual Hom set in `Over T.left` from `Over.mk f.left` to the
chosen cover. Its target is exactly the direct fixed levels at `V` on the
original restricted family with the single additional condition that their
original raw restriction value belongs to the target orbit. Image fixedness is
proved by the restriction equivalence, rather than imposed as an extra
condition on those direct levels.

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val` states that this direct
level's original raw restriction value is the fibre comparison of the actual
composite `t ≫ k.left`. The proof projects the direct evaluation equivalence's
apply/inverse identity and then applies the proved raw Hom evaluation formula.
This establishes the actual morphism and level value comparison.

The contribution concerns a supplied family and an individual finite raw orbit
on pointed connected locally noetherian tests. It does not establish naturality
under changes of test, a comparison on disconnected tests, independence of
geometric points, normalized rational-isogeny comparison, or existence of the
full representing PEL scheme. Admissibility, smoothness, and division-case
projectivity in `DivisionCMRepresentabilityStatement` remain separate proof
obligations. All imported Lean and Markdown pairs and that target are preserved.
