# Rational-isogeny comparison for actual integral Harris level restriction

This internal unit uses the actual universe-zero Harris CM arithmetic data,
abelian scheme `B` over `S`, dual witness `W`, and polarization `lam`. A morphism
`f : T' ⟶ T` of quasi-separated test schemes over `S` and a full-order integral
action `a` on the direct family over `T` are supplied. The joint full-order CM
condition is assumed on `a`; the published restriction theorem derives that
condition on the literal action `(relativeEndRestrict B f).comp a` over `T'`.
The named `Prerequisites`, duality naturality, Weil-transition, adelic and torsion
inputs are retained. All positive orders are invertible and the roots of unity
are finite etale on both test schemes. The field-valued point `t` over `T'` and
its composite with `f.left` have finite fibres on finite-etale covers. No
algebraic-closure, connectedness or local Noetherian hypothesis is imposed here.

`harrisIntegralCMLevelPullbackDualData` constructs the constrained changed dual
inputs for every actual positive polarized action on `T`. It packages that
action's own dual and evaluation as a `DualWitness`, pulls this witness back
along `f.left`, and uses the published relative dual-map additivity theorem for
the resulting abelian scheme. Its target family is the actual ordinary
pullback of the same source family. It supplies no independent changed family
or moduli representative.

`harrisIntegralCMFullActionLevelRestriction_related` takes an actual fixed Weil
level orbit at an original Harris level. It compares two actual level data over
`T'`: the direct restricted family with its raw restricted orbit, and ordinary
base change of the source level datum using the constructed dual inputs. These
are related by the original `PolarizedWeilLevel.isogenySetoid`, with multiplier
one and the canonical `relativeIntegralActionRationalComparisonIso`. The direct
action is the rational extension of the literal restricted integral action;
the successive action is ordinary rational base change. Faithfulness of the
assembled positive actions comes from their actual level orbits through the
existing constructions.

The proof reduces the displayed data projections. The multiplier equation is
the published `harrisIntegralCMFullActionRestriction_multiple`, which derives
it from actual dual base-change coherence. The raw restriction first performs
ordinary Weil-level base change and then applies the inverse of the canonical
level comparison. Consequently its transported orbit is the original ordinary
pulled orbit, by the inverse-hom identity for that comparison. Ordered-pair
additivity witnesses are proofs of the same proposition, so proof irrelevance
identifies them. The relation uses the existing opposite right-action and
original Harris level conventions.

The provenance is internal: this specializes the published actual family,
duality and raw Weil-level constructions and applies their inverse identity.
It does not yet prove the commuting square on normalized CM classes or on
compatible families of classes at all geometric points. Test-variable identity
and composition, representing schemes, admissibility, smoothness and division
projectivity remain obligations of the surrounding representability proof.
