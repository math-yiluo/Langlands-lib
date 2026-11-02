# Descent comparisons from compatible rigidified classes

This internal construction takes an arbitrary morphism `f : X → S` with
section `ε`, a slice morphism `h : U → T`, and a relative rigidified line
bundle `L` over `U`. Its compatibility hypothesis supplies an actual
rigidified isomorphism between the pullbacks of `L` along every pair of
slice maps to `U` with equal composite to `T`. The uniqueness hypothesis
states that each relative category has at most one isomorphism between
any two objects. Neither hypothesis is proved or omitted here.

`compatibleIso` chooses one of the supplied rigidified isomorphisms.
Uniqueness proves their cocycle law and identifies their further relative
pullbacks with the chosen comparisons after composition. The proof of the
latter assertion uses the published relative composition comparison and
checks its underlying module morphism against the actual module pullback
comparison.

For arbitrary scheme maps `a, b : V → U ×_S X` with common composite
`r : V → T ×_S X`, the point-lift geometry gives two slice maps from
`pointBase f r` to `U`. `thetaCommon` pulls the corresponding rigidified
isomorphism back along `relativePointSection f r`, then conjugates by the
module composition comparisons. The result is an ordinary module
isomorphism `a^* L ≅ b^* L`.

`thetaCommon_comp` proves its cocycle law using the cocycle law of the
rigidified comparisons and preservation of composition by transport.
`thetaCommon_precomp` proves compatibility with arbitrary precomposition,
expressed through `Langlands.Scheme.Modules.transport`. The proof combines
uniqueness for the relative comparisons, precomposition of point lifts,
precomposition of the point section, and the iterated transport identity.

`theta` chooses `r = a ≫ (relativeSpace f).map h` for an arbitrary pair
with equal composites. `theta_eq_common` identifies it with the
construction for any specified common composite; proof irrelevance
identifies the equation witnesses. `theta_comp` gives the resulting
ordinary module cocycle law.

These are derived intermediate comparisons using the Library's actual
rigidified pullback and module transport constructions. This pair does
not apply effective descent, construct a descended line bundle or a
rigidification, or prove the full fppf comparison.
