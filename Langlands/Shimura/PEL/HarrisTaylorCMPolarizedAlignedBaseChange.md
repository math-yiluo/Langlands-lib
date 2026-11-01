# Actual normalized CM pullback along commuting base triangles

This derived construction aligns the existing normalized CM polarized class
tower pullback with commuting structural-map and point triangles. It proves
identity, composition and independence from the constrained dual-evaluation
family for the aligned maps. Every tower and pullback is the existing actual
construction; no new class map or coherence equation is supplied as a premise.

The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.
The arithmetic data are the universe-zero totally real number field `E`, its
quadratic CM extension `F`, the central simple unitary datum `D`, and the
imaginary quadratic CM field `L` with its algebra structure on `F`. The
signature charts use `harrisCMSection E (algebraMap L F) τ₀`. The one displayed
map `p : S ⟶ Spec F` determines the conjugated Harris–Taylor reflex structure
`D.harrisTaylorReflexStructure C p`.

The tower at a pointed base `(S, p, s)` is the existing
`HarrisNumericalWeilLevel.isoClassTower` specialized to that reflex structure
and `p`. Its classes form the numerical subtype of the determinant subtype of
the actual polarized quotient. The image condition retains one actual
representative satisfying the determinant condition, geometric dimension and
central Lie trace together. The normalized comparison already identifies this
with the Harris–Taylor determinant-and-dimension condition on that same
representative. All arrows are those of the original Harris compact-open
transporter category, including subgroup forgetting and Hecke transporters.

The shared construction premises remain explicit: tensor pullback comparison,
composition, unit, associativity, left-unitor comparison and symmetry; Picard
zero pullback, Mumford bundle membership and universal base change; dual
naturality and polarization stability; finite Weil transition compatibility;
the rational profinite-integer/finite-adele comparison; and torsion finite
etaleness. Each base is a quasi-separated `Scheme.{0}`, with invertible positive
torsion orders, finite etale roots of unity and the existing
`PositivePairAdditivity` premise. Points are valued in a fixed field `Ω` and
have the displayed finite-fibre witnesses. No flatness or reducedness premise
is introduced.

For an arrow `b : T ⟶ S`, the pullback also retains
`LieBaseChangeNaturalityStatement S` and a family of
`PositivePullbackDualData ... b X` for every actual source polarized action
`X`. This family consists of dual geometry and evaluation data on the actual
pulled-back abelian scheme. It contains neither a chosen output class nor the
desired map equation. Composition retains Lie naturality on the source and
intermediate bases and independently quantified families for `b`, `c` and
`c ≫ b`.

`classTowerPresentationEq_refl` and `classTowerPresentationEq_trans` prove the
unit and composition laws for the existing equality transport of the CM map
and point. The first is reflexivity. The second eliminates the four
intermediate equalities, after which the equation is the unit law for
composition of identity natural transformations. Proof irrelevance identifies
the finite-fibre witnesses.

For maps `p : S ⟶ Spec F`, `q : T ⟶ Spec F` and points
`s : Spec Ω ⟶ S`, `t : Spec Ω ⟶ T`, `classTowerBaseChangeAlong` accepts the
actual commuting triangles

```text
b ≫ p = q,       t ≫ b = s.
```

It eliminates these equalities and uses the already constructed
`classTowerBaseChange` along `b`. Consequently its source is the tower
presented by `(p, s)` and its target is the tower presented by `(q, t)`.
`classTowerBaseChangeAlong_eq` specifies this precisely: it first transports
the source point from `s` to `t ≫ b`, applies actual pullback, and then
transports the target CM map from `b ≫ p` to `q`. Its proof eliminates the two
triangles and simplifies identity transports. The auxiliary finite-fibre
witness at `t ≫ b` may be any witness.

`classTowerBaseChangeAlong_dualData` proves equality of the aligned maps for
any two constrained dual families. Eliminating the triangles reduces this
directly to the existing actual normalized tower independence theorem.

`classTowerBaseChangeAlong_id` uses the triangles `𝟙 S ≫ p = p` and
`t ≫ 𝟙 S = t`. The explicit transport formula and the existing raw identity
law express the map as three equality transports. Their composition laws
combine these into the reflexive transport, which is the identity. The
finite-fibre witness for `t ≫ 𝟙 S` is obtained from the supplied witness for `t`.

`classTowerBaseChangeAlong_comp` considers `b : T ⟶ S`, `c : R ⟶ T` and
triangles

```text
b ≫ p = q,       c ≫ q = v,
r ≫ b = s,       t ≫ c = r.
```

Successive aligned pullback equals aligned pullback along `c ≫ b`. The
structural triangle for the composite first applies
`(c ≫ b) ≫ p = c ≫ (b ≫ p)`, then the two given structural triangles.
The point triangle first applies
`t ≫ (c ≫ b) = (t ≫ c) ≫ b`, then the two given point triangles.
The proof eliminates the four intermediate presentations. Successive aligned
maps then become the existing raw maps. Applying the explicit transport
formula to the direct map leaves exactly the existing raw composition
equation, with source-point and target-CM-map associativity transports. No
relation between the three dual families is required.

The provenance is internal: equality elimination and categorical laws align
the actual pullbacks from `HarrisTaylorCMPolarizedBaseChange`; their raw
coherence and choice independence are reused from
`HarrisTaylorCMPolarizedBaseChangeCoherence` and
`HarrisTaylorCMPolarizedBaseChangeChoice`. This pair makes no additional
original-literature claim. It constructs a prerequisite for assembling a
varying-base pointed polarized functor; it does not yet construct that
functor, prove point independence, supply unpointed moduli, representability
or canonical models, define scheme levels, or construct coefficient descent.
