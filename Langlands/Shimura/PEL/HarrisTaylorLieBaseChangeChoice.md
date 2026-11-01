# Dual-choice independence of Harris dimension and positive Lie pullback

This derived construction restricts the actual ambient choice-independence
theorem of `HarrisPolarizedBaseChangeChoice` to the existing Harris class image
defined by dimension and positive Lie compatibility on one representative.
It constructs `classTowerBaseChangeOfExists` from existence of constrained
actual dual inputs, proves its two forgetful squares, and proves that both
dual-family and path choices leave the mixed point/base pullback unchanged.
All conclusions are maps or equalities of the existing actual polarized
rational-isomorphism classes.

The arithmetic data are the totally real number field `E`, the totally complex
quadratic extension `F`, central simple unitary datum `D` on `A`, its signature
charts `C`, and the imaginary quadratic number field `L` embedded in `F`.
The structure map is `p : S ⟶ Spec F`. The positive auxiliary left involution,
Hodge form, original levels `HarrisLevel D`, and opposite-group transporter
arrows are unchanged from the imported constructions. The source class
condition uses one actual polarized representative with prescribed relative
dimension `[E : ℚ] * n²` and the positive Lie tensor-sheaf condition over the
actual structural `O_S ⊗_ℚ L`: the natural imaginary factor has local rank `n`,
and the two totally real actions agree. No numerical label replaces these
geometric conditions.

The bases are actual universe-zero schemes with arbitrary `b : T ⟶ S`;
both are quasi-separated. The initial pointed map uses a field-valued point
`t` on `T` and `t ≫ b` on `S`, with finite fibres for the finite-etale covers
at both points. All imported named tensor/Picard hypotheses remain explicit:
pullback tensor comparison, composition, unit coherence, associativity,
left-unitor comparison and symmetry; Picard-zero pullback, the Mumford-bundle
Picard-zero property and universal base change. The relative finite-Weil
transition proposition, rational profinite-integer/finite-adele comparison,
torsion finite-etale proposition, invertibility of all indexed torsion orders,
finite etale roots of unity on both bases, and ordered-pair dual additivity
on both bases also remain inputs. The imported proved
`dualAbelianBaseChangeNaturality` and `polarizationBaseChange` supply the two
corresponding arguments of ambient pullback internally. No flatness condition
on `b` is imposed.

For each source positive polarized action `X`,
`PositivePullbackDualData ... b X` is dual-evaluation data indexed by
`(Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme`.
The bundle contains a dual-scheme witness and geometry, an inverse Poincare
bundle and its tensor evaluation, and endomorphism additivity. It cannot
supply an independently chosen abelian scheme, polarized output, compatible
level orbit or quotient map. Two families may make different constrained
choices of bundles and evaluations. The theorem concerns equality after
passing to the existing quotient; it does not assert equality of these data
or of their polarized representatives.

`classBaseChange_dualData` proves equality of the two restricted class
functions at every original Harris level. Subtype extensionality reduces
this to the ambient quotient-map equality
`HarrisPolarizedWeilLevel.ambientClassBaseChange_dualData`, evaluated at the
underlying ambient class. The property fields may differ, but the underlying
classes agree. This uses the existing restriction by a single jointly
satisfying representative; it assumes no invariance of dimension under an
arbitrary rational isomorphism. Extensionality in level and class gives
`classTowerBaseChange_dualData`, equality of the complete natural
transformations.

`classTowerBaseChangeOfExists` takes
`dualExists : ∀ X, Nonempty (PositivePullbackDualData ... b X)`.
Classical choice selects one constrained actual input for each source object.
The existing actual pullback and joint-condition preservation construct the
restricted natural transformation from the tower over `p` at `t ≫ b` to
the tower over `b ≫ p` at `t`. The equality theorem
`classTowerBaseChangeOfExists_eq` identifies it with the tower map computed
using every supplied actual family; the component theorem
`classTowerBaseChangeOfExists_app` gives the same formula on each class.
Existence of these constrained inputs is still assumed, and is not proved
by applying classical choice.

`classTowerBaseChangeOfExists_inclusion` identifies this construction with
the restriction of the existence-only ambient pullback. Its square is the
existing inclusion square evaluated at the chosen family.
`classTowerBaseChangeOfExists_forgetDimensionLieAction` proves the second
square: forgetting the polarization and level after this pullback agrees
with the existing `actionClassTowerBaseChange`, which is the map of
`HarrisTaylor.dimensionLieActionPresheaf` for `Over.homMk b rfl`.
Both are equalities of natural transformations, and all tower maps retain
naturality for every original level inclusion and Hecke transporter arrow.

For a second field-valued point `s` on `T` and a fibre-functor path
`epath : fiberFunctor s hsT ≅ fiberFunctor t ht`, the imported diagonal
`classTowerBaseChangeAlongPath` is pointed base pullback at `s` followed by
point comparison on `T`. It maps the source tower at `s ≫ b` to the target
tower at `t`. Finite fibres at `s` and `s ≫ b` remain hypotheses.
`classTowerBaseChangeAlongPath_dualData` unfolds this diagonal and rewrites
the pointed pullback using the proved family independence.
`classTowerBaseChangeAlongPath_choices` combines that result with the
existing whole-tower path independence. Thus independently changing both
the actual dual family and the path gives the identical natural
transformation, without requiring equality of the paths.

With `T` connected and locally Noetherian, and both endpoint fields
algebraically closed, the existing `classTowerGeometricBaseChange` chooses
a path from proved geometric path existence. Its family independence is
`classTowerGeometricBaseChange_dualData`, obtained by unfolding the
construction and applying diagonal family independence.
`classTowerGeometricBaseChange_eq_any_choices` proves that the resulting
geometric pullback is computed by every supplied path and every actual
dual family. It combines family independence with the already proved
equality of canonical comparison and any path. These conclusions do not
need connectedness or local Noetherianness of `S`.

The provenance is an internal derivation from the imported actual ambient
choice-independence theorem, subtype restriction, the existing mixed
point/base square and path independence. It is not a new translation of a
numbered literature result; the original Harris conventions are inherited
through those constructions. The unit does not prove existence of dual
inputs, identity or composition for successive base changes, equivalence
with geometric-isogeny classes, representability, scheme levels or
coefficient descent. The named tensor/Picard/Weil hypotheses remain explicit.
