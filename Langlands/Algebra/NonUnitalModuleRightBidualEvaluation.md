# Evaluation into the actual right bidual

The source construction is the canonical evaluation in Renard,
*Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, I.4.1, printed p.23 / PDF p.29, following the two dual functors on
printed pp.22–23 / PDF pp.28–29
(`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
Original actions follow printed pp.5–7 / PDF pp.11–13, and the recovered
complex module follows I.2.1, printed p.14 / PDF p.20.
The supplementary 2010 corrections, PDF pp.1–2
(`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`),
concern nearby injection, reflexivity and exactness arguments. The 2026 edition
governs; this pair constructs evaluation without making those further claims.

`rightEvaluation` is an original right intertwiner from M into
`RightBidual hA hM`. Its definition composes `comparisonHom hA hM` with the
published `evaluation hA.op hM`. `rightEvaluation_eq_transport` exposes that
equality of entire bundled maps. This reuses the generic evaluation and its
membership proof; the first dual is transported to its actual left action
before the target's second-dual canonical scalars are recovered.

`rightEvaluation_val` identifies the entire included full functional with the
full comparison of the published full evaluation.
`rightEvaluation_val_coe` identifies its entire underlying function with
`fun φ => φ.val m`; `rightEvaluation_apply` specializes this to any actual first
right dual φ. `rightEvaluation_fixed` retains every original fixing idempotent.
Its proof invokes the published `fullEvaluation_fixed` to fix generic
evaluation, then applies the original-action comparison intertwiner.
`rightEvaluation_map_smul` is the constructed right map's action law.

`rightEvaluationLinear` uses precisely the source and actual target complex
modules recovered by `NondegenerateScalars.complexModule`. Its whole additive
map equals that of `rightEvaluation`. `rightEvaluationLinear_eq_transport`
identifies the entire linear map with `comparisonLinear` composed with the
published `evaluationLinear`. The proof uses linear-map extensionality and
the definitional functional formulas.

`rightEvaluation_naturality` compares entire original right intertwiners, with
independent source and target universes. The implemented proof reassociates
composition, uses the comparison's whole-map naturality and the published
generic evaluation's whole-map naturality, then reassociates again.
`rightEvaluation_linear_naturality` gives the same equation for the precisely
recovered complex modules and automatic linearizations of the same
intertwiners; linear-map extensionality reduces it to original-map naturality.

`rightEvaluationNatTrans` is definitionally the published
`evaluationNatTrans hA.op` followed by the hom of `comparisonNatIso hA`.
Its target is exactly
`(rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA`.
The transport law identifies the entire natural transformation and the
component law identifies each entire categorical component. The component
Hom and additive-map laws agree with the original `rightEvaluation`;
the `val`, `val_coe` and application laws expose its full-functional formulas.
`rightEvaluationNatTrans_naturality_hom` exposes the entire component
naturality equation as original bundled maps.

The comparison transport, scalar packaging and categorical packaging are
derived internal constructions implementing the source's actual right
evaluation. The published generic evaluation is imported by Lean name and
retains its existing authorship. The comparison extends Worker 6's audit.
The companion Checks pair checks complete unapplied interfaces, unequal
universes, competing structures and zero carriers. No prior complex module on
M, dimension bound, nonzero condition, anti-involution, faithful action or
evaluation certificate is assumed.
