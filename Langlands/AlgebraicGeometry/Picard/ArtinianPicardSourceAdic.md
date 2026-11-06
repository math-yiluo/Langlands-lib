# Actual maps from Picard tower stages to ordinary adic tests

This internal construction defines actual augmented maps from tower tests to
ordinary adic tests whenever the required kernel containment is given. It
proves their uniqueness, surjectivity and compatibility. The final existence
results retain the isolated general cofinality statement as an explicit
premise; this module supplies no proof of that premise.

Keep the actual Picard source tower's arbitrary common universe `u`,
commutative base `k`, field `K` with the specified `k`-algebra structure,
Noetherian local `k`-algebra `R` with its surjective augmentation `ε`, actual
flat proper morphism `f`, residue-fibre line bundle `M`, and actual initial
pointed stage `s₀`. Let `C` be the unchanged actual quotient `limitRing` and
`ε_C` its original descended augmentation. Every actual tower test `A_n`
has its existing surjective `k`-algebra projection `p_n : C → A_n`.

`projectionKernel n` is the actual ideal `ker p_n` in `C`.
`projectionKernel_antitone` follows by identifying it with the actual image
of the stage equation ideal in `C` and applying monotonicity of ideal maps
to the existing antitone equation sequence. `iInf_projectionKernel` is the
already proved zero intersection of the actual projection kernels.

`adicTest a` is `LocalAdicArtinianTests.test ε_C hε_C a`, the actual
augmented Artinian test with algebra `C/m_C^(a+1)` and its specified original
residue augmentation. `adicProjection a` is the canonical quotient map from
`C`; `ker_adicProjection` identifies its actual kernel with `m_C^(a+1)`.

For an explicit containment `ker p_n ≤ m_C^(a+1)`, `toAdic` is an actual
arrow of augmented tests `A_n → C/m_C^(a+1)`. A private generic
`augmentedDescent` uses `AlgHom.liftOfSurjective` to descend the canonical
adic projection through the original surjection `p_n`. Its augmentation
triangle is checked after choosing a preimage under that surjection, then
using the two original augmentation equations. This is a genuine algebra
map between the original tests, without replacing either test or choosing
a coefficient-field section.

`toAdic_projection` retains its exact defining equation: composing with
`p_n` gives the canonical adic projection from `C`.
`toAdic_surjective` follows from surjectivity of that adic projection.
`toAdic_unique` says the same equation uniquely determines the actual test
arrow, by evaluating the two algebra maps on preimages under `p_n`.

`later_bound` propagates a kernel containment to all later tower indices by
antitonicity. `toAdic_step` proves that descending from stage `n+1` through
its actual elementary step and then mapping to the fixed adic test gives
the same actual map as the propagated containment. Uniqueness reduces this
to the exact consecutive projection equation.
`toAdic_adicTransition` likewise proves compatibility when one ordinary
adic test is reduced to an earlier one. It uses the same uniqueness and
the original `LocalAdicArtinianTests.projection_transition` equation.

For the last two results assume additionally that `R` is complete for its
actual maximal ideal and supply
`hc : Langlands.Algebra.CompleteLocalIdealCofinalityStatement.{u}`.
The preceding completeness specialization makes the unchanged `C` complete
Noetherian local. The theorem `exists_adic_bound` applies exactly `hc` to
its actual antitone projection kernels with zero intersection, obtaining
`ker p_n ≤ m_C^(a+1)` for some tower index. `exists_toAdic` then produces an
actual surjective augmented test arrow from that stage to the ordinary
adic test with its exact original projection equation.

The provenance is internal descent through actual surjective maps, the
existing tower kernel formulas and quotient transitions. The explicit
cofinality premise remains an obligation. This result alone constructs no
compatible formal line-bundle system, proves no formal versality, and does
not discharge the exact field Picard-stack atlas target.
