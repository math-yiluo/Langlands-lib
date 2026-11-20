# Integration in a product chart for regular orbits

Let `p : X → B` be continuous, with `B` Hausdorff and having a compact open neighborhood basis. Suppose that, over an open subset `V` of `B`, a homeomorphism identifies `p ⁻¹' V` with `V × Q` and identifies `p` with projection to the parameter. Assume that `Q` is Hausdorff and its measurable space contains the open sets. `RegularOrbitalChartIntegrationStatement` asserts that a Schwartz–Bruhat test on `X` restricts to integrable slices on `Q` for a fixed measure finite on compact sets. The integrals are locally constant on `V`.

The proof `integrable_locallyConstant_orbitChart` chooses a compact open neighborhood `C ⊆ V` of a parameter `b`. Since `C` is closed in `B`, the restricted chart identifies `C × Q` with the closed subset `p ⁻¹' C` of `X`. Pullback to this closed embedding preserves compact support and local constancy. The Library's `SchwartzBruhat.sliceSnd` and `SchwartzBruhat.partialIntegral` then give integrability and local constancy over `C`.

This is a derived analytic lemma for the regular slice approach to Henniart–Lemaire (2011), I.2.7, printed p. 20. The chart and fixed measure are inputs. For an orbital application, `Q` is a fixed centralizer quotient and the chart evaluates the twisted conjugate of a representative of each parameter.
