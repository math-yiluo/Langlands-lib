# Extending the compact identity comparison to the full local Lie operator

For each real or complex place, every matrix direction is the sum of an upper triangular direction and a skew-adjoint direction. The skew-adjoint comparison follows from differentiating the actual compact intertwiner. An upper triangular comparison at infinite compact identity then gives the identity comparison in every real matrix direction by additivity. Compact adjoint covariance extends the comparison to all compact arguments and hence to the scalar section.

`sectionPlaceLieAction` is the operator on a smooth compact-finite scalar section obtained by inserting the local complexified Lie generator into the actual adelic enveloping action. On a simple tensor with scalar one it is the real-direction section differential. Complex linearity shows that comparing these scalar-one directions suffices to compare the full complexified Lie action.

This is internal to the normalized scalar inducing model for `CuspidalIsobaricAutomorphyStatement`. Getz and Hahn (2024), §4.4, Definition 4.4.6, give the compact and Lie covariance setting, and §10.1, pp. 270–271 (PDF 282–283), give the scalar compact model. The Lean proof uses the Library's two matrix splittings, actual section enveloping action, and the established compact adjoint comparison.
