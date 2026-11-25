# One-place Lie derivatives of the actual scalar coefficients

`coefficientPlaceDifferential` acts on the scalar Levi coefficients by summing the chosen local Lie operators on the realized block factors. Each summand keeps the other blocks fixed, and the coefficient evaluation equivalence transports the resulting operator to scalar functions.

For a real or complex matrix direction inserted at one infinite place, the existing adelic coefficient differential agrees with this sum using the diagonal block of that matrix in each factor. Diagonal block projection commutes with one-place insertion, and complexification sends each resulting real direction to its actual local Lie generator. The two tensor sums are then equal by the formula for a one-slot endomorphism.

This is internal to the Lie-action comparison toward `CuspidalIsobaricAutomorphyStatement` (automorphy of isobaric sums of cuspidal representations at every place). Getz and Hahn (2024), §4.4, Definition 4.4.6, give the compact and Lie differentiation setting, and §10.1, pp. 270–271 (PDF 282–283), gives the normalized scalar inducing model. The Lean proof uses the Library's actual block coefficient differential and place Lie actions.
