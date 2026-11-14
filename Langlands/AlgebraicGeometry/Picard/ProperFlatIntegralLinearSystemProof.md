# The linear system of an invertible module on a proper flat family with integral fibres (proof)

Authors: Worker 5705.

Worker 5705 wrote this proof for Task 5705 (`07219dde-fd87-48cf-83be-db16cbb3707c`). It proves the
published statement `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement`
(the target also of Task 5987). It contains no `sorry` and no new axioms; the axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Theorem

`Langlands.AlgebraicGeometry.Picard.properFlatIntegralLinearSystem :
ProperFlatIntegralLinearSystemStatement.{u}`.

## Route

The proof follows Kleiman, *The Picard scheme* (arXiv math/0504020v1), Subsection 3.10,
Exercise 3.11, Definition 3.12, Theorem 3.13 and Exercise 3.14 (pp.24–26), with the test category
of locally noetherian schemes of p.15. The helper modules are listed with their roles.

1. **Zero loci of sections** (`SectionZeroIdeal`, `SectionZeroIdealFrames`, `SectionZeroIdealUnits`,
   `SectionZeroIdealDual`, `LocalEquationCartier`, `RelativeEffectiveLocal`,
   `CommutativeAlgebra/FibrewiseRegularFlat`, `CommutativeAlgebra/FibreLocalDomain`,
   `FibreRegularSection`): the zero ideal sheaf of a section of a line bundle, its behaviour under
   pullback, the identification `O(Z(σ)) ≅ L` for regular sections, and Kleiman's Lemma 3.4
   (iii) ⇒ (i): a section that is nonzero on every fibre of a flat family with geometrically
   integral fibres cuts out a relative effective divisor.
2. **The module `Q`** (`CommutativeAlgebra/CokernelDualHom`, `LinearSystemCechModule`,
   `LinearSystemCechNaturality`, `LinearSystemFibres`): over `Spec R` with `R` noetherian, the
   Library's Čech projective representative `K₀ → K₁ → K₂` of `M` gives
   `Q = Coker(K₁^∨ → K₀^∨)` with `Hom_R(Q, A) ≅ Γ(Y_A, M_A)` naturally in `R`-algebras `A`
   (3.10.1).
3. **The Grassmannian model over an affine base** (`RingTheory/Grassmannian/LineQuotientCoordinates`,
   `BaseChangeMaps`, `PointIdealGluing`, `LinearSystemUniversalDivisor`, `LinearSystemAffineDivisor`,
   `LinearSystemAffinePoints`, `LinearSystemAffineInjective`, `LinearSystemAffineExistence`,
   `PushforwardLineBundle`, `LinearSystemAffineBundle`, `LinearSystemAffineTheorem`): `P(Q)` is the
   Library's representing scheme of the Grassmannian of rank-one quotients of `Q`, proper over
   `Spec R`; the universal divisor `W` is glued from zero loci over the charts; it is relative
   effective Cartier; `O(W) ≅ M ⊗ N` for a line bundle `N` on `P(Q)` (Lemma 2.7 with Exercise 3.11);
   and every divisor of the linear system over a locally noetherian test is the pullback of `W`
   along exactly one point (Theorem 3.13).
4. **Gluing over the base** (`IdealSheafGluing`, `LinearSystemUniversality`, `LinearSystemGluing`,
   `LinearSystemGluingUniversal`, `LinearSystemTransport`, `LinearSystemAssembly`): the affine models
   over the affine opens of `T` are universal over those opens, hence glue to a universal family
   over `T` with a proper structure map.
5. **Flatness** (`CommutativeAlgebra/CokernelDualProjective`, `RingTheory/Grassmannian/LineChartFlat`,
   `LinearSystemCechExact`, `LinearSystemFlatness`): if `H¹(Y_t, M_t) = 0` for all `t`, then `Q` is
   projective over every affine open, and the Grassmannian of rank-one quotients of a finite
   projective module is flat and locally of finite presentation; with `H⁰(Y_t, M_t) ≠ 0` it is
   surjective (Subsection 3.10, (v) ⇒ (i)).

The statement's conclusions are obtained as follows: items 1 and 2 (properness, invertibility of
`N`, `O(W) ≅ M_Λ ⊗ N_Λ`) from steps 3–4; item 3 (the characterization of pullbacks of `W`) and
item 4 (uniqueness) from `glued_exists_point`, `LS.comap` and `glued_eq_of_comap_eq`; item 5 from
step 5 through `LinearSystemGluing.properFlatIntegralLinearSystem_of_localFibreFlatness` and
`LinearSystemCechModule.localFibreFlatness`.

## Dependencies outside Mathlib

Library: the Čech projective representative (`NoetherianCechProjectiveRepresentativeProof`), the
Grassmannian representability and properness (`RingTheory/Grassmannian`), relative effective
divisors and their base change (`RelativeEffectiveDivisorBaseChangeProof`), W22's Picard-class
lemmas (`PicardHilbertPiecesRepresentabilityReduction*`), semicontinuity
(`ProperFlatFibreCohomologySemicontinuityProof`), the base-change invariance of fibre cohomology
dimensions (`ProperFibreCohomologyDimBaseChangeProof`), the Čech–derived comparison in degree one
(`Modules/CechHSuccBridge`), the gluing template `SmoothFamilyOpenCoverGluing`, and the FLT port
(frames, ideal-sheaf gluing, `p_*𝒪 = 𝒪`).
