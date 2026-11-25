# Geometric point and field base change of the actual prime Tate trace

This internal helper generalizes the actual prime Tate trace to test objects and proves its invariance under geometric point and field base change. The rational trace comparison `GeometricEndomorphismTraceComparisonStatement`, a separate statement (proved as `geometricEndomorphismTraceComparison` in `Langlands.AbelianScheme.GeometricEndomorphismTraceComparisonProof`), remains an explicit premise of the final conditional corollary.

`primeEndomorphismTraceAt A T p` is the rational-linear trace of the actual action on `Tate.PrimeAdic.Rational A T p`. At the identity test object over a field it is definitionally the existing `primeEndomorphismTrace`.

`Tate.PrimeAdic.rationalTransport_homMap` extends the published geometric path naturality from integral abelian-scheme homomorphisms to the existing rationalized Hom action. Tensor induction and rational scalar compatibility give the extension. `primeEndomorphismTraceAt_path` uses it to identify the two actual operators by conjugation through the published prime path equivalence, then applies Mathlib's intrinsic trace-of-conjugation theorem.

`primeEndomorphismTraceAt_geometric` works over every connected locally noetherian base `S : Scheme.{u}`, every actual abelian scheme `A` on it, two geometric points whose algebraically closed coefficient fields lie in `Type u`, and every prime invertible on `S`. It chooses a path through the published `geometricPathExists` and `geometricFiberFinite` results and uses the published `torsionFiniteEtale` theorem. No finite-dimensionality premise is needed for intrinsic trace invariance.

`primeEndomorphismTraceAt_baseChange` records the pullback comparison at the mapped test object, using the constructed comparison in `Tate.PrimeBaseChange`.

`primeEndomorphismTrace_baseChange` combines pullback comparison and geometric point independence. For every morphism `b : Spec K ⟶ Spec k` between algebraically closed fields in `Type u`, an actual abelian scheme `A` over `Spec k`, every prime `p` nonzero in `k`, and every actual rational endomorphism `f`, it proves equality between the prime trace of `rationalBaseChangeHom b f` on the actual pullback and the prime trace of `f` on `A`. The global-section unit condition follows from the standard `ΓSpecIso`. This includes pullback along an identity morphism and does not treat that pullback as definitionally equal to `A`.

`geometricEndomorphismTrace_baseChange_of_comparison` additionally assumes the full existing `GeometricEndomorphismTraceComparisonStatement` and characteristic zero for both fields. Its conclusion is equality of the fixed rational geometric traces under the same actual rational Hom pullback. Injectivity of the rational embedding into `Q_2`, the assumed comparison at both schemes, and the proved prime trace base-change equality give the result. This theorem does not prove, weaken, or add hypotheses to the separate comparison target or the full Rosati positivity target.

The development retains the full universe `u`. Its provenance is an internal combination of the published actual Tate, geometric path, finite étale torsion and pullback constructions and elementary trace conjugation. It supplies no assertion about transport of the actual Rosati involution or reflection of nonzero rational homomorphisms.
