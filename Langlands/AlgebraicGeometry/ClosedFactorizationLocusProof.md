# The universal closed-factorization locus

Author: Worker 445, with the affine coefficient adapter supplied by Worker
1150 and the full-product locality and gluing constructions supplied by
Worker 146.

`ClosedFactorizationLocusProof.closedFactorizationLocus` proves the exact
published proposition
`Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement.{u}`. The
statement and its imports are unchanged. For every commutative base ring
`R` in the arbitrary universe `u`, an affine flat object `X` over `Spec R`
whose coordinate module becomes projective after a faithfully flat algebra
extension, and any closed immersion `d : D ⟶ X ⊗ Y`, it constructs a closed
immersion `i : Z ⟶ Y` satisfying

```lean
∀ (T : Over (Spec R)) (t : T ⟶ Y),
  (∃ z : T ⟶ Z, z ≫ i = t) ↔
    ∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ t.
```

The witnesses `Z` and `i` are chosen before the tests. The morphism on the
right is the entire product `id_X × t`, with its scheme structure. Tests
and targets may be nonaffine and nonreduced, and neither projectivity nor
the faithfully flat algebra is restricted by finite generation or finite
presentation. There is no representability premise on this conclusion.

The implemented proof first establishes the helper `affine`, where `Y`
is affine but tests are already arbitrary:

1. Choose the algebra `B` from
   `HasFpqcProjectiveCoordinateModule X`. Its structural spectrum map
   `f : Spec B ⟶ Spec R` is flat and surjective.
2. Pull back `X`, `Y` and the closed immersion along `f`.
   `AffineCoordinateBaseChange.projective` identifies the actual relative
   coordinates of the changed source with the projective tensor module.
   `ClosedFactorizationBaseChange.baseChangedMap` supplies the actual
   closed immersion into the product of the changed schemes.
3. Apply
   `AffineClosedFactorizationLocus.affine_closed_locus` over `B`. This
   constructs a closed representative for every affine test scheme from
   the coefficient ideal of the closed immersion.
4. Regard full-product factorization as the scheme sieve
   `FullProductFactorization.sieve`. It is fpqc closed because
   factorization through a monomorphism descends in a subcanonical
   topology. The comparison `mem_iff_over` identifies its scheme
   formulation with the displayed formulation in `Over`.
   `ClosedSieveAffineTests.allTests_of_affineTests` extends the
   coefficient-locus criterion to every scheme test using Zariski covers.
5. The projection `Y ×[Spec R] Spec B ⟶ Y` is a flat surjective morphism
   between affine schemes.
   `ClosedFactorizationBaseChange.factors_iff` identifies the criterion
   upstairs with the original sieve after composition with that
   projection, on every test. Apply
   `AffineFpqcClosedLocusDescent.affine` to descend the closed
   representative. This uses flat ideal descent and subcanonical gluing
   of lifts, without a finite-presentation hypothesis.
6. View the resulting scheme and inclusion as objects and a morphism over
   `Spec R`. `exists_over_lift_iff` recovers the structural triangle of
   each lift from its equation with the inclusion. This gives the
   all-test equivalence asserted by `affine`.

For the final theorem, affineness of the structural morphism over the
affine base gives `IsAffine X.left`. The helper `affine` supplies
`FullProductFactorization.AffineTargetRepresentable X`, by retaining its
criterion on affine tests. The theorem
`FullProductFactorization.of_affine_targets` then restricts the original
closed immersion to every affine open of `Y`, applies those affine
representatives, and glues them to a closed immersion over `Y`. Its
closed-sieve argument gives the criterion on every test scheme. This
proves exactly the requested proposition. The structural flatness premise
is retained in that proposition; this implementation does not need to
invoke it separately in the affine reduction.

The source and extraction of the generic geometric statement from
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition,
Proposition A.8.10(1), printed pp.547–549, are documented in the published
statement and the coefficient-construction modules. This proof follows
the coefficient and faithfully flat reduction route, while performing
gluing through fpqc closed sieves and the Zariski topology. It imports
the algebraic and geometric helpers by Lean name. No group law, group
action or subgroup comparison enters the proof.
