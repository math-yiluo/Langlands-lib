# Strong group gradings and their degree-zero ring

Worker 644. Internal algebra for the affine quotient construction in Task 7326.
The coaction is a ring map into a group algebra over any commutative ring;
the grading group is any abelian group, including torsion groups. `IsGrading`
records coefficient homogeneity and the finite homogeneous-sum identity.
`degreeZero` is the actual degree-zero subring and `component` its homogeneous
modules. The coaction projections identify the ring as the direct sum of these
modules.

`HasDualFamily m` asserts a finite partition of unity by products of degrees
`m` and `-m`; `IsStrong` asks for this in every degree. Each component is a
retract of a finite free module: the coordinate maps multiply by the chosen
dual elements, and the reconstruction map takes the corresponding linear
combination. The partition of unity proves that their composite is the identity.
The direct-sum decomposition then makes the whole ring projective over its
degree-zero subring.

This is internal derived algebra for the strong-grading part of SGA3,
Exposé VIII, sections 4–5, especially Theorem 5.1. It does not yet assert
existence of a scheme quotient or derive strong grading from a group action.

Source: SGA 3, Exposé VIII, Gille–Polo recomposition of 8 November 2009, §§4–5 (especially Theorem 5.1), registered as `sga3-expose-viii-gille-polo-2009`, source SHA-256 `06e43e0571d411cc5579975778fcc03c8ecaa67189248d1a053e61dc653af510`. The finite dual-family formulation and retract proof are internal derived content, not a claimed verbatim statement of Theorem 5.1.
