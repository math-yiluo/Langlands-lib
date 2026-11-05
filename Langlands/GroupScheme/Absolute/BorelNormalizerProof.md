# The Borel normalizer theorem on algebraically closed points

Worker 1369.

`Langlands.GroupScheme.borelNormalizer.{u}` proves the unchanged published
`Langlands.GroupScheme.BorelNormalizerStatement.{u}`. For every algebraically
closed field `k`, smooth connected affine group scheme `G` over `k`, and
existing Borel embedding `b : B ⟶ G`, the abstract normalizer in `G(k)` of the
image of `B(k)` equals that image. The universe and characteristic are
unrestricted. All structural inputs in the proof are imported published
theorems and are supplied internally.

The implemented proof adapts the author's published conditional
`borelNormalizer_of_structuralInputs` assembly. It uses strong induction on
the Lie dimension of the ambient group. For the supplied Borel, the height
construction supplies a maximal torus of `B`. The proved
`solvableMaximalTorusConjugacy` and the published torus correction lemma reduce
the problem to a rational point that normalizes both the Borel image and this
torus. The actual torus commutator endomorphism satisfies its pointwise
commutator formula. The proved `torusEndomorphismDichotomy` gives two cases.

In the scheme-surjective case, `solvableUnipotentFactorization` supplies the
rational unipotent-times-torus factorization for this same maximal torus.
The proof chooses the actual homogeneous quotient of `G` by the prescribed
Borel. Its projection is smooth, surjective and quasi-compact, and its fibers
on every relative scheme test are exactly the Borel cosets. Properness of
this quotient follows from
`IsBorelSubgroup.quotient_isProper_of_solvableProperFixedPoint` applied to the
proved `solvableProperFixedPoint`. This applies directly to the chosen Borel
quotient; no general parabolic quotient properness premise is required.

Smoothness gives reducedness of the Borel and ambient group. The published
`normalizer_range_carrier_base_eq_algClosed_points` then identifies abstract
point-normalizer membership with membership in the full subgroup-functor
normalizer. The proper-quotient surjective-commutator lemma proves normality
of the Borel range. The smooth normal quotient lemma constructs its affine
group quotient and uses the proper homogeneous quotient to show that the
Borel inclusion is an isomorphism. Its inverse gives a Borel preimage of
the normalizing point.

Otherwise the dichotomy supplies a closed copy of `Gm` killed by the torus
commutator. Its composite into `G` is closed and factors through `B`. If that
copy is central, the published smooth central multiplicative quotient branch
applies the induction hypothesis to the smaller quotient. If it is
noncentral, the published canonical smooth connected centralizer branch
applies the induction hypothesis in smaller Lie dimension. The latter uses
the exact proved `centralizerBorelIntersection` to obtain the Borel subgroup
inside the prescribed ambient Borel. Both branches give membership of the
corrected point. The torus correction lemma recovers membership of the
original point, and the induction yields the stated normalizer equality.

This is an internal composition of the imported Library constructions and
proofs. The target pair records its original-source correspondence with
Milne, *Algebraic Groups* (2017), Theorem 17.48, printed p.367 / PDF p.383.
This module proves precisely its published point form. The proof reuses the
author's assembly and surjective quotient mechanics, together with the
published structural proofs; it introduces no new source-backed statement.
The original statement and its imports are unchanged.
