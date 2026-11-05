# Compact induced Hermitian forms and actual integral duality

This derived comparison connects the existing probability-normalized integral
duality with the Hermitian forms on the two actual normalized inductions.
Its source context is Waldspurger (2003), I.3, printed p.243 (PDF p.9),
the integral identification of the smooth dual of normalized induction,
and V.2, printed p.293 (PDF p.59), the induced Hermitian and tensor forms.
The source convention is conjugate linear in the first argument.

The construction retains the existing actual induced representations,
`CompactInduction.integralDualEquiv`, and intrinsic compact Haar probability.
The ambient locally compact, second countable nonarchimedean group, closed
subgroups `P` and `U`, semidirect decomposition of `P` by `M` and `U`,
local compactness of `P`, compact open `K` with `G = P K`, ambient
unimodularity, full parabolic modulus and Borel structures are explicit.
The duality comparison additionally assumes Hausdorff topology, continuous
Levi projection and admissibility of the inducing object. Compact-open
cofinality for the Hermitian identifications is explicit. The group and
representation carrier universes are independent.

`hermitianMap` applies the inducing Hermitian functional at every point of an
induced section. The half modulus is positive real, so conjugating it leaves
it unchanged; this proves the covariance of the new section. The uniform
open stabilizer of the original section also stabilizes its pointwise image.
Additivity and conjugate linearity follow pointwise. No inducing or induced
irreducibility is used.

`hermitianMap_inner` computes the induced dual form on two such sections.
The smooth-dual form reverses the two vectors after inverting the Hermitian
identification, so the result is the original compact induced form with
its arguments reversed.

`induced_isAdmissible` supplies the already proved compact-quotient induction
admissibility result, with compactness of the quotient obtained from the
supplied compact representatives.

`integralDualEquiv_toSmoothDual` uses the defining probability integral of
the existing dual equivalence. The pointwise Hermitian section and the
induced Hermitian functional have the same pairing with every induced vector.
Equality of linear functionals and invertibility of the existing equivalence
therefore identify them.

`integralDualEquiv_form` proves that pulling back the actual compact form on
induction of the smooth dual along this dual equivalence gives exactly the
Hermitian smooth-dual form of the first induction. It writes both smooth
functionals as Hermitian functionals using admissibility, applies the
pointwise comparison and then the computed anti-isometry. This proves
the isometry of these exact forms without applying Schur's lemma to an
induced representation.

All integrals here use the existing probability `CompactInduction.measure K hK`.
No identification with an arbitrarily chosen Bruhat-density measure is used.
Tensor transport, representative comparisons, realization of the hypotheses
on reductive rational points, spectral families and the Plancherel theorem
are separate obligations.
