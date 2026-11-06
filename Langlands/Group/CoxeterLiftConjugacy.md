# Coxeter relations from conjugacy of involutive lifts

This is an internal group-theoretic derivation. The label type, source group,
Coxeter group and target group may have independent universes.

For involutions A and B, conjugation of A by (AB)^k equals (AB)^(2k) A.
Consequently this conjugate is A exactly when (AB)^(2k) is one, and it is B
exactly when (AB)^(2k+1) is one. The Lean proof first establishes the identity
using the semiconjugacy A (AB)^(-1) = (AB) A and its power law; cancellation
then proves the two equivalences.

The main lemma takes a Coxeter system on W, homomorphisms q : N → W and
f : N → Q, and chosen lifts m of the simple reflections. It assumes their
f-images are involutions, and that each conjugacy q(n) s_a q(n)^(-1) = s_b
implies f(n) f(m_a) f(n)^(-1) = f(m_b). Under these explicit premises it proves
all Coxeter power relations among f(m_a), including diagonal and zero
exponents. No finiteness assumption is used.

The proof writes each Coxeter exponent as 2k or 2k+1. Its relation in W gives
the corresponding conjugacy by q((m_a m_b)^k). The supplied conjugacy law
transfers it to Q, and the same elementary equivalence gives the required
power relation there. This module constructs no algebraic-group lifts and
does not prove the root-generated centralizer statement; those applications
must justify its conjugacy premise.
