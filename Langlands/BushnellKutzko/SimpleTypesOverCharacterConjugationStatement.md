# Conjugate simple characters and the types over them

Let \(F\) be a nonarchimedean local field, \(V\) an \(F\)-vector space of
finite dimension \(N\ge 1\), and \(\psi_F\) an `IsBKAdditiveCharacter`.
Take two simple strata \([\mathfrak A,n,0,\beta_i]\) on the same principal
order, with simple characters \(\theta_i\in C(\mathfrak A,0,\beta_i)\).
Write \(H_i=H^1(\beta_i,\mathfrak A)\) and \(J_i=J(\beta_i,\mathfrak A)\).
For \(u\in U(\mathfrak A)\), the Lean hypothesis is the equality of
subgroup–character pairs after `CharacterPair.conj u`. It says
\(H_2=u^{-1}H_1u\) and \(\theta_2(h)=\theta_1(uhu^{-1})\) on all of \(H_2\).

`SimpleTypesOverCharacterConjugationStatement` asserts \(J_2=u^{-1}J_1u\)
and transports every simple type over \((\mathfrak A,\beta_1,\theta_1)\)
to a simple type over \((\mathfrak A,\beta_2,\theta_2)\). The transported
representation of \(J_2\) is \(j\mapsto\lambda(uju^{-1})\).
The field, vector space and representation carrier have independent
universes.

The hypotheses are symmetric under exchanging the indices and replacing
\(u\) by \(u^{-1}\). Transport preserves representation equivalence, and
applying the assertion in the reverse direction gives its inverse on
equivalence classes. This gives the bijection of BK94 (3.4).

## Source

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), Proposition (3.4), printed p. 124, with the continuation of its
proof on p. 125 (volume PDF pp. 137–138).
Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
