# Weak base change of a prime-degree weak induction

Let `E/F` be the actual prime-degree Galois extension. Suppose the
cuspidal class `c` over `F` is weakly automorphically induced from the
cuspidal class `d` over `E`.
`CyclicInductionOrbitBaseChangeStatement` says that the isobaric multiset
of all arithmetic conjugates of `d` is a weak base change of the singleton
multiset of `c`. The orbit counts each automorphism once, including
multiplicities when two conjugates are equal. The witness for the
singleton comes from the given weak induction. For the orbit, transport
the actual spectral presentation of `d` along each automorphism, then
attach their finite sum to the multiset. The rank equation for weak
induction and `rank_galoisOrbit_of_isGalois` give the base-change rank.

At a good place of `F` the prime-degree extension is split or inert. At a
split place the induction polynomial is the product of the polynomials
at every place over it. The conjugates of any chosen upper place run
through that same fibre once. The residue degree in the base-change
operation is one. At an inert place the induction polynomial has the
form `P(X^ℓ)`, with `ℓ = [E:F]`. Each eigenvalue from `P` contributes its
`ℓ` roots, with multiplicities, to the spectrum of the induction. Taking
the `ℓ`-th power of every eigenvalue therefore gives `P(X)^ℓ` as a
polynomial. The unique upper place is fixed, so all `ℓ` conjugates have
the polynomial `P` there. These are the two checks of the actual cofinite
base-change predicate. The local unramified facts hold outside the finite
sets for the extension and the presentations.

The statement is a comparison using actual supplied cuspidal classes. In
the Harris prime branch, use it for the class obtained from the regular
induction premise. Once that class has a unitary realization, the orbit
lift's uniqueness identifies it with the orbit lift. Regularity and the
auxiliary component are obtained from their separate inputs.

Arthur–Clozel, *Simple algebras, base change, and the advanced theory of
the trace formula* (1989), `arthur-clozel-1989-base-change`, Chapter III,
Definition 6.1 and equations (6.1)–(6.2), printed pp. 215–216, describe the
split and inert induction spectra. The proof of Theorem III.6.2, equations
(6.5)–(6.6), checks the base-change spectra of the regular orbit at split
and inert places. The statement
here uses that unramified calculation in the direction from the supplied
weak induction to the orbit relation. Harris (1998), Proposition 4.8,
printed p. 203, TeX lines 1646–1664, uses III.6.4 to identify the weak
induction with the lift of the prime orbit.
