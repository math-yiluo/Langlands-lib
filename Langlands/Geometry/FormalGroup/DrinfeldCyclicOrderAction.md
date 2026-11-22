# Extending a coefficient action to the division order

Let \(D\) be a central division algebra of reduced degree \(d\) over the local field \(K\). The construction uses an embedded degree-\(d\) unramified field \(E\) with integer ring \(C\), a scalar uniformizer \(\pi\), an automorphism \(\sigma\) of \(E/K\) of order \(d\), and a unit \(j\in D^\times\) with \(j^d=\pi\) and \(j\iota(a)=\iota(\sigma(a))j\). `integerCyclicAddCoordinates` expresses the actual division order as tuples over \(C\). The inverse sends \((a_i)\) to \(\sum_{0\le i<d}\iota(a_i)j^i\).

`liftCyclicOrder` takes a ring map \(f:C\to S\) to a semiring and an element \(t\in S\) with \(t^d=f(\pi)\) and \(t f(a)=f(\sigma(a))t\). In these equations \(\pi\) is mapped into \(C\) and \(\sigma\) acts on \(C\) by restriction. The resulting map from the actual division order sends each integral expansion to \(\sum_i f(a_i)t^i\). The conjugation relation computes the product of two monomials, and the power relation reduces the exponent to the basis range. The value lemmas verify the map on \(C\) and \(j\). Those values determine the map by the same integral expansion.

The construction specializes to the arithmetic Frobenius presentation in Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 B, printed p. 110 (PDF p. 4).
