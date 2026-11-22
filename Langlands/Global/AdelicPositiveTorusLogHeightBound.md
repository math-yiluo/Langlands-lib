# Heights of positive torus points in spanning character coordinates

`AdelicPositiveTorusLogHeightBoundStatement` takes a split torus \(T\) over a number field \(F\), a morphism \(i\colon T\to G\), a positive-rank matrix representation \(\rho\) of \(G\), and a set \(S\) of characters whose rational span is the full rational character space of \(T\).

There are constants \(C\ge 1\) and \(r\ge 0\) such that for every intrinsic positive point \(a\) of \(T\) and \(B\ge 0\) with
\(\big|\log|\chi(a)|_{\mathbb A}\big|\le B\) for all \(\chi\in S\), the adelic representation height of \(i(a)\) is at most \(C\exp(rB)\). The character norms are full idele norms and the representation height is the submultiplicative adelic height.

The proof uses a finite coordinate splitting of the torus. The log norm is additive in the character, so each coordinate log norm is bounded through its rational span expression in \(S\). The normalized idelic scalar formula divides this bound by the field degree to give the logarithm of the positive coordinate itself. It bounds the product of the maxima of each scalar and its inverse by an exponential in \(B\). The polynomial representation height estimate in these positive coordinates completes the proof.

This gives the upper comparison between height and log coordinates on the positive torus, as used in Mœglin–Waldspurger, §I.2.2(iv).
