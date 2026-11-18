# Laurent fractions invariant under scaling a block of variables

The product Laurent algebra has two blocks of integer exponents. `firstBlock`
includes Laurent polynomials on the first block by extending each exponent by
zero. `specialize` substitutes complex units into the second block. The
specializations detect zero because each coefficient in the first block is a
Laurent polynomial in the second block, and the Library's finite Laurent
evaluation theorem detects such a polynomial on all complex unit tuples.

`exists_firstBlock_fraction_of_fixed` applies to a fraction fixed by every
second-block scaling, with compatible actions on the Laurent algebra and its
fraction field. For a presentation \(p/q\), fixedness gives
\(\sigma_c(p)q=p\sigma_c(q)\). Choose a specialization \(a\) with \(q(a)\ne0\).
Evaluating the cross-multiplication identity at \(a\), and varying \(c\), gives
\(p(d)q(a)=p(a)q(d)\) at every specialization \(d\). Detection upgrades
this identity to equality in the Laurent algebra. The original fraction is
therefore the first-block fraction \(p(a)/q(a)\).

This is a derived algebraic lemma for the unramified-character coordinate
descent. Both blocks may have dimension zero.
