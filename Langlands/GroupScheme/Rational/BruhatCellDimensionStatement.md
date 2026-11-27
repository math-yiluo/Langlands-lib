# The relative-root dimension of a rational Bruhat factor

Let \(G\) be connected reductive over a field \(k\), and let \(T\) be a
maximal \(k\)-split torus. Fix a generic cocharacter \(\nu\) of \(T\).
The canonical affine dynamic subgroups \(U\) and \(V\) use \(\nu\) and
\(-\nu\), respectively, composed with the torus inclusion.
For \(n\in N_G(T)(k)\), `BruhatCell.factor` is the
scheme-theoretic intersection \(C=U\cap nVn^{-1}\).

`Langlands.GroupScheme.RationalBruhatCellDimensionStatement` asserts
that the structure map of \(C\) is smooth of relative dimension

\[
\sum_{\substack{\alpha\in\Phi(G,T)\\
                 \langle\alpha,\nu\rangle>0\\
                 \langle w^{-1}\alpha,\nu\rangle<0}}
     \dim_k\mathfrak g_\alpha ,
\]

where \(w\) acts on characters by `weylAction i n` and
\(\mathfrak g_\alpha\) is the actual adjoint weight space over \(k\).
The formula uses the full relative root set and includes each occurring
multiple that satisfies both sign conditions. The field can be imperfect.

## Source

Borel–Tits, *Groupes réductifs* (1965), §5.13(1)–(2), printed p.99
(PDF p.46), identifies the opposite factor for \(w\) with the subgroup
for \(\Phi^+\cap w\Phi^-\) and with \(U\cap nVn^{-1}\).
The proof of Théorème 5.15 uses the factor in the rational Bruhat
decomposition, printed pp.100–101 (PDF pp.47–48).
Milne, *Algebraic Groups* (2017), §25.13, printed p.548 (PDF p.564),
defines the relative roots by the adjoint weight spaces over \(k\).
The dimension formula is derived from the weight-space description of
the Lie algebra of the actual intersection.

Registered originals `borel-tits-1965-groupes-reductifs`
(`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`)
and `milne-2017-algebraic-groups`
(`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
