# The centralizer of a semisimple point in a connected solvable group

`Langlands.GroupScheme.solvableSemisimpleCentralizer` proves the proposition
`Langlands.GroupScheme.SolvableSemisimpleCentralizerStatement` in every
universe. It applies to every representative of the scheme centralizer.

The proof follows the quotient argument of Milne, *Algebraic Groups* (2017),
Theorem 16.40, with induction on the length bound for the derived series of
rational points. In the commutative case the centralizer is the entire
group. The last potentially nontrivial derived term is represented by a
smooth connected closed normal subgroup. It is commutative by the next
bound on the derived series and unipotent because it lies in the kernel of
the split torus quotient.

After quotienting by this subgroup, the semisimplicity hypothesis passes to
the image. The comparison of centralizers is surjective on rational points
and its full kernel is the connected centralizer inside the commutative
unipotent subgroup. The fppf image of the comparison has the topology of
the quotient centralizer. The induction hypothesis and the connected
fibers therefore give connectedness of the original centralizer.

In the same induction, centralizing rational points are shown to meet every
coset of the first derived subgroup of the group of rational points. The
quotient step uses surjectivity on rational points and the fact that the
first derived subgroup maps onto that of a quotient. The split torus
quotient then shows that the smooth connected unipotent kernel times the
centralizer covers all rational points. Chevalley's theorem and the
Jacobson property give surjectivity of the multiplication morphism.

The retained source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, printed
pp. 338–339 for Lemma 16.39 and Theorem 16.40 and printed p. 336 for the
split torus quotient in Theorem 16.33.
