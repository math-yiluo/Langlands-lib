# Support of constituents of an ordered normalized product

`Langlands.AllFieldBZ.CuspidalSupport.ProductConstituentSupportStatement`
concerns a nonarchimedean local field \(F\), an ordered shape \(B\), and
actual smooth complex representations \(A_i\) of the GL groups of its
blocks. For each factor, \(s_i\) is a supercuspidal support in the sense of
`IsSupercuspidalSupport`. This predicate includes irreducibility and
uses actual subquotients of normalized inductions of supercuspidal factors.

Every irreducible smooth subquotient of the actual normalized product
of the \(A_i\) has supercuspidal support \(\sum_i s_i\), with
multiplicities. The empty shape uses the empty multiset. This is the
support argument from exactness, transitivity and uniqueness in
Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)* (1980), §§1.1 and 1.10, printed
pp. 170–171 and 174 (`zelevinsky-1980-induced-ii`).
