# A p-divisible group through its finite group schemes

`PDivisibleGroup` records a direct diagram of actual finite locally free
commutative group schemes over an affine base and its compatible reverse
multiplication maps. The transfer followed by inclusion factors actual
multiplication, and the inclusion and complementary transfer form the short
exact sequence on affine fppf tests. `HasHeight` asks for the ranks of the
actual finite coordinate algebras to be `p^(n*h)` on every base prime.

For a divisible formal module with scalar `p`, `pDivisibleGroup` uses its
represented kernels of `[p^n]`. The previously checked affine point formulas
give the exactness and multiplication identities. The affine global section
isomorphism identifies the actual coordinate rank of each level with the
rank of its original kernel model, which gives `pDivisibleGroup_hasHeight`.

The scalar factorization, exact sequence and rank powers follow the finite
level formulation in Tate, *p-Divisible Groups* (1967), §2.1, printed p. 161
(PDF p. 2), especially equation (2). This formulation works with the actual
finite group schemes and so can also be used with dual levels having an
étale part.
