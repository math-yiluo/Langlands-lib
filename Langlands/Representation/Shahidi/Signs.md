# Shahidi's alternating diagonal and Whittaker sign conventions

This derived construction implements the alternating matrix and the associated
function transformations in Shahidi, *Fourier transforms of intertwining
operators and Plancherel measures for GL(n)* (1984), printed page 80 and
pages 102–103. The registered source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

On page 80, the diagonal entries of ε are (-1)^i with one-based indices.
The equal-rank integrand uses W₂(εg) although both input functions are in
ψ-models. The source's modified dual transform is W(ε w transpose(g⁻¹)).
The unequal-rank definition on pages 102–103 likewise uses this alternating
matrix on the smaller-rank factor. The elementary translation here is over
any topological field; it does not extend the analytic theorem to that scope.

`alternatingDiagonal n` is an actual invertible diagonal matrix, constructed
through the published `Iwasawa.diagonalUnits`. Its diagonal entries and its
square being the identity are proved. At positive rank n+1 it equals the
scalar matrix (-1)^(n+1) times the Library's
`Whittaker.characterChangeElement (-1) n`. The proof compares diagonal entries
and cancels an even power of -1; it also covers characteristic two.
The scalar factor commutes with every matrix, so its conjugation of the actual
upper-unipotent subgroup is the existing change-of-character conjugation.

`alternatingTranslate n` is the linear involution on all complex functions
obtained by left translation by this actual matrix. A function transforming
under the standard ψ unipotent character becomes a function transforming
under the inverse character. The proof moves the alternating diagonal past
the unipotent matrix and uses the published character-change identity.
`alternatingFunctional` carries out the same translation on an actual
representation's Whittaker functional, producing an inverse-character
functional. Its coefficient is exactly W(εg); there is no assumption of
irreducibility, admissibility, or a normed representation carrier.

`sourceDualFunction` composes alternating translation with the Library's
`Whittaker.dualFunction`. Its proved evaluation formula is the original
W(ε w transpose(g⁻¹)), with the all-positive long Weyl matrix. Alternating
translation reverses the unipotent character and the dual transform reverses
it again, so the resulting function retains the standard ψ character. This
is an identity of actual functions and equivariance conditions. It does not
identify the inverse-transpose pullback representation with the smooth
contragredient; that separate representation theorem is not assumed here.

Finally, `matrixCoefficient_alternatingDiagonal` computes the factor relative
to the Library's character-change diagonal. Given a character ω of Fˣ whose
scalar action on the supplied representation is explicitly proved, the
coefficient at εg equals ω(-1)^(n+1) times the coefficient at d₋₁g. The proof
uses the matrix factorization, representation multiplication, the supplied
scalar action, and linearity of the algebraic functional. This factor is a
translation identity in rank n+1; it is not, by itself, the central-character
factor in Theorem 5.1.

These intrinsic matrix and function identities do not assert the JPSS
functional equation, any quotient-measure change, existence of local
coefficients, or Shahidi's comparison theorem. Those remain separate units.
