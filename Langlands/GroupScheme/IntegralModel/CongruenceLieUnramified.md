# The congruence–Lie homomorphism under maximal unramified extension

`CongruenceLieUnramifiedCompatibilityStatement` uses a nonarchimedean
local field `F`, its separable inertia fixed field `K`, a smooth affine
integral model `M` over `𝒪[F]`, and the actual pullback
`M.baseChangeUnramified` to the integers of `K`. Both horizontal arrows
are `congruenceLieHom` for positive integers `n ≤ m ≤ 2n`. The upper
model is smooth by base change.

The group arrow is `rationalExtend F K G` restricted to the actual
congruence subgroups. A local coefficient map carries the powers of the
maximal ideal into the corresponding powers of the target ideal. The
resulting map on the congruence rings gives the commuting square of
spectrum maps. The proof of `baseChange_mem_congruenceKernelAt` compares
the reductions of the extended section and the unit through this square.
The generic image of the extended section is the extension of the original
generic point.

The Lie arrow is induced by `GenericLie.baseChange` on the two Lie-lattice
quotients. It extends dual-number tangent points. The lemma
`baseChange_mem_lieLattice` gives preservation of the lattices, and
semilinearity and the map on maximal ideals give preservation of their
powers. The statement equates the two composites of these specified
homomorphisms.

For this unramified extension the original maximal ideal generates the
maximal ideal upstairs, so the two congruence levels use the same powers
as in coefficient functoriality. The coefficient-ring and point arrows
are constructed for local coefficient maps because the containment of
maximal ideals suffices to define those arrows. The commuting square is
stated for the maximal unramified extension of `F`.

This is the unramified coefficient instance of Kaletha and Prasad,
*Bruhat–Tits Theory: A New Approach*, Proposition A.5.19(3) and Remark
A.5.20, pp. 642–643 (PDF pp. 673–674).
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
