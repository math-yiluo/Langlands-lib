# Unramified characters of the actual general linear group

In the twisted Paley–Wiener interface, `IsUnramifiedCharacter ψ` means that
`ψ : G →* ℂˣ` is trivial on every compact subgroup. This module relates
that condition to the usual determinant-order characters for the Library's
actual `GL_n(E)` over a nonarchimedean local field `E`. These are derived
lemmas for the unramified twists in Henniart–Lemaire (2011), II.5.1, II.5.5, and
II.5.13, proof, printed p. 113. The implementation uses the Library's
`LocalFieldData.ofInstances E` and does not require characteristic zero.

## Determinant order

`determinantOrderHom E n` is the multiplicative homomorphism from `GL_n(E)`
to `Multiplicative ℤ` sending `g` to the normalized additive order of `det g`.
It is the composition of `GeneralLinear.determinant` with the field-unit
order `LocalFieldData.ordUnits`.

`determinantOrderHom_eq_one_of_mem_compact` says that every element of a
compact subgroup has order zero. The integer-valued order is continuous by
`AllField.RankinSelberg.continuous_ord_units` and continuity of the determinant.
Hence its image on the compact subgroup is finite, since the integers are
discrete. This image is a subgroup in multiplicative notation. Its elements
have finite order and therefore are the identity in the torsion-free group
`Multiplicative ℤ`.

## Character formula and kernel criterion

`eq_detOrderCharacter_of_isUnramified` takes an index `i : Fin n` (so the rank
is positive). Put `d` equal to the diagonal matrix with a uniformizer `ϖ` in
slot `i` and ones elsewhere. If `ψ` is unramified, then
`ψ(g) = ψ(d) ^ ord(det g)` for every `g`.

The Lean proof uses the actual Cartan decomposition `Cartan.exists_cartan`:
write `g = k₁ a(λ) k₂` with both `kᵢ` in the integral compact subgroup and
`a(λ)` diagonal with entries `ϖ ^ λⱼ`. Both `ψ` and `determinantOrderHom` are
trivial on the compact subgroup. In either homomorphism, the value on
`a(λ)` is the value on `d` to the sum of the exponents. This follows by
multiplying diagonal matrices with just one nontrivial slot and noting that
the single-slot matrices with the same nontrivial entry are conjugate by
permutation matrices. The determinant of `d` is `ϖ`, of order one.

`isUnramifiedCharacter_iff_detOrderKer_le` identifies unramifiedness with
containment of the determinant-order kernel in `ψ.ker` in positive rank.
The forward direction is the character formula. The converse uses order
zero on compact subgroups. The determinant-order kernel is equivalently the
kernel of the normalized determinant norm, since those two field-unit
kernels coincide (`LocalFieldData.ker_ordUnits`).

## Finiteness at fixed centre and product comparison

`finite_unramifiedCharacter_trivialCenter` proves finiteness of the subtype
of unramified characters of positive-rank `GL_n(E)` trivial on the entire
centre. The scalar matrix with scalar `ϖ` is central and has determinant
order `n`, so the character formula forces `ψ(d)^n = 1`. Evaluation at `d`
is injective by that same formula and hence embeds the subtype into the
finite Mathlib group `rootsOfUnity n ℂ`. This gives the finiteness of
Henniart–Lemaire's group `Ψ₂` in II.5.13, proof, printed p. 113. It does not
assert any normalization of an intertwining operator at a self-twist.

`isUnramifiedCharacter_pi_iff` compares unramifiedness in a finite product of
topological groups with unramifiedness on every coordinate group. In one
direction, a compact subgroup of a factor maps continuously into a compact
subgroup of the product under the single-coordinate inclusion. In the other,
project a compact subgroup to each factor. Every element of the product is
the product of its single-coordinate elements; they commute with each other
even when the factor groups are noncommutative. The character is one on each
such element, hence one on the product. This applies to the standard Levi
products by taking the groups to be their general linear factors.

## Source

G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
GL_n en caractéristique non nulle*, Mém. Soc. Math. France 124 (2011), II.5.1
and II.5.5 (the unramified character groups), and II.5.13, proof, printed
p. 113 (the finite subgroup of characters trivial on the centre). The source
does not give the Lean proof through the actual matrix Cartan decomposition.
