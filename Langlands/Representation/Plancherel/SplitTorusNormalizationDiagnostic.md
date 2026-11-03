# Absolute-value characters and the rank-one normalization diagnostic

This companion uses the existing residue-normalized absolute value of an actual
algebraic character. The map to complex units is the existing
`positiveUnitsToComplex`; the field, valuation, actual rational points and
character/cocharacter lattices remain the shared constructions.

For an actual split torus and an integral algebraic character `α`, its
normalized absolute-value character equals the positive character of the real
parameter `1 ⊗ α`. Its normalized real part is therefore `1 ⊗ α`; its raw
natural-logarithm real part is `(-log q) • (1 ⊗ α)`. The implemented proof
uses the defining character evaluations of the existing centralizer valuation
and rational norm logarithm, then the previously proved positive-character
inverse law.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, V.2.3 and V.2.5
(printed pp.105–107/PDF pp.111–113) and V.3.19–V.3.20
(printed pp.115–116/PDF pp.121–122). These internal diagnostic constructions
check the discrepancy between the fixed positive valuation and `q^(-s)`
parameter on the one hand, and the later printed raw logarithm on the other.

On the actual one-coordinate split torus, the coordinate character has integer
coordinate one and the existing order-one uniformizer point has positive
valuation coordinate one. The finite-coordinate pairing therefore evaluates
its normalized real parameter to **1**. Its raw parameter evaluates to
**`-log q`**, and a separate theorem computes the literal natural logarithm
of the character's norm at that same point as **`-log q`**. Thus the exact
factor is checked without identifying the two parameters or changing a chamber
sign. No characteristic or field-universe restriction is added.
