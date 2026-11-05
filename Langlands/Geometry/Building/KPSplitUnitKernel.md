# Character-valuation kernels of split tori

This internal construction compares the existing character-valuation kernel
of a finite split torus with the product of the corresponding kernels of
its coordinate multiplicative groups. It is valid over any field and for
any valuation with values in a linearly ordered commutative group with zero.

`mem_gm_characterValuationKernel` identifies the kernel for the actual
multiplicative group with the condition that its scalar unit has valuation
one. Every character of the multiplicative group is an integer power,
using the published `gmEndEquiv`; powers of a unit of valuation one
retain valuation one.

`splitPoint_decomposition` evaluates the published identity decomposition
as a sum of coordinate projection/cocharacter composites. In multiplicative
point notation it reconstructs each point as the product of its coordinate
cocharacter values. The equivalence `splitCharacterKernelEquiv` restricts
the categorical product-point equivalence to the actual character kernels.
Coordinate projections preserve the kernels by character restriction;
the inverse preserves them by the same result for each coordinate
cocharacter and closure under finite products.

This is derived infrastructure for the reduction to the multiplicative
group in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 2.5.12, printed p.89 (PDF p.120). It supplies no norm-surjectivity
or splitting-field-independence assertion.
