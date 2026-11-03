# Local kernels and finite-quotient prescription reduction

Author: Worker 53. The imported generic finite-quotient character extension is
by Worker 1232.

This assembly implements the elementary and character-theoretic part of
Artin and Tate, *Class Field Theory* (AMS Chelsea, 2009), Chapter X, Section 2,
Theorem 5, printed p.80 (one-based PDF p.89). Registered source:
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The arithmetic finite-quotient assertion remains a hypothesis of this reduction.
Its conclusion is conditional on that arithmetic assertion.

`complexCharacterOpenKernel` is the actual kernel of the given continuous
complex character, bundled as an open subgroup. Positive bounded exponent makes
the character locally constant by the published
`isLocallyConstant_of_complexUnits_pow_eq_one`; its fiber at one is therefore
open. Factoring the character through the finite group of complex `n`th roots
of unity proves that its kernel has finite index. These generic constructions
retain an arbitrary domain universe.

The product character is killed by `n`: evaluating the power on the whole
product separates it into the power of the infinite character and the finite
product of the powers of the prescribed finite characters.

The reduction takes this open finite-index kernel as `U` in the arithmetic
finite-quotient statement. The exact preimage equality supplies the kernel
inclusion required by the imported generic extension theorem. That theorem
constructs a continuous character of the actual idele-class group killed by
`2 * n` and with the required product pullback. Evaluating the pullback equality
on the single selected finite factor proves each finite component identity;
evaluating it on the whole infinite factor proves the whole infinity identity.
No real sign component is discarded. There is no universe restriction.

To obtain the unconditional exact target, a proved arithmetic finite-quotient
theorem must be supplied. No global extension, Grunwald–Wang theorem, or
class-field-theory package is assumed as an instance.
