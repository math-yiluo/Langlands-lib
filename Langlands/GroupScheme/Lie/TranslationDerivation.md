# Coordinate derivations from actual infinitesimal translation

This internal construction is derived from the actual group law, coefficient
extension of dual-number identity kernels, and the published equivalence
between identity kernels and derivations of affine coordinates at the identity.
It uses no external structural theorem about algebraic groups.

Let `R` be any commutative ring and `G` an affine group scheme over `Spec R`.
No smoothness, finite type, reducedness, connectedness, field, or characteristic
assumption is needed. For an actual identity-kernel point `X` over `R`, and
an actual point `g` over any `R`-algebra `A`, `infinitesimalTranslate G X g` is
the product of the coefficient extension of `X` with the constant dual-number
lift of `g`, in that order. Its reduction is `g`, and it is natural under all
maps of test algebras.

Apply this operation to the universal point of the chosen coordinate algebra.
Its coordinate map has constant part the identity. The epsilon coefficient is
therefore a derivation, `translationDerivation G X`, from the coordinate
algebra to itself. The proof identifies its dual-number lift with the original
translation map. Naturality and the universal point then prove the same
coordinate identity at every affine test point: its infinitesimal coefficient
is the point's coordinate homomorphism applied to this derivation.

For any global coordinate derivation `D`, `derivationAtIdentity G D` evaluates
its values by the coordinate augmentation. It is a derivation into `R` with
the augmentation action of the coordinate algebra. The existing actual
kernel–derivation equivalence gives `kernelOfDerivation G D`; its infinitesimal
coordinates are exactly those evaluated values.
The local augmentation algebra structure is installed only on the ground
ring `R`; global derivations retain the ordinary multiplication action of the
coordinate algebra on itself.

Evaluating `translationDerivation G X` recovers `X`. This follows by applying
the coordinate formula at the identity, where translating its constant lift
is precisely `X`.

This module does not assert that every global derivation is translation
invariant. It does not yet compare prime-power iterates with algebraic
representation differentials, construct semisimple replacement, or prove
Cartan generation.
