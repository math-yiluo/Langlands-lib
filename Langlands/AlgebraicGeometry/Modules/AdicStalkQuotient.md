# Actual adic thickening stalks as quotients

This internal derived comparison computes the kernel of the actual projection
from `X ×[Spec R] Spec (R/I^(n+1))` to `X`, both on affine sections and on actual
stalks. The stalk kernel is the `(n+1)`st power of the extension of `I` along
the actual base-ring map to the ambient stalk. The associated quotient algebra
equivalence uses the actual scheme stalk map as its algebra structure.

The affine calculation uses the pushout of sections for the actual pullback
square, and reuses the Library's generic pushout-kernel theorem from the
Anthropic FLT port. The quotient spectrum's map on global sections is the
ring quotient map transported across `ΓSpecIso`. Localization of the affine
kernel then uses `ClosedImmersion.ker_stalkMap_eq_map`; compatibility of
germs with the actual structure map identifies the extended base ideal.
The first isomorphism theorem supplies the quotient algebra equivalence.

`pullbackStalkQuotientEquiv` compares the stalk of the ordinary pullback of
any actual module sheaf `M` with `M_x / (I O_{X,x})^(n+1) M_x`, at a point of
the thickening mapping to `x`. It is linear over the original ambient stalk,
with the action on the pulled-back stalk given by `relativeStalkModule`.
It composes `StalkPullback.pullbackStalkTensorEquiv`, restricted scalars,
the tensor product of the inverse quotient algebra equivalence with the
identity of `M_x`, and Mathlib's `quotTensorEquivQuotSMul`.

The base section and stalk maps are defined from the actual structure morphism
and `ΓSpecIso`, rather than from an unrelated algebra structure. All results
hold for arbitrary commutative `R`, ideal `I`, actual scheme `X` and module
sheaf `M`, in arbitrary universe `u`. They require no properness, noetherianity,
completeness, finite presentation, flatness or compatibility hypothesis.
This unit does not produce lifts of points, reflect rank one, or algebraize a
formal system; those remain separate geometric obligations.

The unchanged `baseSectionHom` definition is shared through
`Modules/AffineBaseSections`, with its original namespace and interface.
