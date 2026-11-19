# Linearity of the constant term and its exponent projections

The functions possessing a right-finite normalized constant term form the
submodule `standardConstantTermDomain`. The constant term on this domain is
the linear map `standardConstantTermLinear`, by the existing addition and
scalar laws for right-finite constant terms. Its image lies in the sum of
the weak and positive exponent spaces by `mem_sup_of_isRightFinite`.

The uniqueness law `weakPart_eq_of_mem` proves `weakPartLinear` on that
sum because both exponent spaces are submodules. Subtracting the weak
projection from the submodule inclusion gives `positivePartLinear`.
Both maps act on exactly the earlier function-valued parts.
