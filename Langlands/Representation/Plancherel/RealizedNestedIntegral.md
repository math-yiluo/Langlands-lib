# Weak integral restriction to a represented intermediate Levi

`HasIntegral.realized_restriction` evaluates the actual weak standard
integral on the represented intermediate group. The inverse quotient
homeomorphism sends each inner radical coordinate to its ambient image.
The outer half-character is trivial on the inner radical, by compact
subgroup containment of the target radical. The restriction formula thus
identifies each integrand with the ambient integrand times the same
factor used on the restricted section. Smooth-dual tests transport by
the equivalence of inducing groups.

`realizedNested_domain_eq_top` uses a surjective stages restriction and
this integral identity. It transports existence of representing vectors
and cancels the positive quotient-measure scale, giving full convergence
on the lower carrier with the prescribed lower measure.
