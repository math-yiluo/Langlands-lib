# Waldspurger's actual integral form on invariant families

Waldspurger (2003), VII.2, printed pp. 319–320, uses the weighted integral
of the inverse-formal-degree pairing. `GlobalForm.invariantGlobalForm`
is `GlobalForm.rawGlobalForm` on the two underlying smooth families. The
first slot is conjugate linear, and the second slot is complex linear.
`GlobalForm.invariantGlobalForm_action` restricts the proved invariance
under the actual product action. The existing one-orbit integrability
and finite-support formula apply to the underlying smooth families.

`GlobalForm.invariantGlobalPositiveForm` uses the same integral as its
inner product. It restricts the full-family positive form along the
injective intertwiner into the full smooth family, so its Hermitian,
nonnegative and definite properties use the exact `PositiveFormStatement`
with geometric finiteness, the maximal split torus, density
nonnegativity and density positivity on a dense set. The underlying
invariant space uses the conditional V.3 comparison.
