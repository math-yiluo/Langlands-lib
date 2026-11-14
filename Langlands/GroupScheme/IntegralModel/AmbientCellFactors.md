# Ambient integral factors from cell coordinates

This internal adapter concerns an integral model `M` over a domain `A` with
fraction field `K`, and two actual integral group homomorphisms `i` and `p`
into its group. It assumes that multiplication of their actual generic
fibres, followed by the supplied generic identification of `M`, is a
monomorphism. It does not require separate integral models, flatness,
smoothness, closedness, or connectedness for the factor groups.
`ambientCellFactorSections` projects the integral cell coordinate and sends
both original factor sections into the ambient integral model.

`ambient_cell_factors_eq` takes an integral section with an actual integral
binary cell coordinate. If two prescribed generic ambient points lie in the
images of the generic factor inclusions and multiply to that section's
generic point, they equal the generic images of the two original integral
coordinate sections.

The proof projects the integral coordinate to its two factors. The integral
product identity and naturality of changing a section's base identify their
generic product. Monicity of the generic multiplication identifies the two
generic coordinates separately. Naturality then gives the claimed equalities
in the ambient generic group.

`ambient_integral_factors_of_cell_lift` uses these two integral sections as
witnesses that both prescribed ambient factors belong to `M.integralPoints`.
This is an internal variant of `IntegralModel.CellFactors` that retains only
ambient integrality and avoids imposing integral-model structure on the
factors. It supplies neither the input cell coordinate nor the monicity
hypothesis, and it does not assert the host opposite-factor theorem.
