# Smoothness and geometric connectedness over the centre

Let \(A\) be a flat algebra over a discrete valuation ring with uniformizer \(t\), and let \(I\) contain \(t\). Assume \(A/(t)\) and \(A/I\) are regular rings. For each prime of \(A/I\), localize \(A\) at its inverse image. The two quotient local rings are regular. `exists_lifted_regular_generators` supplies equations for the localized centre, and the polynomial chart computation identifies the reduced dilatation, after that localization, with a polynomial algebra over the local centre.

`exists_blowupResidue_fieldEquiv` applies this comparison to any field-valued point of the centre. Its field map factors through localization at its kernel. Tensoring the local polynomial chart with the field identifies the fibre coordinate ring with a polynomial algebra over the field.

If \(A\) is of finite type over the base, `blowupResidue_smooth` obtains flatness over \(A/I\) from the polynomial descriptions at maximal localizations. The reduced algebra is of finite presentation over the Noetherian centre. The flat finite-presentation fibre criterion gives smoothness. `blowupResidue_geometricallyConnected` uses the tensor-product description for every field-valued point and connectedness of the spectrum of a polynomial algebra over a field.

The result is the affine version of the special-fibre step of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Appendix A.5.10, printed p. 635. `isRegularRing_of_smoothSpec` supplies the regularity hypotheses for the affine schemes smooth over the residue field.
