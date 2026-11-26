# Harris frames under rational rescaling

Fix the Harris CM data, an actual positive-auxiliary polarized action `X` over a
scheme `S`, and a second actual polarization `lam` for the same family and
dual witness. Assume the rationalization of `lam` equals the rationalization
of the polarization of `X` multiplied by a unit `q` of `ℚ`.

`harrisRescalePolarization` puts `lam` on the same action object and keeps the
same dual data. The relation with the positive auxiliary involution follows
from `isInvolutionCompatible_rationalUnitMultiple_iff`, since the rational
scalar commutes with both actions.

For quasi-separated `S`, the relative finite Weil transition data, the
comparison of rational profinite integers with the finite adeles and a
field-valued point of `S`, `harrisRescalePolarizationFrameEquiv` identifies the
actual adelic Weil frames for the two polarizations at that point.
`rationalWeilAlongHom0BilinearMap_smul` scales the alternating form on the
rational Tate group by `q`. The diagonal rational scalar acts by its image in
the finite adeles on the Tate twist, by
`TateTwist.Divisibility.finiteAdeleAction_diagonal`. `FormIso.transport` uses
the identity on the rational Tate group and the resulting scalar
automorphism of the twist. Its formula `FormIso.transport_apply` gives the
same evaluation of the underlying map on the original adelic source.
