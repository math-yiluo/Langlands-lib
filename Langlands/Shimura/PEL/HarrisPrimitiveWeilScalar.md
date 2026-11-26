# The integral similitude of the primitive Harris Weil form

Fix a polarized Harris action \(X\) with a normalized Weil frame at an
algebraically closed point of characteristic zero. The base is
quasi-separated and the frame identifies the fixed integral adelic
source span with the full integral Tate image as in
`HarrisIntegralFrameCondition`. Let \(\mu\) be a primitive homomorphism
in the polarization ray as in `HarrisPrimitivePolarization`, so a
positive integral multiple of \(\mu\) is the given polarization.

`harrisPrimitiveWeil_exists_integralScalar` uses
`geometricFullIntegralBasis` and `finiteAdeleBasisOf` to write the actual
Weil form of \(\mu\) in the same frame. Its rational pairing is the
rescaled fixed source form of `harrisHodgePELPrimitiveAdelicForm` times
one finite-adele scalar. The formula is obtained by linearity in the
dual-valued map and the original frame compatibility. All its values
on the fixed integral lattice are integral because normalization
lifts those vectors to actual integral Tate vectors. The integer
values of the primitive source pairing span the unit ideal by
`harrisHodgePELPrimitivePairing_span`, so the common scalar is integral.

If the base is also connected and locally noetherian, every positive
integer is a unit, and the input `TorsionFiniteEtaleStatement` holds,
`harrisPrimitiveWeil_isUnit` proves that such an integral scalar is
a unit. If its residue at a prime vanished, it would be divisible
by that prime in the integral adeles. Thus every actual integral
Weil value of \(\mu\) would be divisible by the prime in the full
integral Tate twist. By `integralWeil_exists_nsmul_of_forall` and
surjectivity of full Tate evaluation, \(\mu\) would kill the prime
torsion at the indicated geometric point.
`exists_nsmul_eq_iff_levelMap_eq_zero` would then make \(\mu\)
divisible by the prime on the original abelian scheme, contrary to
primitivity. The nonzero prime residues give a unit of the product
of \(p\)-adic integers through `TateAdelicRank.fullScalarEquiv`.

`harrisPrimitiveWeilUnit` chooses the resulting unit of the integral
adeles. `harrisPrimitiveWeilUnit_spec` gives its formula on rational
vectors in the normalized frame. `harrisPrimitiveWeilUnit_integralAlong_nsmul`
gives the formula on the actual full integral Tate vectors for every
natural multiple of \(\mu\). On the two source vectors the integral
Weil value is the image under the integral twist basis of the source
pairing value times that multiple and the integral unit.

This is a derived comparison for the normalized polarization and
adelic alternating data of Kottwitz, *Points on Some Shimura Varieties
over Finite Fields*, §5, printed pp. 389–391 (PDF pp. 17–19).
The primitive form and the twist basis use the Library's actual
integral Harris and Tate constructions.

Source `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`,
§5, printed pp. 389–391 (PDF pp. 17–19).
