# Base change of the rank-one spherical Hecke algebra

The top standard double coset represents the uniformizer scalar matrix. Its
Satake scalar is the product of the coordinates, so raising each coordinate
to the \(l\)-th power raises this scalar to the \(l\)-th power. Satake existence
over \(E\) and separation over \(F\) identify its base change with the \(l\)-th
convolution power of the top standard double coset over \(F\). This part
applies in every positive rank.

In rank one, the spherical subgroup consists of matrices whose determinant
has order zero. Its double cosets are thus indexed by all integer orders.
The compact-open Hecke double-coset multiplication gives a unit for each
order, with the group law given by addition. The Laurent exponent \(m\)
maps to \(lm\), since the base-change homomorphism respects powers of units.
The double-coset elements span the Hecke algebra. Applying linearity yields
the formula `IsUnramifiedBaseChangeHom.rankOne_apply` at every base element.
At order \(lm\) the image takes the original value at order \(m\), and at
orders outside \(l\mathbb Z\) it vanishes.

This is the rank-one group-algebra description in Henniart–Lemaire,
I.6.11, printed p. 52, implemented with the Hecke corner and Satake
character identity of I.1.3.
