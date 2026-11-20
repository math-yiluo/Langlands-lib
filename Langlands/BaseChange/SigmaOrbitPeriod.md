# Period of a local representation with trivial Galois stabilizer

`SigmaOrbitPeriodStatement` says that pullback by a power of a field automorphism fixes a representation with trivial Galois stabilizer up to equivalence exactly when the order of the automorphism divides the exponent.

In `conjugate_equiv_iff_orderOf_dvd`, an equivalence to the pulled-back action makes the power the identity by triviality of the stabilizer. The order criterion gives divisibility. For the converse, divisibility makes the power the identity, and the identity linear map intertwines the two actions.

For a generator of a finite cyclic Galois group, its order is the field degree. The lemma then supplies the period condition in `CuspidalSigmaLiftExistenceStatement`, which expresses the case \(a=1\) of Henniart–Lemaire (2011), II.4.12, Remarque, printed p. 97. Preservation of supercuspidality under a continuous field pullback is available separately as `GeneralLinear.isSupercuspidal_comp_fieldEquiv`.
