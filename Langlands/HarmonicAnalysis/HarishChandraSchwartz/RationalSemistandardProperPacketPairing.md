# The VII.2 pairing for both VIII.2.3 convolution tests

For an intrinsically cuspidal Schwartz function `f`, a point `g`, and a
smooth section `v` on an actual proper semistandard orbit, the convolution
tests are `h ↦ conj (f (g * h⁻¹))` and `h ↦ conj (f (h⁻¹ * g))`. Lean
builds both using the existing Schwartz inversion, translation, and
pointwise complex conjugation operations.

`ProperPacketConvolutionIntegrabilityStatement` requires product
integrability of the conjugate test times the actual density and orbit
coefficient on the product of ambient Haar and the source-normalized
orbit measure. `ProperPacketConvolutionPairingStatement` uses these inputs
to express each convolution at `g` by `GlobalForm.componentForm`, with the
actual Fourier component of its test in the conjugate-linear argument.
The Fourier component uses the conditional VII.1.3 smooth lift. Its
construction needs no finite-support premise.

The ambient Haar measure is the same measure in the convolution, Fourier
transform and pairing. The separate quotient Haar choices for the inducing
representations enter their formal degrees and the normalized orbit measure.
The local field and the complex smooth representation carriers have
independent universes. The rational-point construction applies to connected
reductive groups over nonarchimedean local fields of arbitrary characteristic.

The two convolution-to-pairing identities are the published identities in
`CuspidalConvolution`. In the pairing, Fubini exchanges integration over
the group and the orbit. The pointwise VII.1.1(ii) coefficient pairing gives
the inverse-degree product form, using the actual Fourier orbit formula.
Hermitian symmetry gives the conjugate-first order. The density and orbit
measure agree definitionally with the ones in the packet integral and in
the weighted component form.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d’après Harish-Chandra)*, Journal of the Institute of Mathematics
of Jussieu 2 (2003), printed pp. 319 and 322, VII.2 formula (1) and the proof
of VIII.2.3. [DOI](https://doi.org/10.1017/S1474748003000082)
