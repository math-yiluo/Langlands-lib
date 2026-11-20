# Fourier covariance for complex rectangular Schwartz functions

`complexRectangularFourier_translate` supplies the two-sided change of variables used in the proof of Jacquet's *Archimedean Rankin–Selberg Integrals* (2009), Proposition 7.3, p. 51. If the test is pulled back by `X ↦ A X B`, its transform is evaluated after multiplying by the two inverse transposes and is scaled by `(|det A|_ℂ^n |det B|_ℂ^m)⁻¹`.

The proof uses the published determinant scaling theorem for rectangular Haar measures with the scalar squared-norm change of variables. The entry pairing is the trace of `X Yᵀ`. Cyclicity of the trace and inverse cancellation give the pairing identity. The two-sided action pulls back a Schwartz function by a real continuous linear equivalence. For the transform itself, uncurrying the entries identifies it with the finite-coordinate trace Fourier transform and transfers Schwartz regularity back to matrices.
