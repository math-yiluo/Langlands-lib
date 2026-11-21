# Real Fourier slices with scaled self-dual measures

The complementary real product-slice equality holds for every nonzero real additive parameter. Each Euclidean factor uses Lebesgue measure multiplied by `sqrt |a|` to the power of its real dimension. The positive Schwartz transform is the usual positive transform evaluated at the frequency multiplied by `a`, with the same measure factor. Expanding the transform identifies it with the integral for the Library's scaled real character.

`scaledEuclideanFourierCLM` expresses this transform as a continuous complex-linear map on Schwartz space. It composes the positive Fourier map with pullback by the frequency dilation and then applies the measure factor.

Apply the Lebesgue slice identity at the first frequency multiplied by `a`. On the transformed side change the second integration variable by multiplication by `a`. The two measure factors in the second variable multiply to the absolute Jacobian, which cancels. The same nonzero linear change of variables and finite measure scaling preserve absolute integrability. This supplies the scaled real analytic identity for the affine coordinates in Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemma 7.1.
