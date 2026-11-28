# Tested Weyl cone sums along a truncation ray

`WeylConeTruncationRayStatement` gives the relative spectral limit of a finite
holomorphic cone sum on the ray \(T_0+kT\), for a direction \(T\) positive on
every simple relative root. Each label \(l\) gives a standard parabolic
\(Q_l\), a normalizer representative \(a_l\) transporting the inducing Levi
to the term Levi, a Levi retraction, a real frequency and a polynomial on the
coroot coordinates of \(Q_l\). The inverse Weyl class must carry the Levi
simple roots of \(Q_l\) onto those of the inducing parabolic \(P\). The
displaced complex coroot arguments and the vertices in the meromorphic cone
terms are those of the given family. For all sufficiently large \(k\), the
terms are identified with their holomorphic sum on a dense regular subset of
the full imaginary plane. The weights and coroot polynomials are fixed along
the ray.

`weylConeTruncationRay` chooses the relative spectral coroot charts and the
positive spectral Haar factors before introducing the ray, frequencies and
tests. The finite cone Fourier boundary gives absolute integrability against
each smooth compactly supported relative test and expresses the tested
integral as a sum of signed spatial integrals. In the coordinates of \(Q_l\),
linearity of `weightCoordinate` gives the vertex parameter
\(b_l(0)+k v_l\), where every coordinate of \(v_l\) is positive. The
translated orthant has inequalities
\(0<(u_\alpha+b_l(k)_\alpha)d_{l,\alpha}\), where \(d_l\) is the nonvanishing
coroot slope of the common spectral displacement. For all-positive slopes
the orthant tends to the whole space, and a negative slope forces its
indicator to tend pointwise to zero. The translated Fourier limit gives the
polynomial point distribution in the first case and zero in the second.
The Weyl orientation theorem identifies the first case with
\(Q_l=P\) and \([a_l]=1\). Its orientation sign is \(1\).

The limiting sum pairs the surviving polynomials with the germs of the
test multiplied by each holomorphic weight and pulled back along the inverse
relative coroot chart. The corresponding point in those coordinates is the
evaluation of the real frequency on the projected simple coroots.

`weylConeTruncationRay_withHaar` retains the pushforward identity of the finite Fourier boundary. For every label, the pushforward of the original spectral measure by its relative coroot chart is its positive factor times `coordinateSpectralMeasure`.

This is a relative-coordinate consequence of the signed boundary in
Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023), 109107, Proposition 7.8 and its proof on printed p. 33, followed
by the translated cone limit in the proof of Lemma 7.11 on printed p. 35.
See (7.8)–(7.12), pp. 24–25, for the coroot factors and polynomial cone
terms. The registered source `delorme-2023-spectral-theorem-langlands` has
folder SHA-256 `e8b15973ea4ddbc7c7ba7f8fdf4eac5b42db2de9f74209baad19948cbfeb517b`.
The file `Delorme--On the spectral theorem of Langlands--2023.pdf` in
that folder has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
