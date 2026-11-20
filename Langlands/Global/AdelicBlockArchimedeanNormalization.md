# Smooth archimedean extension of the adelic block half character

`mixedHalfNorm` transports the normalized infinite idelic absolute value to the units of the mixed archimedean space, takes the positive square root and embeds the result in the complex units. `archimedeanHalfExtension` applies the published smooth character extension to the determinant of each diagonal block and takes the pairwise product of powers and quotients determined by the block sizes.

On an actual infinite parabolic matrix, `archimedeanHalfExtension_parabolic` identifies the value with the positive half character of its adelic insertion. The mixed determinant coordinates commute with taking the diagonal blocks, and the finite determinant norms of the inserted blocks are one. Multiplicativity of the positive square root gives the pairwise formula.

`contDiffAt_archimedeanHalfExtension` proves smoothness at every such parabolic matrix. Each diagonal block depends linearly on the matrix entries and its determinant is smooth. The block determinants there are units, so the character extensions are smooth with nonzero values. Powers, products and quotients retain smoothness at the matrix.

This is an internal comparison using the published adelic determinant character and smooth unit character extension. Getz and Hahn (2024), §10.1, p. 271 (PDF 283), describe the normalizing factor in adelic induction and its relation to the factors at each place.
