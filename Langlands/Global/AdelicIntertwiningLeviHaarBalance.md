# Haar balance for the adelic intertwining quotient

`IntertwiningLeviHaarBalanceStatement` identifies the quotient Haar factor of conjugation at each target Levi point with the ratio of the target half modulus to the source half modulus transported by the Levi isomorphism. This is the modulus identity used in Bernstein–Lapid (6.5).

The theorem `intertwiningLeviHaarBalance` moves the cocharacters for the source and target parabolics to a common split torus and applies the equal-centralizer determinant comparison. The sum of the two radical determinant characters is twice the determinant character of the intersection on the common Levi. Each full radical determinant is the Levi restriction of the corresponding parabolic adjoint determinant. The proof identifies the stabilizer's action with the dynamic unipotent action inside the target parabolic by passing both conjugation formulas through the same immersion.

The adelic modulus comparison turns each forward Haar scale into the idele norm of the corresponding determinant character. The radical scale uses its usual ambient image in the adelic group. The stabilizer scale is transported from the dynamic subgroup to the actual stabilizer by continuous group isomorphisms intertwining conjugation. The determinant identity now gives `δ_P(c m) δ_Q(m) = δ_C(m)^2`, where `δ_C` is the positive scale on the stabilizer. The ratio `δ_Q(m) / δ_C(m)` therefore takes the positive half modulus at `c m` to the positive half modulus at `m`.

Source. Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, formula (6.5), journal p. 201, registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal PDF SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
