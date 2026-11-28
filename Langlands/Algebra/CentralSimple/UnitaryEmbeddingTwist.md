# Norm multiplication of unitary embedding twists

The theorem `Langlands.CentralSimple.exists_unitarySolution_mul_norm` gives the change of witness for the equation in Prasad and Rapinchuk, *Local-global principles for embedding of fields with involution into simple algebras with involution*, arXiv:0806.0596v5, Theorem 3.2(iii), p. 11 and equation (9), pp. 13–14. The source uses the product in the order \(\tau(h)h\), which amounts to applying the involution to our witness.

If \(g\varepsilon(a)=h\tau(h)\), multiplying \(a\) by \(p\sigma(p)\) gives a new witness \(\tau(\varepsilon(p))h\). The proof expands the new product with its involution, substitutes the intertwining identity for \(\tau(\varepsilon(p))\), cancels \(g^{-1}g\), and uses commutativity in the source of \(\varepsilon\). An anti-involution sends a unit to a unit by reversing each inverse identity. The theorem `Langlands.CentralSimple.unitaryEmbeddingTwist_baseChange` extends the intertwining identity to arbitrary commutative coefficient algebras by evaluating it on pure tensors and then using additivity.

Source ID `prasad-rapinchuk-2010-embedding-fields-involution`. The retained PDF has SHA-256 `949df4d66b6ff7561ed36de8638a909543a582aa51e2f276e410c6ac624cfa79`.
