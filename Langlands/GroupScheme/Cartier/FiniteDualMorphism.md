# Morphisms of finite convolution duals

For a map \(\varphi:A\to B\) of finite projective commutative bialgebras, `dualBialgHom` is the actual map from the convolution dual of \(B\) to the convolution dual of \(A\). It sends a functional \(f\) to \(f\circ\varphi\). Preservation of the original coproduct and counit proves compatibility with convolution and its unit. Pairing the transposed coproduct against pure tensors proves compatibility with the dual coproduct using preservation of the original multiplication. Compatibility with the dual counit follows by evaluating on the original unit.

The transpose preserves identities and reverses composition. `dualBialgHom_bidual` verifies naturality of the evaluation equivalence for bicommutative bialgebras. The same functional on either side of that formula evaluates to \(f(\varphi(a))\). These maps supply the finite-level morphisms needed to construct the dual torsion diagram of a special formal module.

The dual algebra and evaluation pairing are in Demazure and Gabriel, *Groupes algébriques*, Tome I (1970), Chapter II, §1, no. 2, 2.10(a), (b) and (d), printed pp. 156–158 (PDF pp. 186–188). The Lean construction derives functoriality by transposing actual coordinate algebra maps. Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), uses the Cartier dual in the split polarized object.
