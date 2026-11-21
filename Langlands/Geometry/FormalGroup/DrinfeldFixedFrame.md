# A fixed special formal division-order module of height d²

`drinfeldFixedFrame` constructs a special formal module over the residue field of the completed maximal unramified base. Given the invariant and a scalar uniformizer, it uses the chosen unramified subfield of the actual division algebra, a residue embedding, and the standard Lubin–Tate line with its arithmetic Frobenius endomorphism. The inverse Frobenius twists give the `d` distinct tangent characters, and the actual division uniformizer acts diagonally.

The scalar uniformizer acts on each coordinate by the `d`-fold residue-cardinality power. The kernel rank of its `n`-th power on the product is `q^(n d²)`, giving the required height along with scalar divisibility and torsion. The invariant uses the Library's opposite Brauer class convention for Drinfeld's arithmetic conjugation law.

This supplies the fixed special formal module in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 A, printed p. 109, using his cyclic presentation in §2 B, printed p. 110. The line is the standard law of Lubin and Tate, *Formal Complex Multiplication in Local Fields* (1965), §1, Theorem 1, printed p. 382.
