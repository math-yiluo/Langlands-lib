# Corrected torus lifts and the monomial section

Given a group homomorphism \(q\) to the special linear group, `MonomialLiftData` supplies lifts of the simple Weyl matrices and normalized lifts \(\widetilde h_i(x)\) of the simple coroot matrices. The element
\[
c_i(x,y)=\widetilde h_i(x)\widetilde h_i(y)\widetilde h_i(xy)^{-1}
\]
lies in \(\ker(q)\) by multiplicativity of the coroot. In a central extension, this is the central torus defect. The function `correctedCorootLift` sends \(x\) to \(\widetilde h_i(x)c_i(x,x)\).

The constructor `ofRootWeylLifts` takes the parameterized lifts \(\widetilde w_i(x)\). It uses
\(\widetilde w_i(-1)\) for the simple Weyl lift and
\(\widetilde h_i(x)=\widetilde w_i(x)\widetilde w_i(1)^{-1}\) for the coroot lift. In the base
group, the root matrix product at \(x=1\) gives \(w_i(1)^{-1}=w_i(-1)\). At general \(x\)
the product gives the adjacent entries \(x,x^{-1}\), which are the image of the single
coordinate \(x\) under `slDiagonalCorootEquiv`.

The function `torusLift` reads the simple coroot coordinates \(x_i\) of a diagonal and multiplies the corrected factors in descending index order. After projection, the product can be evaluated in the commutative group of simple coroot coordinates, where the single-coordinate factors multiply to the original tuple. The function `weylLift` multiplies the lifted simple Weyl matrices in the chosen reduced expression. Projection sends that product to `weylMatrix`.

The function `monomialLift` sends \(t\eta_w\) to the lift of \(t\) followed by the lift of \(\eta_w\). Its projection and value at the identity supply the section conditions used by `BruhatLiftData`. The construction uses the fixed reduced expression associated to \(w\).

## Source

- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §1, printed p. 134, PDF p. 4, the lifted coroot and its multiplicative defect, and printed p. 138, PDF p. 8, the simple Weyl lift. The correction and descending product are in §2, printed pp. 140–141, PDF pp. 10–11, and the monomial section formula is in Lemma 2(c) and its proof on p. 141. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
