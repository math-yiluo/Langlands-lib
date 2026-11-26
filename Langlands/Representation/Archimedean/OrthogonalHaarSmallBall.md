# Polynomial lower bound for small orthogonal Haar balls

`OrthogonalHaar.distSq` is the squared Frobenius distance between real orthogonal matrices. `OrthogonalHaarSmallBallStatement` gives the lower bound \((2m+1)^{-n^2}\) for the measure of the closed ball at the identity of Frobenius radius \(n/m\), for every positive integer \(m\). The measure is a probability measure invariant under left translation on the orthogonal group with measurable multiplication.

`orthogonalHaarSmallBall` partitions the ambient entry cube \([-1,1]^{n^2}\) by the coordinate labels \(\lfloor m(x_{ij}+1)\rfloor\). The sum of the squared entries of each column of an orthogonal matrix is one, so each label belongs to \(\{0,\ldots,2m\}\). Two matrices with the same label differ in each entry by at most \(1/m\), making their Frobenius distance at most \(n/m\). Choose a representative of each occupied cell. The left translates of the identity ball by these representatives cover the orthogonal group because orthogonal multiplication preserves the Frobenius distance. Left invariance and finite subadditivity give \(1\le (2m+1)^{n^2}\) times the mass of a ball. Dividing yields the stated bound.

This elementary covering estimate supplies a denominator bound for normalized polynomial peaks at the identity. The exponent arises from the matrix embedding.
