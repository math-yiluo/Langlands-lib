# Coordinate lattice chains with prescribed jumps

Let \(F\) be a nonarchimedean local field with uniformizer \(\pi\), \(I\) a finite
coordinate set, and \(a\colon I\to\operatorname{Fin}(e)\) a surjection, with \(e>0\).
In `LatticeChain.blockChain`, coordinate \(k\) is multiplied by \(\pi\) at step
\(a(k)\) in each period. Its zeroth lattice is \(\mathfrak o_F^I\).

The lattice at index \(i\) is the image of \(\mathfrak o_F^I\) under the diagonal
scaling with exponents \(-\lfloor (a(k)-i)/e\rfloor\). The map is invertible, so the
image spans \(F^I\) and is finitely generated over \(\mathfrak o_F\).
`mem_blockChain` expresses membership by the inequality
\(i\le a(k)+e\,\operatorname{ord}_F(v_k)\) at every nonzero coordinate \(v_k\).
For strict decrease at \(i\), choose a coordinate with \(a(k)\) equal to the
remainder of \(i\) modulo \(e\). The vector supported there with coefficient
\(\pi^{\lfloor i/e\rfloor}\) belongs to \(L_i\) and fails the inequality for
\(L_{i+1}\). Increasing \(i\) by \(e\) multiplies the lattice by \(\pi\), which
gives `period_blockChain` by uniqueness of the period.

This is the split-coordinate lattice-chain construction of Bushnell and Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), §1.1, printed
pp. 20 and 23 (PDF pp. 32 and 35). It allows several coordinates to jump at
once, as needed for layers of prescribed ranks.
