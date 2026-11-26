# Values of the induced family on Levi chambers

In a finite-dimensional real inner product space, `activeRoots R b` retains the roots in `R` whose orthogonal projections to `b` are nonzero. For such a root `r`, the linear form `rootForm r` sends `x ∈ b` to `⟪restrictedRoot b r, x⟫ = ⟪r, x⟫`.

Suppose `R` satisfies `IsRootSet`, the subspaces satisfy `a ≤ a₁`, and the fine family `c₁` satisfies `IsFamily R a₁ c₁`. A fine chamber extends a coarse chamber when its positive-root set contains the coarse positive-root set. For every continuous real linear parameter `Λ` on `a`, `inducedFamily_eq_of_extension` evaluates the induced family using any such extension at `extendParam a a₁ Λ`.

A small regular perturbation of a coarse chamber point in the fine space gives an extension. Roots with nonzero projection to the coarse space have the same sign at any two extensions, so a finite gallery joins the extensions while avoiding their hyperplanes. At each crossing choose a projected root with the least positive evaluation at the first endpoint among those vanishing at the wall point. A decomposition into two positive projected roots would force both to vanish at the wall point and give smaller positive evaluations. This proves simplicity on the first side. The wall reverses the signs of the vanishing roots, which gives simplicity of the negative root on the other side. All forms vanishing at the crossing are proportional.

If the crossed wall has normal `v = restrictedRoot a₁ r`, the projection of `r` to `a` is zero. By nested orthogonal projection, `(extendParam a a₁ Λ) v = 0`. The adjacent-family axiom gives equality at this parameter at each crossing, so every extension gives the same value.

The choice independence is the assertion on the induced family in Arthur, *An introduction to the trace formula*, §17, printed p. 99. The proof uses the real instances of `FiniteHyperplaneChamberGallery` with the coarse nonvanishing roots specified as walls to avoid. The retained source is `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
