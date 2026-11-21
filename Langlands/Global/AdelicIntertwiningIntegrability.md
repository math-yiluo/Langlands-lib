# Integrability on the rational intertwining quotient

`Langlands.Global.IntertwiningIntegrabilityStatement` uses the data and regular
region of `IntertwiningAbsoluteConvergenceStatement`. It gives a threshold
\(R\) such that the actual intertwining integrand is Bochner integrable on
\((V(F)\cap w U(\mathbb A) w^{-1})\backslash V(\mathbb A)\) at every sufficiently
regular source parameter and every adelic argument. It uses the Library's
quotient measure induced by Haar measure on \(V(\mathbb A)\) normalized by
\(\operatorname{vol}(V(F)\backslash V(\mathbb A))=1\).

`IsIwasawaCompact.intertwiningIntegrand_mk` gives the value at an arbitrary
representative \(v\). The chosen representative \(x\) of its class has
\(xv^{-1}\) in the rational stabilizer, so \(w^{-1}xv^{-1}w\) belongs to the
adelic source radical. Both the inducing function and its height factor are
invariant under this element. Thus the quotient integrand pulls back to the
continuous function \(v\mapsto \phi_\lambda(w^{-1}vg)\), which proves
`IsIwasawaCompact.continuous_intertwiningIntegrand` by the quotient topology.

In `intertwiningIntegrability`, the actual target radical image is closed and
the rational stabilizer is discrete. These supply the Borel structure of the
quotient and hence strong measurability of the continuous integrand. Apply
`intertwiningAbsoluteConvergence` on the singleton sets consisting of the
adelic argument and the parameter in linear coordinates. The resulting
integrable majorant proves integrability by `Integrable.mono'`, at the same
threshold.

This is a derived Lean formulation of the integrability in Mœglin and
Waldspurger, *Spectral decomposition and Eisenstein series* (1995), II.1.6,
printed pp. 87–88, Proposition (i) and its proof. The proof reuses the published
domination result and supplies the representative independence and
measurability for the chosen quotient model.
