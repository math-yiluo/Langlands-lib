# Split-centre invariance and norm-one evaluation of normalized Levi slices

Let \(l\colon M\to P\) and \(p\colon P\to G\) denote the Levi and parabolic
inclusions. Write \(\iota\) for their composite on adelic points. For any
translate \(k\in G(\mathbb A)\), the Library's `normalizedLeviValue p l φ m k`
is the slice
\[
f_k(m)=m^{-\rho_P}\phi(\iota(m)k),\qquad
m^{-\rho_P}=\delta_P(l(m))^{-1/2}.
\]
In Lean the normalizing factor is `parameterPower F P (-halfModulusParameter F P)`
at \(l(m)\). Here \(\rho_P\) is half the parameter of the rational
character \(\det(\operatorname{Ad}\mid\operatorname{Lie}P)\).

`normalizedLeviValue_splitComponent_mul` uses
`IsSplitComponentEquivariant p l φ`, which holds for an inducing form in
\(\mathcal A^2_P\). For \(a\) in the positive split component \(A_M\)
(`RestrictionSplitCentre.canonicalSubgroup F M`), the covariance also holds
at the translated argument \(\iota(m)k\). Multiplicativity of parameter powers
gives
\[
f_k(am)=a^{-\rho_P}m^{-\rho_P}a^{\rho_P}\phi(\iota(m)k)=f_k(m).
\]
The proof uses `form_canonical_mul` for the covariance and adds the two
opposite parameters in the product at \(a\).

`normalizedLeviValue_of_mem_normOne` uses
`parameterPower_map_of_mem_normOne` to evaluate the normalizing factor at
one. Every rational character of \(P\) pulls back to a rational character
of \(M\), whose adelic absolute value on \(M(\mathbb A)^1\) is one. Thus
\(f_k(m)=\phi(\iota(m)k)\) on \(M(\mathbb A)^1\) for any \(\phi\). The
proof rewrites the two point maps as the map of the composite.
`normalizedLeviSliceComparison` proves `NormalizedLeviSliceComparisonStatement`
by collecting these identities.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
  Series* (1995), I.2.17, printed p. 37
  (`moeglin-waldspurger-1995-growth-and-constant-terms`), defines the slice
  with \(m^{-\rho_P}\) and describes \(\rho_P\) using the roots on
  \(\operatorname{Lie}U\). For the Levi of a connected reductive group the
  determinant of the adjoint action on \(\operatorname{Lie}M\) is trivial,
  giving the same determinant character on restriction from \(P\).
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series* (2011), §2, printed p. 311
  (`lapid-2011-asymptotic-inner-product-truncated-eisenstein`), gives the
  \(A_M\)-covariance and the norm-one decomposition of \(M(\mathbb A)\).
