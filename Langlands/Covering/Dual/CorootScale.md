# Coroot scales and divided roots for covering data

In `Langlands.Covering.Dual`, let `P : RootDatum ι X Y` be the original
integral root datum and `Q : QuadraticForm ℤ Y` a quadratic form. Write
\(c_i\) for `P.coroot i`, \(f_i\) for the root functional `P.root' i`,
\(s_i\) for `P.coreflection i`, and \(B_Q\) for `Q.polarBilin`. Invariance is
expressed as \(Q(s_i y)=Q(y)\) for every \(y\) at the root index used in a
result. A form invariant under all coreflections supplies this hypothesis
at every index. For a split pinning `p`, the input `p.rootDatum` has
cocharacter module `cocharacterLattice p.torus`.

## Polarization and scaling

`polarBilin_coroot` proves \(B_Q(c_i,y)=Q(c_i) f_i(y)\). The proof expands
the polarization and uses additivity of \(s_i\) and invariance of \(Q\) to
obtain \(B_Q(s_i c_i,s_i y)=B_Q(c_i,y)\). The root pairing gives
\(s_i c_i=-c_i\) and \(s_i y=y-f_i(y)c_i\). Bilinearity and
\(B_Q(c_i,c_i)=2Q(c_i)\) then give \(2B_Q(c_i,y)=2f_i(y)Q(c_i)\), and
cancellation takes place in \(\mathbb Z\).

For degree \(n>0\), `corootScale` is \(m_i=n/\gcd(n,Q(c_i))\), with the
nonnegative integer gcd. The gcd is positive and divides \(n\), so the
quotient is at least one by `corootScale_pos`.
`degree_dvd_mul_coroot_value_iff` proves for every integer \(k\) that
\(n\mid kQ(c_i)\) if and only if \(m_i\mid k\). The proof rewrites the latter
condition as \(n\mid\gcd(n,Q(c_i))k\) using
`Int.ediv_dvd_iff_dvd_mul`. The gcd divisibility equivalence then replaces
the gcd by \(Q(c_i)\). In particular \(m_i\) is the least positive integer
with \(n\mid m_i Q(c_i)\). The equivalence treats \(Q(c_i)\) as an arbitrary
integer. The zero value gives \(m_i=1\) by
`corootScale_eq_one_of_coroot_value_eq_zero`, and `corootScale_neg` shows
that negating \(Q\) preserves the scale.

`corootScale_reflectionPerm` uses \(c_{s_j i}=s_j c_i\) and the invariance
under \(s_j\) to show that the reflection permutation at \(j\) preserves
the scale at every \(i\).

## Integral evaluations and coreflections

`scaledCoroot` is \(m_i c_i\) in \(Y\).
`degree_dvd_polarBilin_scaledCoroot` proves \(n\mid B_Q(m_i c_i,y)\) for
every \(y\in Y\) by bilinearity and \(n\mid m_i Q(c_i)\).
`corootScale_dvd_root_apply` proves \(m_i\mid f_i(y)\) from
\(n\mid B_Q(y,c_i)\), using symmetry of the polarization, the coroot
identity and the integer divisibility equivalence.

For a supplied \(\mathbb Z\)-submodule \(L\) of \(Y\) with
\(n\mid B_Q(y,c_i)\) for all \(y\in L\), `dividedRoot` is the integral
linear functional \(f_i^{\mathrm{div}}(y)=f_i(y)/m_i\).
`dividedRoot_apply` gives its quotient formula and `mul_dividedRoot_apply`
gives \(m_i f_i^{\mathrm{div}}(y)=f_i(y)\) by exact integer division.
The linearity proof multiplies both sides of each linearity law by \(m_i\),
uses exact division and linearity of \(f_i\), and cancels \(m_i\).

`sub_dividedRoot_smul_scaledCoroot` uses the multiplication identity to
give \(y-f_i^{\mathrm{div}}(y)(m_i c_i)=s_i y\) in \(Y\).
If \(m_i c_i\in L\), `dividedRoot_scaledCoroot` proves
\(f_i^{\mathrm{div}}(m_i c_i)=2\) by applying the same identity to this
element, using \(f_i(c_i)=2\), and cancelling \(m_i\). For the congruence
lattice defined by \(n\mid B_Q(y,z)\) for every \(z\in Y\), its membership
condition supplies the hypothesis on \(L\) and the scaled-coroot divisibility
supplies \(m_i c_i\in L\).

## Sources

- Martin H. Weissman, *Split metaplectic groups and their L-groups*,
  §1.3, Lemma 1.2 and Construction 1.3, printed pp. 94–95 (one-based PDF
  pp. 6–7). The polarization identity and the lattice integrality argument
  there are written for simple roots, and the same coreflection calculation
  applies at any root index. Registered as
  `weissman-2014-split-metaplectic-groups` with SHA-256
  `52b8015c678377f6f0d2e9d9995558ba8a77a8fc870bce5c252c0decb1db78b3`.
  [Published article](https://doi.org/10.1515/crelle-2012-0111)
- Wee Teck Gan and Fan Gao, *The Langlands–Weissman program for
  Brylinski–Deligne extensions*, §5.1, printed pp. 212–213 (one-based PDF
  pp. 230–231 in the Astérisque 398 volume), gives the gcd formula on every
  coroot and the scaled coroot and divided root formulas. Registered as
  `gan-gao-2018-langlands-weissman-program` with SHA-256
  `fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
