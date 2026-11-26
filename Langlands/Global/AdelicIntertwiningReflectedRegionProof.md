# Agreement of intertwining integrals on the reflected regular region

`Langlands.Global.intertwiningReflectedRegionAgreement` proves
`Langlands.Global.IntertwiningReflectedRegionAgreementStatement.{u}`.
For any finite meromorphic expansion agreeing with the normalized
intertwining integral on sufficiently regular source parameters, the
same expansion agrees with the integral at parameters in its specified
domain for which \(-w\lambda\) is sufficiently regular for the target.

## Proof

In `intertwiningReflectedRegionIntegrability`, factor a target-radical
point as in `exists_intertwiningReflectedHeightComparison`. The
reflected target parameter gives rapid decay of the source height
power in the height of the resulting opposite target point. Left
source-radical invariance permits the inducing function to be evaluated
at the polynomially bounded representative from that comparison.
For a fixed adelic argument \(g\), moderate growth bounds the value
of the inducing function there. Compact translation of the height
power accounts for \(g\).

Write the original integration variable in the target radical as a
principal point \(\delta\) times an element of a compact fundamental
set. A Chevalley line bounds the projective height of the rational
class \(P(F)w^{-1}\delta\) by a fixed negative character power of its
Iwasawa height. Source-radical invariance and the polynomial bound for
that fixed character power bound this projective height by a power of
the same representative's matrix height. Choose the opposite-radical
decay order to absorb both moderate growth and a power of this
projective height. Inverse powers of projective heights are summable
over the rational classes. The fibers of the class map lie in single
cosets of the discrete stabilizer, so the compact-cover unfolding
lemma supplies an integrable majorant on the actual quotient. The
threshold precedes the choice of the parameter and \(g\). In matrix
rank zero the closed embedding forces the adelic group to be trivial.
The integrand is then constant on the mass-one rational quotient.

`intertwiningReflectedRegionAgreement_of_integrability` works in
complex coordinates. For fixed \(g\) the convex absolute-convergence
domain has an interior containing both open regular regions.
The integral is holomorphic on this interior by local domination on
simplices and differentiation under the integral. The meromorphic
identity theorem with local denominators extends the initial equality
on the nonempty source region. The intersection of the coefficient
domains is the whole space for the empty expansion, so the argument
also handles this case with arbitrary \(D\).

## Provenance

Mœglin and Waldspurger give the inversion-root convergence region in
*Spectral decomposition and Eisenstein series*, II.1.6(i), (iv),
pp. 87–90, registered as
`moeglin-waldspurger-1995-spectral-decomposition`,
`06.1_pp_78_100_Definitions.pdf`, SHA-256
`948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`.
The Lean proof uses projective heights and the Iwasawa comparison
above to obtain the reflected-region estimate. The parameter and
quotient normalization is Bernstein and Lapid, *On the meromorphic
continuation of Eisenstein series*, §2.2, p. 191, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal PDF
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
