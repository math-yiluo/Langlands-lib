# Coefficients and derivatives of actual semilinear root transport

This is an internal coordinate and differential calculation for actual
additive-line homomorphisms. It derives the formulas from the Library's
canonical point descent, polynomial coordinates and dual-number coefficient
maps. It states no new assertion from Steinberg or Borel–Springer. The fields
`k` and `K` are arbitrary in universe `u`, with a supplied `k`-algebra structure
on `K` and a supplied automorphism `σ : K ≃ₐ[k] K`. In particular, finite and
imperfect fields are retained.

`VectorGroup.standardEpsilon_val_eq_scalarPoint` identifies the underlying
dual-number point of the standard tangent vector with the scalar point whose
global coordinate is epsilon. Its proof applies the injective standard vector
coordinates, then the global-sections/spectrum isomorphism, and uses
`vectorAffineCoordinates_vectorLiePoint`. Thus this is an equality of actual
scheme points, including the dual-number structure.

`VectorGroup.scalarPoint_generic_eq_id` identifies the scalar point with
coordinate `X 0` on the one-variable polynomial test with the identity map
of the standard affine line. The proof writes the point as the spectrum of
polynomial evaluation, checks evaluation on the variable and applies the
functor's identity law.

`PolynomialGalois.aeval_generic_twisted` identifies evaluation at the generic
variable in `Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K)` with
`PolynomialGalois.lineConjugate k K σ`. The ring is unchanged; its `K`-algebra
structure sends a coefficient `c` to the original algebra map of `σ c`.
`PolynomialGalois.aeval_epsilon_twisted` similarly identifies evaluation at
epsilon in the twisted dual-number test with ordinary epsilon evaluation
followed by `GeneralLinear.DualNumber.coefficientAlgMap σ.toAlgHom` over `k`.
Both proofs check coefficients and variables using polynomial ring-homomorphism
extensionality. The latter coefficient map fixes epsilon because `σ` fixes zero
and one.

`VectorGroup.affineCoefficientCurve k K G f` is defined for any group scheme
`G` over `k` and any homomorphism `f` from the standard additive line over `K`
to the actual base change of `G`. It is the whole underlying morphism of `f`,
viewed as a polynomial-valued point of `G` by `Lie.affineBaseChangeEquiv`.
`affineCoefficientCurve_evaluate` proves that polynomial substitution computes
its value on every commutative `K`-algebra with a compatible `k`-structure. It
uses naturality of the affine base-change comparison and the formula expressing
a scalar point as polynomial evaluation.

For two such homomorphisms `f` and `f'`, the following lemmas take the explicit
all-test scalar-descent law: descending `scalarPoint z` followed by `f'` gives
`scalarPoint z` followed by `f`, on the test scheme with its structure changed
by `Spec σ`. This law is required for every scheme over `K` and every global
section; it is the law described by the preceding module's
`VectorGroup.ScalarDescentCompatible`.

* `affinePoint_of_scalar_descent` gives evaluation of the original coefficient
  curve on the twisted affine test. It applies the preceding module's
  `galoisTestPoint_of_scalar_descent`, the affine comparison for that test and
  `affineCoefficientCurve_evaluate`.
* `affineCoefficientCurve_conjugate_of_scalar_descent` specializes this formula
  to the generic polynomial test. The generic scalar point is the identity and
  twisted evaluation is coefficient conjugation, so the complete curve of `f'`
  is coefficient conjugation of the curve of `f`.
* `derivative_of_scalar_descent` also assumes that `G` is affine. It proves that
  the actual epsilon differential of `f'` is
  `Lie.baseChangeGaloisEquiv k K G σ` applied to that of `f`. The proof evaluates
  the affine formula on dual numbers at epsilon, factors twisted evaluation
  through the dual-number coefficient map, and applies the injective actual
  Lie-kernel base-change comparison. The standard epsilon identification turns
  the resulting equality of affine points into the required equality of Lie
  vectors.

Finally let `p` be a supplied split pinning of the actual base change of an
affine `k`-group `G`, and let `x` be a supplied normalized parametrization of a
simple root `a`. `NormalizedRootParametrization.galoisHom_coefficientCurve`
identifies the whole coefficient curve of the actually constructed `x.galoisHom`
with coefficient conjugation of `x.coefficientCurve`. The lemma
`galoisHom_derivative` identifies its epsilon differential with canonical
semilinear transport of `p.pinning.rootVector a`. These are specializations of
the two generic laws using the published all-test `x.galoisHom_point` law; the
derivative specialization also uses the supplied normalization `x.derivative`.

These calculations provide the differential needed to normalize a transported
root homomorphism once root-vector compatibility is established. They do not
construct compatible root vectors, a compatible pinning, a family of normalized
root maps, orbit orthogonality, a cross-section or the parent quotient theorem.
No global section in exceptional even type A is asserted.
