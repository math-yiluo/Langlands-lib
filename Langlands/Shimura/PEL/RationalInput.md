# Rational source conditions for PEL levels

Worker 142. This unit records the algebraic source hypotheses for the PEL
level construction and proves the form properties needed after scalar
extension. It reuses `AlgebraInvolution`, `FormRespectsInvolution`,
`bilinearSimilitudes` and the actual tensor-algebra action of
`ScalarExtension`.

The parameters are a rational algebra `D`, a rational vector space `V`
with a `D`-module structure, an involution
`σ : AlgebraInvolution ℚ D`, and a rational bilinear form `ψ` on `V`.
`RationalPELConditions σ ψ` is the conjunction of:

- compatibility of the scalar actions, `IsScalarTower ℚ D V`;
- finite dimension of `D` over `ℚ`;
- finite dimension of `V` over `ℚ`;
- faithfulness of the given action of `D` on `V`;
- alternation of `ψ`;
- nondegeneracy of `ψ`;
- the identity `ψ (d • x) y = ψ x (σ d • y)` for all `d`, `x`, `y`.

The seven named projection lemmas expose exactly these conditions. This is
a proposition on existing data, not a structure containing a replacement
module, form, representation or geometric compatibility theorem. The
rational group is the already constructed `bilinearSimilitudes D ψ`.
For a commutative rational algebra `R`, its source after extension is the
already constructed `ScalarExtensionSimilitudes D V R ψ`, acting on
`R ⊗[ℚ] V` through `D ⊗[ℚ] R`.

`RationalPELConditions` deliberately does not assert that `V` is nonzero.
The conclusions about determination of the multiplier impose
`[Nontrivial V]` explicitly. In the usual nonzero PEL application that
hypothesis must be supplied. A zero vector space has a nondegenerate
alternating zero form, but all unit multipliers give the same underlying
automorphism, so it cannot be silently included in the freeness claim.

## Scalar extension and the value one

`Langlands.Algebra.bilinForm_attains_one` works for a nondegenerate form
over any field on a nonzero module; it needs no finite dimension or
alternation. Choose a nonzero `x`. Left nondegeneracy supplies `y` with
`ψ x y ≠ 0`, and rescaling `x` by the inverse of that value gives a pair
whose value is one.

`bilinForm_baseChange_attains_one` takes an existing value-one pair and
uses `1 ⊗ x`, `1 ⊗ y`. Mathlib's pure-tensor base-change formula gives
value one over every commutative coefficient algebra. No field,
integral-domain or nontriviality hypothesis on that algebra is needed.

`bilinForm_baseChange_isAlt` first extends the skew-symmetry identity by
tensor induction in both variables. Applying it on the diagonal gives
twice the value equal to zero; multiplication by the rational scalar
`1/2` gives alternation. This proof applies to commutative rational
algebras with zero divisors as well.

The namespace `RationalPELConditions` specializes these helpers to
`baseChange_isAlt` and `baseChange_attains_one`.
`baseChange_nondegenerate` installs the finite-dimensional instance
already present in the conditions and directly invokes the published
`Langlands.Algebra.bilinForm_baseChange_nondegenerate`. That theorem
uses an invertible Gram determinant and applies to arbitrary commutative
coefficient algebras; no new nondegeneracy proof is introduced here.

Finally `scalarExtension_underlying_injective` uses the extended
value-one pair and the existing
`bilinearSimilitudes.underlying_injective`. Thus, for a nonzero rational
source satisfying the conditions, two extended similitudes with the
same `D ⊗[ℚ] R`-linear operator have the same unit multiplier and are
equal. This is the algebraic ingredient for freeness on compatible
frames. It does not assert the existence of a frame.

## Provenance and scope

Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
Section 5, printed p.389 (PDF p.17), specifies a finite-dimensional simple
rational algebra with positive involution, a nonzero finite left module,
and a nondegenerate alternating form with precisely the displayed
involution identity. Printed pp.390–391 (PDF pp.18–19) explain
twist-valued compatible frames and the simply transitive right action
when such frames exist. The registered source is
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
No source-specific errata note was found in the consulted project notes.

The predicate is a derived extraction of the finite, faithful, form
conditions needed by the parent infrastructure task. It permits general
rational algebras and imposes faithfulness explicitly. In Kottwitz's
simple-algebra setting the nonzero module is faithful. It omits
simplicity, positivity, nonzeroness, integral orders, preserved
self-dual lattices, Hodge data and prime-local hypotheses. It is
therefore not a definition of all of Kottwitz's PEL data. The elementary
normalization and tensor-extension proofs above justify their stated
generality; they are not attributed as literal theorems in the source.

No abelian scheme, polarization, Weil pairing, Tate twist, monodromy,
topology, compact open subgroup or Harris group comparison is constructed
by this module. Its source conditions and lemmas are to be used with the
published actual geometric interfaces. In particular, it does not
establish nonemptiness of a frame space or complete the PEL level task.
