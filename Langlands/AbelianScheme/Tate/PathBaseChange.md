# Base change and path transport on actual Tate modules

Author: Worker 142.

This module proves that the canonical comparison for actual Tate modules under
pointed base change commutes with transport along a given finite-etale path.
It also constructs a diagonal rational comparison and identifies its inverse.
The finite statement concerns actual multiplication kernels; the integral
statement concerns their compatible point families; rationalization is over
the integers. The target path is `FiniteEtale.pathPushforward`, constructed
using actual pullback covers.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines the full and away Tate modules by
inverse limits of actual torsion points and their rational versions by tensoring
with the rationals over the integers. Section III.1, printed pp.90–92 /
PDF pp.98–100, uses geometric base points and monodromy-invariant orbits.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Chapter X section 3, (10.25)–(10.26), printed p.150 / PDF p.154, defines the
finite-etale cover category, geometric-fibre functor and its automorphism group.
Items (10.29)–(10.30), printed p.151 / PDF p.155, discuss different endpoint
fields, change of base point and pullback functoriality. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The present squares and diagonal comparison are internal deductions from the
actual kernel, pullback and transport constructions in the imported modules.
They are not presented as separately stated theorems in these sources. The
finite proof uses the canonical torsion pullback isomorphism and path
naturality; the remaining proofs use coordinates and rational tensor induction.

## Parameters and directions

Let `b : S' ⟶ S`, let `s : Spec Ω ⟶ S'` and `t : Spec Ω' ⟶ S'`, and
let `p : fiberFunctor s hs ≅ fiberFunctor t ht`. The fields can differ.
Finite-fibre witnesses are explicit at `s`, `t`, `s ≫ b` and `t ≫ b`.
Write `b_* p` for `pathPushforward b hsb htb p`.

For an actual group scheme `G` on `S`, base change gives `b*G` on `S'`.
For an abelian scheme `A`, `b*A` is `(AbelianScheme.baseChange b).obj A`.
The base-change comparison always goes from points or Tate modules of the
pulled-back object over `s` to those of the original object over `s ≫ b`.
Path transport goes from `s` to `t`. Every square therefore has the direction

```text
T(b*A, s)  -- transport by p -->  T(b*A, t)
    |                                |
 base change                      base change
    |                                |
    v                                v
T(A, s≫b) -- transport by b_*p --> T(A, t≫b).
```

The conditional statements do not require algebraically closed fields,
connectedness or local noetherianity: they use the supplied path and finite
fibres. In the Harris–Taylor application the points are geometric and the base
is connected and locally noetherian. This module supplies no path-existence
assertion and makes no claim of unpointed canonicity on the underlying Tate
modules.

## Actual finite group points and torsion

`GroupScheme.baseChangePointsEquiv_pathAct` proves the square for points of an
actual finite-etale group scheme. It applies
`pathPushforward_apply_left_of_comp` to the first projection of the pullback.
Equality of the underlying scheme maps gives equality of morphisms over the
base. Thus the point comparison is the existing pullback adjunction, rather
than an arbitrary equivalence.

`GroupScheme.Tate.levelBaseChange_finiteLevelTransport` proves the same square
on `Level G _ n`, with finiteness and etaleness of the actual multiplication
kernels on both bases as explicit typeclass hypotheses. The group object is
commutative. This general theorem imposes no positivity or invertibility
hypothesis beyond these kernel hypotheses.

Its proof expresses a torsion point through `kernelLevelEquiv`, then uses the
inverse of `torsionBaseChangeIso` to obtain a point of the pullback of the
original kernel. Path naturality for the canonical kernel isomorphism compares
the two finite transports. `levelBaseChange_kernel` identifies the existing
torsion comparison with the point comparison on that actual kernel, and
`baseChangePointsEquiv_pathAct` supplies the middle square. Applying the kernel
equivalence again gives the claimed equality of torsion points.

`AbelianScheme.Tate.levelBaseChange_transport` specializes this result to
an abelian scheme. It retains the explicit proposition
`TorsionFiniteEtaleStatement`, a positive order `0 < n`, and units for the order
in both `Γ(S, ⊤)` and `Γ(S', ⊤)`. The torsion theorem is applied at each base
to obtain the required finite-etale kernels. No assertion about noninvertible
torsion is inferred from this specialization.

## Selected integral and rational modules

For `P : ℕ → Prop`, `Index P` consists of positive orders satisfying `P`.
`integralBaseChange_transport` uses the actual inverse limit of torsion points
at those orders. It assumes invertibility of every selected order on both
bases, along with the same torsion finite-etaleness proposition. Extensionality
of coherent families reduces the equality to `levelBaseChange_transport`
at every coordinate.

`rationalBaseChange_transport` proves the square after scalar extension:
`Rational A _ P` is `ℚ ⊗[ℤ] Integral A _ P`. On a pure tensor the equality is
the integral square, with its rational coefficient unchanged. Tensor induction
and additivity prove the general result. This construction does not tensor the
integral module over the integers with the finite adeles.

These selected statements cover the full system by taking `P := fun _ => True`
and the away system by taking `P := fun n => Nat.Coprime n m`.
For prime `m = p` the latter is the prime-to-`p` system. The Lean definitions
also permit any natural modulus `m`.

## Diagonal comparison and inverse

`rationalBaseChangeAlongPath` constructs a rational linear equivalence

```text
Rational (b*A) (Over.mk s) P ≃ₗ[ℚ] Rational A (Over.mk (t ≫ b)) P
```

by transporting along `p` on `S'` and then applying actual base change at `t`.
Its definition needs the selected-order units on `S'`; it does not use units
on `S` or the finite-fibre witnesses for the composite points.

`rationalBaseChangeAlongPath_apply` identifies this diagonal with base change
at `s` followed by transport along `b_*p`. This alternate description uses the
additional hypotheses needed for transport on `S` and is exactly
`rationalBaseChange_transport`.

`rationalBaseChangeAlongPath_symm_apply` identifies the inverse diagonal as
reverse transport along the pushed path followed by inverse base change at
`s`. The proof applies injectivity of the two forward comparisons, rewrites by
the alternate description and cancels the equivalences. It does not choose
another path or a replacement inverse.

## Finite-adelic scalar structures

`finiteAdeleBaseChange_transport` states the same square for the existing
finite-adelic linear equivalences, using one
`RationalProfiniteIntegerAdeleComparison` on both bases. Their underlying maps
are exactly the rational comparisons, so the proof is the rational square.

`primeToFiniteAdeleBaseChange_transport` states the away version using one
coupled `PrimeToRationalProfiniteIntegerAdeleComparison` and precisely the
orders coprime to its modulus. It too is the selected rational square on
underlying elements. No new adelic ring or scalar identification is introduced.
Compatibility of the separate maps with endomorphism and tensor-algebra actions
is supplied by the existing base-change and transport modules.

The imported companion `TwistPathBaseChange` proves the corresponding actual
root-kernel point square and selected integral and rational twist equalities.
It includes section-ring full and away twists with the same scalar
comparisons, and prime-adic twists. Its paired Markdown explains the
root-coordinate identity under base change and each implemented proof.
Together these modules supply the Tate-module and twist comparisons.
Restriction to Weil-compatible frames and fixed orbit levels additionally
uses the existing geometric pairing compatibility. No polarization,
nondegeneracy or frame nonemptiness conclusion is asserted here.
