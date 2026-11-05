# Normalized additive coordinates and descended extension defects

Worker 1330.

This derived construction continues `AdditiveExtensionCoordinate`. Let
`q : E ⟶ H` be a homomorphism of group schemes over a scheme `B`, and let
`a : kernel q ⟶ V` be a homomorphism. `IsFiberCoordinate q a f` means that
one regular map `f : E.X ⟶ V.X` satisfies, on every test scheme,
`a(g h⁻¹) = f(g) f(h)⁻¹` whenever `q(g) = q(h)`. The expression on the left
uses the actual point of the full scheme-theoretic kernel constructed by
`kernelDifference`.

`normalize f` divides `f` by its value at the identity. The resulting map is
still a fibre coordinate and takes the identity to the identity. A fibre
coordinate satisfies `f(xg) = a(x) f(g)` for every kernel point `x`.
Over an affine base `Spec R`, for an affine flat surjective homomorphism
between affine group schemes and any homomorphism of its kernel to the
standard rank-`n` vector group, `exists_normalizedFiberCoordinate` combines
this normalization with the existing affine additive-coordinate existence
theorem. Neither a section nor an identification of the kernel with a vector
group is assumed.

For the remaining constructions, `b` is an automorphic action of `H` on the
actual kernel, `c` is an automorphic action of `H` on `V`, and the two
all-test compatibility equations are explicit arguments: `b(q(g),x)` maps
to `g x g⁻¹` in `E`, and `a(b(t,x)) = c(t,a(x))`. These imply the right
translation formula `f(gx) = c(q(g),a(x)) f(g)`.

The regular morphism `defect q c f : E.X ⊗ E.X ⟶ V.X` is defined by

```text
δ(g,h) = f(gh) (f(g) c(q(g),f(h)))⁻¹.
```

Assume here that `V` is commutative. The product-kernel-difference formula,
followed by the fibre-coordinate equation and action compatibility, proves
that `δ(g,h)` depends only on `q(g)` and `q(h)`. This invariance holds on
every test scheme. For a quasi-compact flat surjective `q`, the square of
its underlying scheme map is an effective epimorphism, by the existing
`CommutatorDescent.effectiveEpi_tensorHom`. Its universal property descends
the defect to `quotientDefect : H.X ⊗ H.X ⟶ V.X`. Cancellation of that
scheme epimorphism proves that the descended morphism is over `B`.
`fac_quotientDefect` and `lift_quotientDefect` record its pullback and its
value on lifted pairs.

Write `C(t,r)` for evaluation of this descended morphism. The theorem
`quotientDefect_cocycle` proves, for all three points on every test scheme,

```text
C(t,r) C(tr,s) = C(t,rs) c(t,C(r,s)).
```

On lifts this follows by expanding the definition of the defect, using the
action laws and associativity, and cancelling in the commutative target.
For arbitrary quotient points, the proof applies
`AutomorphicAction.hom_ext_of_local_quotient_lift` three times to obtain local
lifts, transports all maps by naturality, and uses the identity on lifts.
Thus no global lifting hypothesis on test-scheme points is present.

This is internal infrastructure for the extension problem of Milne,
*Algebraic Groups*, corrected reprint (2022), Theorem 15.34(d), printed
pp. 319–320. The implementation derives the defect and its descent directly
from the Library's actual kernel, automorphic-action, and fpqc descent
interfaces. It does not assert a correction of the defect, a homomorphic
section, or the final splitting statement. The general base, target, and
quotient hypotheses stated above are the hypotheses in Lean; no smoothness,
reducedness, connectedness, characteristic, or kernel-embedding condition
is added.
