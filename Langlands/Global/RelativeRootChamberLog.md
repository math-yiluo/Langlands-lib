# Logarithmic halfspaces for actual positive-torus chambers

This derived adapter expresses the existing actual positive-torus chambers as
linear halfspaces in the existing real character dual. Let `F` be any number
field, `T₀` and `T` commutative group schemes over `F`, and `j : T₀ ⟶ T` an
actual morphism. For an arbitrary set `Δ` of actual characters of `T` and
positive thresholds `b χ`, the weak and strict log chambers consist of
functionals `ℓ : RealCharacterDual F T₀.toGrp` satisfying, respectively,

```
log(b χ) ≤ ℓ(j ≫ χ)       and       log(b χ) < ℓ(j ≫ χ)
```

for every `χ ∈ Δ`. The real logarithm is applied to the positive real value of
the unit `b χ`. Character restriction is composition with `j`; neither its
injectivity nor maximal splitness is assumed.

The intersection identities express these sets as inverse images of real
closed or open upper intervals under the continuous real-linear evaluation
maps at `j ≫ χ`. Consequently both chambers are convex, arbitrary weak
chambers are closed, and finite strict chambers are open in the real dual.
An empty character set gives the whole dual. Finiteness of a root set remains
an explicit hypothesis, rather than a conclusion about algebraic groups.

Strict monotonicity of the real logarithm on positive units proves
`mem_weakCharacterChamber_iff_log` and its strict counterpart. These identify
the existing intrinsic positive-subgroup chambers with the inverse images of
the corresponding log chambers under the actual normalized adelic
`characterLog`. These membership comparisons require no splitting.

If `T₀` is supplied with an actual finite splitting
`e : T₀.toGrp ≅ splitTorus (Spec F) I`, the explicit inverse `positiveExp`
from `PositiveRealTorusLog` proves both exact image equalities: the actual
log maps each intrinsic chamber onto the corresponding log chamber.
The scalar-coordinate membership formulas retain `d = [F : ℚ]`:

```
log(b χ) ≤ d * ∑ i, exponentᵢ(j ≫ χ) * log(xᵢ)
```

and the analogous strict inequality. They follow from the actual normalized
character-log formula; no degree division or threshold change is implicit.
The finite index type `I` may be empty.

For the existing `simpleRelativeRoots i ν`, the weak specialization retains
the common threshold `log t`. The based strict specialization compares
`characterLog(a₀)(χ)` with `characterLog(a)(j ≫ χ)`, where `a₀` is an actual
adelic point of `T`. The reference is a torus point; no extension to an
arbitrary Levi reference point is claimed.

The original source conventions are Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), §2.7, printed pp.71–72, equations
(2.25)–(2.26), for weak normalized simple-root inequalities on the derived
positive torus, and Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series* (1995), I.1.4, printed pp.5–7, equation (4), and I.2.1, printed
pp.18–20, for the normalized logarithm, equal-archimedean scalar embedding
and strict reference inequalities. MW treats roots as normalized real
characters in this convention; its p.19 argument explicitly distinguishes
algebraic evaluation from normalized positive-character evaluation. This
adapter is an elementary internal consequence of those conventions and the
existing `RelativeRootChamber` and `PositiveRealTorusLog` constructions.

The supplied `j`, character set and splitting are actual data. Identifying
them with maximal derived split tori and the roots of a minimal parabolic
requires the separate structural comparisons. No character restriction
finite-index theorem, Iwasawa decomposition or height independence,
Siegel-set coverage, Haar-modulus comparison or finite volume is established
here.
