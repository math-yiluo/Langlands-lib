# Stabilizers of actual Harris levels on a fixed polarized object

This derived module specializes `OrbitStabilizers` to the actual compatible
Weil-frame level tower of one fixed `PositivePolarizedAction`. It retains
the original Harris finite-adelic group, its opposite-group convention,
the Hodge-positive auxiliary involution, and the constructed
`hodgeLevelFunctor`. The object and all its polarization and dual data
remain fixed throughout each theorem.

Let `V ≤ U` be compact-open Harris levels, with `V` normal in `U`, and
let `g,k ∈ U`. For any monodromy-fixed `V`-orbit `x` of actual compatible
Weil frames on the fixed object, the two original inverse-right normal
transporter maps send `x` to the same orbit if and only if
`g * k⁻¹ ∈ V`. In particular, the transporter for `g` fixes `x` if and
only if `g ∈ V`.

`representativeOrbitResidualEmbedding` therefore constructs an actual
embedding of `U / V` into the fixed-object fine level, for each starting
orbit `x`. Its map is quotient descent of the original inverse-right
transporter map, rather than a selected representative. The equality
criterion proves both well-definedness and injectivity, using the
standard quotient-group equality criterion. The `_mk` equation
identifies its value on every original subgroup element.

The proof installs the actual Weil-frame right action and obtains its
freeness from `weilAdelicFrameRightAction_injective`. That theorem uses
the actual rational PEL form, here supplied by
`hodgeRationalPELConditions`, and nontriviality of the regular source
algebra, supplied by the central simple datum. The generic
`RightOrbit.translate_eq_translate_iff` then computes the orbit
stabilizer. Subtype extensionality retains the monodromy-fixed
condition. The scalar-extension continuous group equivalence carries
the original inverse-right transporter elements to the frame action;
their quotient is the image of `g * k⁻¹`. The existing subgroup
membership comparison returns exactly membership in the original
`V.subgroup`. The self-stabilizer corollary takes `k = 1`.

The base is any existing `Scheme.{0}` with a field-valued point and the
stated finite-fiber, torsion, roots-of-unity and quasi-separatedness
hypotheses of the actual level tower. Tensor comparison and coherence,
Picard, and relative Weil-transition assertions are explicit premises.
No connectedness, local Noetherianity, algebraic closure, sufficiently
small level or representability premise is needed for these
fixed-object conclusions.

These are internal deductions by Worker 57 from published constructions.
Their context is Harris–Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed pp.90–91 (one-based
PDF pp.98–99), where compatible frame orbits and right frame composition
enter the moduli problem. The stronger assertion there about normal
level Galois covers also takes the quotient by rational isogenies.
The present result proves neither freeness on that quotient nor
uniqueness of the translating residual element on represented schemes.
Rational self-isogeny stabilizers, applicable representability,
etaleness, the exact kernel-pair comparison, canonical geometry and
coefficient descent remain separate obligations.
