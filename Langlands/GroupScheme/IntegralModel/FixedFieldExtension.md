# The strictly Henselian extension input on maximal-unramified integers

This internal adapter connects the general strictly Henselian extension
statement with the full model construction. All coefficients have arbitrary
common universe `u`.

`fixedField_hasSmoothHomExtension` specializes an assumed
`SmoothHomExtensionStatement` to the actual `fixedFieldIntegers F` and its
specified fraction field `inertiaFixedField F`. The existing arithmetic
theorem proves that the integer ring is a DVR and Henselian, and its residue
field is an algebraic closure of the original residue field. Algebraic
closedness implies separable closedness. These discharge all ring
hypotheses of the general statement. The statement itself remains an
explicit premise; the adapter does not prove an extension theorem.

The auxiliary `isSmooth_of_coefficientIso` reflects smoothness from a
supplied compatible upstairs model isomorphism through a flat surjective
integer coefficient map. The upstairs model isomorphism identifies the
structural morphisms, and the existing fpqc descent of smooth morphisms
then gives smoothness of the original model. No smoothness premise on that
original model is needed.

`modelOfFiniteRecovery` uses a supplied finite Galois arithmetically
unramified coefficient model N for the base change of an F-group G, its exact
compatible recovery of the original smooth model P over the inertia
integers, and P's original point stability under all F-automorphisms of the
inertia fixed field. The actual coefficient algebra structures are those
of the specified field and spectral-integer inclusions. Smoothness of N is
reflected from recovery of P. The specialized fixed-ring extension property
and the completed finite descent/recovery construction then give an actual
model of G over the given valuation integers of F.
`modelOfFiniteRecovery_smooth` proves its smoothness and
`modelOfFiniteRecoveryIso` recovers P from its actual
`baseChangeUnramified`, over `Iso.refl` of the original prescribed generic
group.

This is an internal application of the proved arithmetic and smoothness
descent facts and the actual finite-recovery construction. The supporting
`SmoothHomExtension` pair supplies two proposition targets and necessity
lemmas; it proves neither converse extension statement. This unit still
assumes the strictly Henselian extension statement and existence of the
finite coefficient model with exact recovery. It does not prove those
inputs or the unconditional `UnramifiedSmoothModelDescentStatement` / KP
Fact 2.10.16.
