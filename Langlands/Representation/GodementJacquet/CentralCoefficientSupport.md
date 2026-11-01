# Compact central covers for matrix coefficients

These internal lemmas concern arbitrary topological groups and complex
representations on an independently universed algebraic carrier.
`centralSaturation K` consists of central multiples of points of `K`.
`compactCentralSupportFunctions` is the submodule of functions whose support
is contained in such a saturation for some compact `K`. Finite unions of
compact covers prove stability under addition, and scalar multiplication
only decreases support.

Suppose the center acts through a specified complex unit character, `H` is
normal, and `H` joined with the center has finite index. If every vector's
coefficient for one fixed functional restricts to a compactly supported
coefficient on `H`, then its coefficient on the whole group lies in this
submodule. The proof chooses representatives for the finite quotient by
`H` joined with the center. It takes the union of the translated compact
supports of the restricted coefficients of the corresponding translated
vectors. Normality rewrites each group element as a central element times
one of these translated subgroup elements. The central scalar action
shows that a nonzero coefficient forces membership in that compact cover.
No unitarity or norm invariance of the character is needed.

The final theorem applies this argument to actual smooth-dual functionals
and smooth vectors and extends by the defining complex span. Compactness
of the restricted coefficients and existence of the scalar central
character remain explicit hypotheses. This file derives a general support
implication; it does not assume or prove those hypotheses from
supercuspidality, nor assert any integral or functional equation. The
argument is an internal finite-coset support construction.
