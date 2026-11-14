# Degree-one cup creation on ordered Čech homology

This derived internal construction defines cup creation by an actual one-cocycle
on the all-sequence ordered Čech complex. All declarations are in
`Langlands.Cohomology.Cech`. It uses the published Alexander–Whitney product
`cup₁` and Mathlib's short-complex homology construction.

## Generic descent

Let `K` and `Q` be natural-number cochain complexes in any preadditive category,
and suppose maps `c n : K.X n ⟶ Q.X (n + 1)` satisfy

`K.d n (n + 1) ≫ c (n + 1) = -(c n ≫ Q.d (n + 1) (n + 2))`.

`creationShortComplexMap K Q c hc n` is a morphism from the short complex
computing degree-`n` homology of `K` to that computing degree-`n+1` homology of
`Q`. For positive `n`, its three components are `-c (n - 1)`, `c n`, and
`-c (n + 1)`, after the standard identifications of adjacent objects. At `n = 0`,
the left component is zero, and the source's degree-zero incoming differential
is zero by the complex shape. The two commutative squares follow from the stated
anticommutation identities. No separate bottom-boundary assumption is needed.

`creationShortComplexMap_τ₂` identifies its middle component with `c n`.
Assuming homology exists in the two relevant degrees, `creationHomologyMap`
is the induced morphism `K.homology n ⟶ Q.homology (n + 1)`.
`creationCyclesMap_i` says its cycle map followed by the target cycle inclusion
is the source cycle inclusion followed by `c n`.
`creationHomologyMap_homologyπ` gives the corresponding compatibility with
passing from cycles to homology classes.

## Section-cochain instance

Let `R` be any commutative ring, `π : X ⟶ Spec R` a scheme morphism, and
`U : ι → X.Opens` any family of opens. The index type has an independent
universe; neither finiteness, affine intersections nor a covering hypothesis is
required. For each open `W`, supply an `R`-algebra structure on `Γ(X, W)` and
an equality identifying its algebra map with the section map `secHom π W`.

`face_smul` proves that section restriction in a cochain face respects these
scalar actions, using the existing restriction algebra homomorphism
`resAlgHom`. `cup₁LinearMap π halg U z n` is the Alexander–Whitney product with
the one-cochain `z`, as an `R`-linear map from degree `n` to degree `n + 1`
section-cochain modules. Its underlying function is exactly
`cup₁ X.presheaf U z`. Additivity is the published `cup₁_add_right` identity;
scalar compatibility follows from `face_smul` and scalar multiplication
commuting with multiplication in a section algebra.

`cup₁AddHom` is its underlying additive morphism between terms of the actual
ordered Čech complex. If `z` is a one-cocycle, `cup₁HomologyMap π halg U z hz n`
is the induced additive map from degree-`n` Čech homology to degree-`n + 1`
Čech homology. Its anticommutation condition is the published identity
`d_cup₁_of_cocycle`; the proof explicitly identifies the differential of the
alternating-coface complex with the elementwise Čech differential.

## Provenance and scope

This is internal infrastructure derived from the cited Lean constructions, with
no additional literature assertion. It uses an actual one-cocycle as input. It
does not yet prove independence under replacing that input by a cohomologous
one, compare these homology objects with actual right-derived sheaf cohomology,
or construct geometric creation–contraction relations. The host degree-two
exterior and canonical coproduct comparison remains unproved.
