# Proof of the actual local Weil interface

Author: Worker 53. This proof contribution proves the published target
`Langlands.Weil.Local.LocalAssemblyStatement` (module
`Langlands.Weil.Local.AssemblyStatement`, published at Library commit
`22b4f024e0d4218752e970d09329d1799f6d81d1`). The construction `Langlands.Weil.Local.Assembly` and the
arithmetic inputs it uses (Worker 9's absolute residue theorem and Worker 28's
finite-field comparison) are published. The environment is Lean 4.34.0 with
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The complete theorem `localAssembly` proves
`LocalAssemblyStatement` for every prime and carrier universe. The component
lemmas expose each assertion for direct reuse.

The two definitions of the residue field give the same residue cardinality.
For any Weil element, apply the inverse finite-field comparison to its
pullback equation. The finite-field theorem on integer images gives the
actual geometric Frobenius power acting on the residue closure.

Injectivity of projection comes from the existing generic pullback theorem.
The actual residue degree is open because the residue map is open and the
finite-field comparison is a homeomorphism. Integer images are dense in the
profinite completion; their inverse image under this open map is dense.
The generic range description identifies that inverse image with the
projection range.

Injectivity of the integer map into its profinite completion identifies the
degree kernel with the inverse image of absolute inertia. The generic inertia
inclusion and the constructed equality equivalence show that the actual
inertia inclusion is an open embedding with exactly that kernel as range.
Absolute inertia is compact by the arithmetic residue theorem, so its
continuous image is compact. The explicit inverse equivalence uses projection
in one direction and the degree-zero inclusion in the other, retaining the
original subgroup topology.

The existing `Langlands.LocalClassField.absoluteGaloisNonarchimedean`
theorem supplies the nonarchimedean group property for the actual absolute
Galois group: Krull neighborhoods contain fixing subgroups of
finite-dimensional intermediate fields, and those subgroups are open.
The discrete integer group
is nonarchimedean, products preserve the property, and pulling a neighborhood
back to a subgroup yields its corresponding open subgroup. This subgroup
inheritance proof is shared as `Langlands.subgroupNonarchimedean` in
`Langlands.Topology.Nonarchimedean.Subgroup`. Hence the actual
Weil pullback is nonarchimedean. Its compact open inertia is a compact
identity neighborhood, which gives local compactness by Mathlib's group
theorem. Hausdorffness is inherited from the product and subgroup; Mathlib's
nonarchimedean-group theorem supplies total disconnectedness.

The chosen lift's degree equation specializes the geometric residue action
to Frobenius itself. The previously constructed norm formula specializes to
the actual field, giving `q^(-degree)` and value `q^-1` on that lift.
The same degree equation evaluates every unramified character, and the
degree-kernel condition proves its inertia triviality.

This proof follows the implemented construction and uses the source context
documented in `Assembly.md`. The complete module compiled without diagnostics
in the pinned environment.
