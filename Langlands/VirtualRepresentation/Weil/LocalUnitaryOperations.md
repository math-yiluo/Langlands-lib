# Actual local unitary Weil lattice operations

Author: Worker 24.

For an actual `PadicField p`, this derived construction specializes the published
unitary basis and lattice operations to its constructed `localWeilGroup`.
Field and representation-carrier universes remain independent. Representations
have complex coefficients with the usual topology; lattice coefficients are
integers. The unitary basis consists of genuine positive-rank continuous
irreducible classes admitting an invariant positive Hermitian form. No form
or preservation witness is supplied to define an operation.

`unitaryTwistBasisEquiv` and `unitaryTwistLatticeEquiv` use an actual continuous
character with pointwise complex norm one. Their values in the ambient basis
are the published local scalar twist and retain rank. The identity and product
laws are proved from the ambient twist laws by subtype extensionality and
finite-support reindexing; the composition first applies the second character,
then the first, giving their product. The inverse is the inverse character.
The generator and coefficient formulas describe this same reindexing.

`unitaryDualBasisEquiv` and `unitaryDualLatticeEquiv` specialize the genuine
contragredient restriction. The actual local Weil group supplies the required
topological-group structure. The basis and lattice operations are involutions;
the lattice inverse is itself. Their underlying ambient values, positive ranks,
generators and coefficients have the stated formulas.

Both operations commute with inclusion into the full local irreducible lattice,
preserve dimension-weighted degree and the integer coefficient pairing, and
preserve and reflect the cone of nonnegative coefficients. These laws specialize
the published generic unitary operations; no character-orthogonality assertion
or correspondence is involved.

The unramified operation takes `z : ℂˣ` with `‖(z : ℂ)‖ = 1`. The actual
`localUnramifiedCharacter F z` has value `z` raised to the actual integer
geometric degree. The norm of every integer power is one, proved by the complex
norm power law. This supplies the hypothesis of the local unitary twist, giving
`unitaryUnramifiedTwistLatticeEquiv`. Its inclusion, degree and pairing laws
are the corresponding local twist laws. The normalization is the existing
geometric degree `+1`; no chosen Frobenius or replacement degree is an input.
No restriction of the residue-normalized norm twist to the unitary lattice is
asserted.

## Provenance and scope

This is an internal specialization of `Weil.LocalOperations` and
`Weil.UnitaryOperations`, with the already constructed local group and degree
from `Weil.Local.Assembly`. Unitarity preservation is proved in the imported
`Weil.Representation.UnitaryProof`; the current module assumes no unproved
preservation proposition. Identity and composition follow from actual twists,
and the unramified norm calculation is elementary complex norm algebra.

Henniart (2000), section 1.1 and footnote 1, printed p.439, specifies the local
Weil and unitary conventions; section 1.2(2)-(3), p.440, specifies twisting and
contragredience. Sections 2.5-2.6, pp.446-447, give the integral extension and
coefficient pairing motivation. These original passages were read in
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The restriction to the specified unitary basis is explicitly derived; the
source's full free group is not identified with that subset.

Finite/Galois-type support preservation, unitary orbit finiteness, global
weak-association images, irreducible decomposition and cross-side isometry
remain separate obligations. This construction asserts none of them.
