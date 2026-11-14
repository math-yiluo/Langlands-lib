# Kernel of the quotient determined by invariant characters

Worker 714. Internal supporting construction for the anisotropic-part theorem.

The construction `anisotropicPart` takes a commutative group scheme over a
field and a finite Galois extension over which it is split. It returns
`AnisotropicPartData`: an actual closed subgroup which is a torus and is
anisotropic, together with factorization of every closed anisotropic
subtorus through its inclusion.

The chosen subgroup is the actual scheme-theoretic kernel of the split
quotient constructed in `TorusAnisotropicQuotient`. To prove it is a torus,
the proof base changes the kernel and uses its canonical diagonalizable
model. Its character group is the full integral quotient by the invariant
lattice. The lattice lemma `free_quotient_invariants` proves this quotient
free, and finite generation gives a finite basis identifying the
diagonalizable group with a split torus. The kernel inclusion is closed
because the split target is separated.

For anisotropy, a cocharacter killed by the quotient pairs to zero with
every invariant character. Each character's finite orbit sum is invariant.
Invariance of the pairing identifies its pairing with the original
cocharacter with the pairing of the original character against the
cocharacter's orbit sum. A cocharacter defined over the ground field is
fixed, so its orbit sum is the group order times itself. Cancellation in
the integers proves that it pairs trivially with every character.
Characters detect cocharacters of a split torus, and faithful field
extension detects the original cocharacter. Thus every cocharacter of
the kernel vanishes; the published cocharacter criterion gives anisotropy.
No division in the ground field or restriction on its characteristic is
used. The cocharacter lemmas only need a finite extension; the chosen
quotient construction uses the finite Galois hypothesis.

For the universal property, a homomorphism from an anisotropic torus to
any split torus is trivial: every rational character of the source
vanishes, and the target's characters separate homomorphisms. Affineness
and local finite type of the source follow from its torus hypothesis.
The actual kernel universal property supplies the required factorization.
This argument proves factorization even without closedness of the
incoming map.

These are internal consequences of the existing character, cocharacter,
finite Galois descent and kernel APIs, supporting the unchanged public
anisotropic-part statement. The finite surjective multiplication assertion
is a separate obligation.
