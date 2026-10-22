# Universal properties of the generic Weil pullback

`Langlands.Weil.UniversalProperty` is a proposition definition, not a theorem.
It gives both algebraic and continuous universal properties of the explicit
integer-Frobenius pullback. It has independent universe parameters `u` and `v`
for the original group and the group mapping into the pullback.

For every group `Γ` with a topology and continuous homomorphism
`φ : Γ → ProfiniteIntegers`, it asserts both of the following.

- For every group `H` and homomorphisms `a : H → Γ`, `b : H → ℤ` with
  `φ ∘ a = frobenius ∘ b`, there is a unique group homomorphism `h : H → W(φ)`
  whose composites with projection and degree are `a` and `b`.
- If `H` also has a topology and `a` and `b` are continuous (with discrete
  topology on the degree integers), there is a unique **continuous** group
  homomorphism with those composites.

Each uniqueness assertion is within the indicated bundled homomorphism type.
The compatibility equation, existence, and both projection equations are
explicit in Lean. Neither surjectivity of `φ` nor a Frobenius lift is required.
Continuity of the group operations of `Γ` or `H` is not needed for these
factorization statements, though they apply in particular to topological
groups.

## Provenance and source correspondence

These are derived universal properties of the subgroup
`{(g,n) | φ(g) = frobenius(n)}` with its product-subtype topology. A prospective
proof uses `h(x) = (a(x), b(x))`; compatibility gives membership, coordinate
homomorphisms give the group law, continuity into the subtype follows from
continuity of the two coordinates, and uniqueness follows from both
coordinate equations. This explains the intended mathematical statement;
it is not a claim of an implemented proof.

The original construction being generalized is Guy Henniart,
*Representations du groupe de Weil d'un corps local*, L'Enseignement
Mathematique (2) 26 (1980), Section 2.1, printed page 158 (PDF page 5).
Henniart defines the integer-Frobenius preimage and specifies the topology
on inertia. The generic categorical factorization statements are derived
here; they are not claimed to appear as theorems in that paper.

- `literature_id`: `henniart-1980-weil-representations`
- `content_sha256`: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`
- File: `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`
- Locator: Section 2.1, printed page 158, PDF page 5.
- [Original source DOI](https://doi.org/10.5169/seals-51064).

## Exact dependencies and validation boundary

The only project definition dependency is `Langlands.Weil.Pullback` at the
exact version named in the submission manifest. Its Markdown supplies the
scope restrictions and the additional Galois/residue-field facts needed for
the p-adic specialization. No field-theoretic identification is asserted here.
No other project statement or proof is used.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.

The statement manifest must contain the successful `lean_check` proposition
fingerprint. A proof submission must bind to an independently accepted,
published exact version. This module contains no proof, axiom, or placeholder.
