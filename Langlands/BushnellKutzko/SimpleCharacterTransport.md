# Covariance of simple characters under a linear automorphism

Let `f` be an `F`-linear automorphism of `V`. This module shows that the sets of simple
characters `C(𝔄,m,β)` of BK93 (3.2.1), (3.2.3), printed pp. 98–99, as computed by
`simpleCharacters` from the tail of a defining sequence, are covariant under conjugation by
`f`.

## Characters of corresponding subgroups

For an automorphism `φ` of a group and characters `θ` of `H` and `θ'` of `H'`,
`CharacterCorresponds φ θ θ'` says that `θ'(φ x) = θ(x)` whenever `x ∈ H` and `φ x ∈ H'`. When
`H' = φ(H)`, every `θ` has a corresponding `θ'` and every `θ'` has a corresponding `θ`. These are
`exists_characterCorresponds` and `exists_characterCorresponds_symm`. For subgroups whose
memberships correspond under `φ`, the following lemmas transport the conditions that occur in
`simpleCharacters`:

- `forall_subgroup_congr` transports universal statements over the subgroups;
- `characterAgreesOn_iff` transports `characterAgreesOn`, if the twisting functions satisfy
  `tw'(φ x) = tw(x)`;
- `mem_characterNormalizer_iff` says that `φ g` normalizes `θ'` exactly when `g` normalizes `θ`.

## The relative determinant

Let `σK : E ≃ E'` be a ring isomorphism of fields and `f` a `σK`-semilinear equivalence from a
finite-dimensional `E`-space. `det_endConj_semilinear` proves
`det_{E'}(f x f⁻¹) = σK(det_E x)`. `semilinearCoords` transports the coordinates of a basis
`b`, and `ofEquivFun_semilinearCoords` shows that the resulting `E'`-basis is `f ∘ b`. In these
bases the matrix of `f x f⁻¹` is the matrix of `x` with `σK` applied to its entries.

`exists_factor_rangeRestrict_iff` says that a character `χ` of a group `U` factors through
`d.rangeRestrict : U → d.range`, via a character of the image `d.range` of a homomorphism `d`,
exactly when `χ` is constant on the fibres of `d`. The factoring character lives on the image
only: for the inclusion `d` of `A₃` in `S₃`, a nontrivial character of `A₃` is constant on the
fibres of `d`, but it is not the restriction of a character of `S₃`. This matches
`factorsThroughCentralizerDet`, whose factoring character is defined on the determinant image.
The proof of BK93 (3.2.5), printed p. 99, likewise takes the character on the determinant
image and extends it to `F[β]^×` in a separate step. Hence
`factorsThroughCentralizerDet_iff_det_eq` restates `factorsThroughCentralizerDet`. In this form
`F[β]` is a field, and the character takes equal values on units of `End_{F[β]}(V)` in its
domain with equal determinants. With
`relativeEndUnits_unitsConj` and the determinant formula, `factorsThroughCentralizerDet_transport`
shows that a character satisfies `factorsThroughCentralizerDet` for `fβf⁻¹` exactly when the
corresponding character satisfies it for `β`. Here `σK = elementAlgebraConj f β`, and `V` is
finite-dimensional over `F`.

## Simple characters

`elementCharacter_unitsConj` shows that the function `ψ_b(g) = ψ_F(tr(b(g − 1)))` of BK93
(1.1.6), printed p. 22, satisfies `ψ_{fbf⁻¹}(fgf⁻¹) = ψ_b(g)`, because the trace is invariant
under conjugation. By `LatticeChain.Corresponds.mem_relativeOrderNormalizer`, the groups
`B_β^× ∩ 𝔎(𝔄)` correspond, and by `mem_simpleHGroup` the groups `H^k` correspond.

`LatticeChain.Corresponds.mem_simpleCharacters` is the main result. Let `L` and `L'` be chains
corresponding under `f`, and let `θ`, `θ'` be corresponding characters of `H^{m+1}` computed
from `β` and a tail, and from `fβf⁻¹` and the conjugated tail. Then `θ'` is a simple character
for the conjugated data exactly when `θ` is one for the original data. The proof is by
induction on the tail, for all `β` and `m`. In the terminal case the two conditions are
transported by `forall_subgroup_congr`, with `elementCharacter_unitsConj`, and by
`factorsThroughCentralizerDet_transport`. In the recursive case the critical depths agree, so
both sides take the same branch of the definition. The conditions in the branch are
transported by the lemmas above. The characters `θ₀` of the shorter tail are matched by
`exists_characterCorresponds` and the induction hypothesis.

BK93 does not state this transport separately. Bushnell and Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), (1.1.6), printed p. 22, and (3.2.1), (3.2.3) and the
proof of (3.2.5), printed pp. 98–99. Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
