# Brauer relations as identities in the representation ring of a finite Galois group

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. After the reduction
to the bottom field (`BrauerKernel.BottomReduction`), Deligne's global argument needs the
local relation in a form that can be transported to a global Galois group. This unit gives
that form. An actual relation `z` over the bottom field yields a finite normal intermediate
field `K` with group `G = Gal(K/F)`, characters of subgroups of `G`, and, for every
unramified type `τ`, an identity in the representation ring of `G`. No epsilon or L-factor
identity is asserted.

All declarations are in `Langlands.LocalFactor.NonabelianBrauer`, except two in
`Langlands.VirtualRepresentation.ExactGrothendieckGroup`.

## Galois restriction (`section Restriction`)

Fix `K : Extension F` with `Normal F.Carrier K.field`.

- `galoisRestriction F K : W_F →* Gal(K/F)` (definition): Mathlib's
  `AlgEquiv.restrictNormalHom K.field` composed with the published `localProjection F`.
  `galoisRestriction_apply` gives the action on `K`.
- `galoisRestriction_surjective`: the published `localProjection_denseRange`, Mathlib's
  `AlgEquiv.restrictNormalHom_surjective` and `InfiniteGalois.restrictNormalHom_continuous`
  give a dense range in the discrete finite group, hence surjectivity. This follows the
  published `Weil.Local.finiteGaloisQuotient_surjective`.
- `galoisRestriction_eq_one_iff`, `isOpen_ker_galoisRestriction`: the kernel is the Weil
  subgroup `W_K`, which is open.
- `galoisImage F K L` (definition): the image of `W_L` in `Gal(K/F)`.
  `galoisRestriction_mem_galoisImage_iff`: for `L ≤ K`, an element of `W_F` lies in `W_L`
  exactly when its restriction lies in `galoisImage F K L`, since the kernel `W_K` is inside
  `W_L`.
- `toGaloisImage F K L` (definition) and `toGaloisImage_surjective`: the restriction map from
  `W_L` onto its image.
- `galoisCharacter F K L χ hχ` (definition) and `galoisCharacter_apply`: a character `χ` of
  `W_L` that is trivial on `W_K` descends to the Galois image, by Mathlib's
  `MonoidHom.liftOfRightInverse`.

## A trivializing finite Galois field

- `characterLine_hasFiniteImage`, `eq_one_of_characterLine_eq_one`: for the published
  `FiniteRepresentation.characterLine`, a finite-range character has finite image, and the
  line acts trivially only where the character is `1`.
- `exists_galois_kernel_character`: a finite-range continuous character of `W_L` is trivial
  on the elements whose Galois projection lies in some open normal subgroup. This is the
  published `CommonClosure.exists_galois_kernel` applied to its character line.
- `exists_normal_extension_trivializing`: for finitely many finite-range continuous
  characters `χ_i` of `W_{L_i}`, there is a finite normal `K` containing every `L_i` with
  every `χ_i` trivial on `W_K`. Take the fixed fields `N_i` of the open normal subgroups of
  the previous item; they are finite by Mathlib's `InfiniteGalois.isOpen_iff_finite` and
  `fixingSubgroup_fixedField`. Then `K` is the normal closure (Mathlib's
  `IntermediateField.normalClosure`) of `⨆ i, (L_i ⊔ N_i)`. Its fixing subgroup lies in each
  of these open subgroups.

## Inflation

- `inflate_induce_characterLine`: let `π : W_E → Q` be surjective onto a finite group with
  open kernel, `S ≤ Q` with preimage `W_L`, `χ` a character of `S`, and `η` any continuous
  character of `W_L` with `η = χ ∘ π` on `W_L`. Then the published inflation
  `ExactGrothendieckGroup.inflate π` of `Ind_S^Q χ` is the common-closure induction of the
  line of `η`. This is the published `CommonClosure.inflate_induce_oneDimensional` with the
  character `η` made explicit. The proof is the same, through
  `ExactGrothendieckGroup.inflate_ofClass_induce`.
- `ExactGrothendieckGroup.traceFunction_liftFiniteRepresentation` and
  `ExactGrothendieckGroup.trace_inflate`: the trace (`BrauerKernel.Trace`) of an inflated
  virtual representation is its virtual character (`FiniteRep.virtualCharacter`) composed
  with `π`. Both sides are additive in the representation class. On classes the claim is the
  invariance of the trace under conjugation by the universe lift.

## The Galois type decomposition

- `twistedContinuousCharacter` (definition), `twistedContinuousCharacter_apply`: the twisted
  Weil character of `BrauerKernel.TypeSplit` as a continuous character.
- `trace_induce_characterClass`: the trace of `induce F E L h [η]` is the Frobenius sum
  `frobeniusSum F g η` of `TypeSplit`.
- `GaloisTypeDecomposition F e z` (structure): a finite normal `K`; exponents `t₁`, `t₂`;
  `L_g ≤ K` on the support; characters `θ₁ g`, `θ₂ g` of `galoisImage F K L_g` with
  `θ₁ g ∘ toGaloisImage = twistedWeilCharacter F e L_g (first) (t₁ g)` and the same for
  `θ₂`. Finally, for every `τ`,
  `Σ_{g ∈ supp z} z(g) ([t₁ g = τ] Ind θ₁ g - [t₂ g = τ] Ind θ₂ g) = 0`
  in the published `FiniteRep.VirtualRep ℂ Gal(K/F)`, where `Ind` is the published
  `FiniteRep.induce` of `FiniteRep.oneDimensional`.
- `mem_weilSubgroup_baseExtension`, `bottomGaloisRestriction`,
  `bottomGaloisRestriction_surjective`, `isOpen_ker_bottomGaloisRestriction`: the
  restriction map on the bottom-field Weil subgroup, which is all of `W_F`.
- `galoisType_identity`: assume every type component (`typeComponent` of `TypeSplit`)
  vanishes, and the characters factor as above. Then each type part is zero in the
  representation ring. By the published faithfulness of virtual characters
  (`FiniteRep.VirtualCharacter.faithfulness`) it suffices to show that its character
  vanishes. At `σ = π w` the character is the trace of the inflation (`trace_inflate`). By
  `inflate_induce_characterLine` and `trace_induce_characterClass` that trace is the type
  component at `w`, which is zero.
- `nonempty_galoisTypeDecomposition`: let `e` be normalized and `z` an actual relation over
  the bottom field. Then a Galois type decomposition exists. The accepted
  `exists_typeComponent_eq_zero` (`BrauerKernel.TypeChoice`) gives finite-range twisted
  characters and vanishing type components. `exists_normal_extension_trivializing` gives
  `K`, and `galoisCharacter` gives the characters. `galoisType_identity` gives the
  identities.

The field universe `uF` and the representation universe `uV` are independent. The finite
group and the representation ring live in the field universe.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, §4.10–4.11 (printed
pages 542–543, PDF pages 42–43). There a representation of the Weil group is trivial on a
finite-index subgroup of inertia, and each type component, after an unramified twist,
becomes a representation of a finite Galois group. The global lemma 4.12 (printed page 544)
then works with `Gal(K'/K)`. This unit is the corresponding internal derivation for the
actual presentation. It uses the published finite-quotient tools (`exists_galois_kernel`,
`inflate_ofClass_induce`), finite virtual-character faithfulness, Mathlib's infinite Galois
theory, and the accepted TypeSplit, TypeChoice and Trace units.
