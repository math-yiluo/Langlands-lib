# Simple roots of a coweight face restrict to simple relative roots

Authors: Worker 187.

The module `Langlands.GroupScheme.Rational.FaceSimpleRootRestriction` (namespace
`Langlands.GroupScheme.FaceSimpleRootRestriction`) compares the simple roots of a
face base of the absolute root datum with the simple relative roots. It serves the
proof `Langlands.GroupScheme.leviCocenterKernelGeneration`.

## Setting

`k` is a field and `E/k` a field extension (finite Galois in the section `Face`).
`f : S ⟶ T` is a homomorphism of commutative group schemes over `k`, and
`j : T ⟶ G` embeds `T` in an affine group of finite type `G`. A subscript `E`
denotes base change to `E`. In the section `Face`, `T_E` is split
(`hT`), `j_E` is a closed immersion (`hj`), and `P` is a reduced root datum of
`j_E` (`hP : IsRootDatumOf j_E P`, with a finite index type `J`). The cocharacter
`ν` of `S` has image `ν' = bc(ν ≫ f)` in the cocharacters of `T_E` (hypothesis
`hν'`), and `C : Face P ν'` is a coweight face (module
`LinearAlgebra.RootDatumCoweightFace`): a base `C.base` adapted to a regular
refinement of `ν'`. The relative roots are those of `groupHom f ≫ j`.

## Results

- `latticePairing_baseChange_comp`: pairing a character `χ` of `T_E` with
  `bc(ν ≫ f)` equals pairing `f_E ≫ χ` with `bc(ν)`.
- `restrict_eq_zero_of_pairing_eq_zero`: let `S` be split and `ν` generic for
  `groupHom f ≫ j`. If a root `χ` of `j_E` vanishes on `bc(ν ≫ f)`, then
  `f_E ≫ χ = 0`. Proof: write `f_E ≫ χ = bc(a)`; base change of characters of the
  split torus `S` is bijective. If `a ≠ 0`, then `a` is a relative root, by
  `mem_roots_iff_exists_splittingField_restriction` (the relative roots are the
  nonzero restrictions of absolute roots). Its pairing with `ν` equals that of `χ`
  with `bc(ν ≫ f)`, which is `0`. This contradicts genericity.
- `faceHeight_galois`: for every `σ ∈ Gal(E/k)`, the Galois action on the root span
  (`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus`) preserves the face
  height `faceHeight C.base ν'` (module `LinearAlgebra.RootDatumFaceHeight`). Proof:
  the action fixes `ν'`, since `ν'` is the base change of a `k`-cocharacter
  (`cocharacterLattice.galoisRepresentation_baseChange`). So `C.correction` gives a
  based correction, and `faceHeight_comp_rootSpanMap` applies with `face_dominant C`.
- `faceHeight_eq_zero_of_restrict_eq_zero`: suppose `f` is the largest split subtorus
  of `T` (`IsLargestSplitSubtorus`) and `E/k` is finite Galois. If a root-span
  element `x` satisfies `f_E ≫ x = 0`, then `faceHeight C.base ν' x = 0`. Proof:
  `IsLargestSplitSubtorus.galoisOrbitSum_character_eq_zero` makes the sum of the
  Galois translates of `x` zero. Each translate has the face height of `x`
  (`faceHeight_galois`), so `|Gal(E/k)| · h(x) = 0` and `h(x) = 0`.
- `restrict_mem_simpleRelativeRoots` (simple restriction): let `S` be split, `f` the
  largest split subtorus, `β` a simple root of `C.base` with `root' β ν' ≠ 0`, and
  `f_E ≫ root β = bc(a)`. Then `a ∈ simpleRelativeRoots (groupHom f ≫ j) ν`. Proof:
  `ν'` is dominant for `C.base` (`face_dominant`), so `⟨a, ν⟩ = root' β ν' > 0`. Hence
  `a ≠ 0`, and `a` is a positive relative root. Suppose `a = a₁ + a₂` with positive
  relative roots `aᵢ`. Lift them to absolute roots `mᵢ` with `f_E ≫ root mᵢ = bc(aᵢ)`.
  Their values on `ν'` are positive, so their face heights are at least `1`
  (`one_le_faceHeight_root_of_pos`). The element `β − m₁ − m₂` restricts to `0`, so
  its face height is `0` by the previous item. Since `h(β) = 1`, this gives
  `1 − h(m₁) − h(m₂) = 0`, a contradiction.
- `root'_standard` (signs on a standard cocharacter): in the same situation, with
  `ν` generic, `β` any simple root of `C.base` with restriction `a`, and
  `ζ` a standard cocharacter for `{α}` (`IsStandardCocharacter … ν {α} ζ`). Then
  `0 ≤ root' β (bc(ζ ≫ f))`, with equality iff `root' β ν' = 0` or `a = α`. Proof:
  `root' β (bc(ζ ≫ f)) = ⟨a, ζ⟩`. If `root' β ν' = 0`, then `a = 0` by
  `restrict_eq_zero_of_pairing_eq_zero`. Otherwise `a` is a simple relative root by
  the previous item. Then `⟨a, ζ⟩ = 0` if `a = α`, and `⟨a, ζ⟩ > 0` otherwise, by the
  definition of a standard cocharacter.

## Relation to the literature

Together, `restrict_mem_simpleRelativeRoots` and
`restrict_eq_zero_of_pairing_eq_zero` give the part of Borel–Tits, *Groupes
réductifs* (1965), Proposition 6.8 (registered as
`borel-tits-1965-groupes-reductifs`) that this development uses. For a base of the
absolute roots compatible with the relative ordering, each simple root restricts
either to `0` or to a simple relative root. The proof via the Galois-invariant face
height was written for this formalization.
