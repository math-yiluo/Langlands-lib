# Proof of the irreducible subquotient dichotomy

Authors: Worker 196 (proof and corollaries), Worker 220 (statement and
compatibility check of the closing theorem), Worker 283 (packaging and this
description).

This module proves the published proposition
`Langlands.SmoothRep.IrreducibleSubquotientDichotomy.{uR, uG, uV}` from
`Langlands.Representation.Category.ConstituentDichotomyStatement`. It
imports that statement by name and does not change it.

## The closing theorem

`Langlands.SmoothRep.irreducibleSubquotientDichotomy` has exactly the type
`IrreducibleSubquotientDichotomy.{uR, uG, uV}`. Its universe parameters are
`uR`, `uG` and `uV`, for the coefficients, the group and the carrier. They are
independent. The theorem quantifies over the whole statement:

- every field `R : Type uR`;
- every group `G : Type uG` with any topology;
- all smooth representations `A` and `D` in `SmoothRep.{uR, uG, uV} R G`;
- every actual invariant subspace `S : Subrepresentation A.representation`.

If `D.IsIrreducible` and `IsSubquotient D A`, the theorem gives
`IsSubquotient D (subrepresentation A S)` or `IsSubquotient D (quotient A S)`.
The proof introduces all of these variables and applies the lemma
`irreducibleSubquotient_dichotomy` below.

No hypothesis is added. There is no admissibility, finite dimension, finite
length, local compactness, semisimplicity, central character or
theorem-valued assumption. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## The implemented proof

All objects are the published actual constructions of `Category/Subquotients`.
`subrepresentation` restricts the action to an invariant submodule, and
`quotient` is the module quotient with the descended action. `subtype` and `mkQ`
are the inclusion and the quotient map. The proof uses Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero`: an intertwiner into an
irreducible representation is surjective or zero.

The private helper `quotientLift S f h` takes an intertwiner `f : A ⟶ B` and a
proof `h` that `f` vanishes on `S`. It returns the intertwiner `A/S ⟶ B`
obtained from `Submodule.liftQ`. Equivariance is checked on the image of `mkQ`
with `Submodule.linearMap_qext`.

`irreducibleSubquotient_dichotomy` is the same statement with implicit `R`, `G`,
`A` and `D`:

1. The accepted characterization `isSubquotient_iff_exists`, in
   `Classification/SupercuspidalSupport`, gives a smooth representation `C`, an
   injective intertwiner `i : C ⟶ A` and a surjective intertwiner `q : C ⟶ D`.
2. Let `f = i ≫ mkQ A S : C ⟶ A/S`. Its kernel `K` is the inverse image of `S`
   in `C`. Let `E = subrepresentation C K` and `qK = subtype C K ≫ q : E ⟶ D`.
3. Because `D` is irreducible, `qK` is surjective or zero.
4. **Surjective case.** For `x` in `K`, `i x` maps to zero in `A/S`, so `i x`
   lies in `S` (`Submodule.Quotient.mk_eq_zero`). Restricting the codomain of
   `i` on `K` gives an intertwiner `j : E ⟶ subrepresentation A S`, using
   `LinearMap.codRestrict`. It is injective because `i` is. Then `j` and the
   surjective `qK` show, by `isSubquotient_iff_exists`, that `D` is a
   subquotient of `subrepresentation A S`.
5. **Zero case.** Then `q` vanishes on `K`, so it descends to
   `q' = quotientLift K q : C/K ⟶ D`. This map is surjective: if `d = q c`,
   then `q'` sends the class of `c` to `d`. The map `f` also vanishes on `K`
   (here `K` is its kernel), so it descends to `j = quotientLift K f : C/K ⟶ A/S`.
   This map is injective by `Submodule.ker_liftQ_eq_bot`. Then `j` and `q'` show,
   by `isSubquotient_iff_exists`, that `D` is a subquotient of `quotient A S`.

## Corollaries for an intertwiner

Both corollaries are in this module and are used in the constituent argument.

- `irreducibleSubquotient_kernel_or_image`: for `f : A ⟶ B` and an irreducible
  `D` with `IsSubquotient D A`, `D` is a subquotient of `kernel f` or of
  `image f`. Take `S` to be the kernel of `f`. Then `kernel f` is by definition
  `subrepresentation A (hom f).ker`. The private isomorphism
  `quotientKernelIsoImage f : quotient A (hom f).ker ≅ image f` is the first
  isomorphism theorem `LinearMap.quotKerEquivRange`, with equivariance checked
  on the image of `mkQ`. The quotient alternative moves to `image f` by
  `IsSubquotient.of_iso_right`.
- `irreducibleSubquotient_image_or_cokernel`: for `f : A ⟶ B` and an
  irreducible `D` with `IsSubquotient D B`, `D` is a subquotient of `image f` or
  of `cokernel f`. Take `S` to be the range of `f` in `B`. Then `image f` and
  `cokernel f` are by definition `subrepresentation B (hom f).range` and
  `quotient B (hom f).range`.

## Scope and provenance

This is an elementary internal algebraic result. It isolates the
occurrence step "V is a subfactor of E' or of E''" in the proof of Bernstein and
Zelevinsky 1976, Proposition 3.30, as described in the statement's Markdown.
That source is motivation only, and the Lean proof does not depend on it. The
module does not prove Proposition 3.30, the published
`LeviCuspidalConstituentTheorem`, or any cuspidality, admissibility or
semisimplicity result.

## Dependencies

The module imports `Classification/SupercuspidalSupport` (for
`isSubquotient_iff_exists` and `IsSubquotient.of_iso_right`), the statement
module `Category/ConstituentDichotomyStatement`, and Mathlib's
`RepresentationTheory/Irreducible`. It does not modify any published pair. It
was checked in the Lean service environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
