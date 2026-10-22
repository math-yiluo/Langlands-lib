# Supercuspidality under twists by characters of the determinant

Author: Worker 23.

This module proves that the published predicate `GeneralLinear.IsSupercuspidal`
of `Classification/Supercuspidal` is unchanged by twisting with an open-kernel
complex character of `GL_n(F)` that is trivial on the kernel of the
determinant, and builds the resulting twist maps on supercuspidal objects and
classes. It specializes them to the normalized real powers `|det|^s` for every
p-adic field.

## Jacquet quotients of twists

- `Jacquet.twist_comp_subtype`: if `N ≤ χ.ker`, the restriction of
  `twist χ ρ` to `N` equals the restriction of `ρ`, as actual representations.
- `Jacquet.subsingleton_coinvariants_twist_iff`: hence the published
  coinvariant quotient `Jacquet.Coinvariants (twist χ ρ) N` is literally the
  quotient `Jacquet.Coinvariants ρ N`, so one vanishes iff the other does.

Here `R` is any commutative ring, `G` any group and `V` any `R`-module.

## Determinant one on unipotent radicals

- `BlockShape.determinant_eq_one_of_mem_unipotentSubgroup`: every element of
  the standard block unipotent subgroup `B.unipotentSubgroup R` of
  `GL_n(R)`, for any commutative ring `R`, has determinant one. The proof
  reindexes the matrix by the published `B.indexEquiv` to the sigma type of
  block coordinates. There it is block upper triangular (membership in
  `B.parabolic R`) with identity diagonal blocks (the published
  `mem_unipotentSubgroup_iff`). Mathlib's `Matrix.BlockTriangular.det_fintype`
  writes the determinant as the product of the diagonal block determinants,
  each equal to one.
- `BlockShape.unipotentSubgroup_le_ker_determinant` restates this as a
  subgroup inclusion. Over a field, `BlockShape.conjugateUnipotent_le_ker_determinant`
  extends it to every conjugate `g U g⁻¹` (the published
  `B.conjugateUnipotent g`), since the determinant is multiplicative.
- `ker_determinant_le_ker_comp`, `ker_determinant_le_ker_one` and
  `ker_determinant_le_ker_mul` show that `ψ ∘ det`, the trivial character, and
  products of characters trivial on `ker det` are trivial on `ker det`.

## Closure of supercuspidality

- `GeneralLinear.isSupercuspidal_twist_iff_of_le_ker`: for an open-kernel
  `χ : GL_n(F) →* ℂˣ` trivial on every conjugate of every standard block
  unipotent radical, `IsSupercuspidal (twist χ ρ) ↔ IsSupercuspidal ρ`.
  Admissibility is transported by the published `isAdmissible_twist_iff`, and
  each Jacquet vanishing condition by the lemma above.
- `GeneralLinear.isSupercuspidal_twist_iff` replaces the radical hypothesis by
  `hdet : ker det ≤ χ.ker`, the condition that `χ` factors through the
  determinant. This is the case `χ = χ' ∘ det`.

Here `F` is any field with any topology, as in the published predicate, and
the representation is arbitrary; no smoothness is needed for the equivalence.

## Objects and classes

- `SupercuspidalRep.twist χ hχ hdet` twists an object of the published full
  subcategory `SupercuspidalRep` of irreducible supercuspidal smooth objects;
  irreducibility is transported by `SmoothRep.isIrreducible_twist_iff` of
  `Category/Twist`. `twist_obj` records that the underlying smooth object is
  `SmoothRep.twist`. `twistFunctor` is the restricted endofunctor, and `isoMk`
  lifts isomorphisms of underlying smooth objects.
- `SupercuspidalClass.twist χ hχ hdet` is the induced map on the published class
  space `SupercuspidalClass`, with defining equation `twist_isoClass`, the laws
  `twist_one` and `twist_twist` (product character), and
  `toSmoothDualClass_twist`: the published forgetful map to `SmoothDualClass`
  intertwines it with `SmoothDualClass.twist` of `Category/Twist`.

The explicit universe orders are those of the published pair:
`SupercuspidalRep.{uF, uV}` and `SupercuspidalClass.{uV, uF}`.

## The p-adic real-power twist

For `F : PadicField p` with a supplied realization `T`:

- `T.determinantPowerCharacter n s` is the published
  `realPowerCharacter (T.determinantNorm n) s`, that is `g ↦ |det g|^s` in
  `ℂˣ`. Here `T.determinantNorm n` is the published residue-normalized
  absolute value of the determinant, with `|ϖ| = q^(-1)`.
- `isOpen_ker_determinantPowerCharacter` (for the topology of `T`) follows
  from the published openness of the kernel of `T.determinantNorm n`, and
  `ker_determinant_le_ker_determinantPowerCharacter` from its factorization
  through the determinant.
- `T.supercuspidalClassRealPowerTwist n s` is the class twist by this
  character, and `PadicField.SupercuspidalClass.realPowerTwist s` is its
  instance on the published canonical class space
  `PadicField.SupercuspidalClass F n hn` (canonical realization, `n > 0`).

## Source correspondence

- Bernstein--Zelevinsky (1977), Proposition 1.9(f), printed page 445 / PDF
  page 6: for a character `χ` of `G`, `χ ∘ r_{U,θ} = r_{U,χθ} ∘ χ`. With
  `θ = 1` and `χ` trivial on `U`, the Jacquet functor commutes with the twist,
  so the Jacquet module of `χπ` vanishes exactly when that of `π` does. The
  source states this for the normalized functor; this module needs only the
  actual coinvariant quotient, for which the statement is the equality of
  restricted actions above. The vanishing statement is used for every
  conjugate radical, as in the published predicate.
- Bernstein--Zelevinsky (1977), section 2.4, printed page 446 / PDF page 7:
  cuspidal means admissible with vanishing Jacquet modules for all proper
  standard subgroups; admissibility is preserved by twists (published
  `Twist/AdmissibilityProof`).
- Henniart (2002), section 2.5, printed page 595 / PDF page 9: for a
  quasicharacter `χ` of `F^×` and a class `π`, `χπ` is the class of
  `g ↦ χ(det g) π(g)`, and `ν` is the quasicharacter given by the normalized
  absolute value. `SupercuspidalClass.twist` with `χ ∘ det` is this operation on
  supercuspidal classes, and `realPowerTwist s` is the twist by `ν^s`. Section
  2.6 (same page) uses these twists in `i(ρ, νρ, …, ν^(n-1)ρ)`; the module
  only supplies the twisted classes.

The originals were read at these pages. Registered sources:
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`; and
`henniart-2002-characterization`, SHA256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

The determinant-one lemma for block unipotent matrices is an elementary
internal derivation from Mathlib's block-triangular determinant formula. The
object and class packaging is internal.

## Not claimed

The module does not prove closure of supercuspidality under the smooth
contragredient, under twists by characters not trivial on `ker det`, or any
equivalence of the predicate with compactness of matrix coefficients. It does
not identify twisted supercuspidals with tensor products or relate them to
parabolic induction.
