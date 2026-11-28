# Elliptic elements of the Lie algebra of `Aˣ`

The module `Langlands.HarmonicAnalysis.UnitConjugation.EllipticElement` defines, for a ring `A`
regarded as the Lie algebra of its unit group `Aˣ` (adjoint action `X ↦ u X u⁻¹`), the
elliptic elements of `A`, and proves three elementary facts about them.

## Definition

In the namespace `Langlands.HarmonicAnalysis.UnitConjugation`, for `A : Type v` with
`[Ring A]`:

- `IsEllipticElement (X : A) : Prop`: every idempotent `e` of `A` (`IsIdempotentElem e`) with
  `e * X = X * e` is central, `e * a = a * e` for every `a : A`.

## Results

- `not_isEllipticElement_iff`: `X` is not elliptic exactly when some idempotent `e` commutes
  with `X` and fails to commute with some `a : A`.
- `isEllipticElement_of_forall_commute`: if every idempotent of `A` is central (for instance if
  `A` is commutative), every element is elliptic.
- `isEllipticElement_map_iff`: `IsEllipticElement (σ X) ↔ IsEllipticElement X` for a ring
  automorphism `σ : A ≃+* A`; `isEllipticElement_conj_iff`: in particular ellipticity is
  invariant under conjugation `X ↦ u X u⁻¹` by a unit `u`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15), §1,
printed p. 5 (PDF p. 20): "Fix a Cartan subalgebra `h` of `g` and put `h' = h ∩ g'`. Let `A`
denote the split component of the corresponding Cartan subgroup of `G`. `h` is called elliptic
if `A` lies in the center of `G`."

The definition is derived from this one for the regular elements `X ∈ g'` (`regularSet`) of a
finite-dimensional semisimple algebra `A` over a field `F` of characteristic zero, for which it
is intended; the module itself states the condition for every element of every ring and does
not prove the facts below.

- `G = Aˣ`, the group of `F`-points of `GL₁(A)`, with Lie algebra `A`. For regular `X` the
  centralizer `h` of `X` in `A` is the Cartan subalgebra containing `X`, a commutative semisimple
  `F`-algebra, that is a finite product `E₁ × ⋯ × E_r` of finite field extensions of `F`, and the
  corresponding Cartan subgroup is the centralizer `hˣ` of `X` in `Aˣ`
  (`conjugationCentralizer X`).
- `hˣ` is the group of `F`-points of the torus `T = ∏ⱼ R_{Eⱼ/F} G_m`; its maximal `F`-split
  subtorus is `∏ⱼ G_m`, embedded through `F ⊆ Eⱼ`, so the split component of `hˣ` is the group
  of the elements `∑ⱼ tⱼ εⱼ` with `tⱼ ∈ Fˣ`, where `ε₁, …, ε_r` are the primitive idempotents
  of `h`.
- The centre of `Aˣ` is the unit group of the centre of `A`. The split component lies in it
  exactly when every `εⱼ` is central in `A` (take `tⱼ = 2` and `tᵢ = 1` for `i ≠ j`), that is
  when every idempotent of `h`, a sum of some of the `εⱼ`, is central.
- The idempotents of `A` commuting with `X` are the idempotents of `h`, since `h` is the
  centralizer of `X`.

So for regular `X`, `IsEllipticElement X` holds exactly when the Cartan subalgebra containing
`X` is elliptic. For `A = M_n(F)` it says that `F[X]` is a field: the characteristic polynomial
of `X` is irreducible.
