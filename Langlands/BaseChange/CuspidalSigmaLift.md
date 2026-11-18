# The σ-lift of a supercuspidal representation: definitions

This module `Langlands.BaseChange.CuspidalSigmaLift` (namespace `Langlands.BaseChange`)
defines the objects in which Henniart–Lemaire describe the σ-lift of a supercuspidal
representation of `GL_n`: the characters of `F^×` trivial on the norms from `E^×` (the group
`K(E/F)`), the stabilizer of the isomorphism class of a representation `π` of `GL_n(F)` in
that group, and the product `P × P^σ × ⋯ × P^{σ^{s-1}}` of the Galois conjugates of a
representation `P` of `GL_{n₁}(E)`. It proves the subgroup axioms, a membership lemma, and
that the product with one factor is that factor. The two statements that use these
definitions are in the modules `Langlands.BaseChange.CuspidalSigmaLiftStructureStatement`
and `Langlands.BaseChange.CuspidalSigmaLiftExistenceStatement`.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
  (PDF page = printed page + 8). Cited below as HL.
  - II.1.3 (printed p. 56): `K(E/F)` is the group of characters of `F^×` that are trivial
    on `N_{E/F}(E^×)`; `Π^σ` is the representation `g ↦ Π(g^σ)`.
  - II.4.12, Proposition and Remarque (printed pp. 96–97): the stabilizer of the
    isomorphism class of a cuspidal representation in `K(E/F)`, and the products
    `Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{s-1}}`.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, Lemma 6.10
  (printed p. 62): the products `T × T^σ × ⋯ × T^{σ^{ℓ-1}}` in prime degree `ℓ`.

## Setting and notation

`GL_n(R)` is the Library's `Langlands.GeneralLinear n R` and `det` is
`GeneralLinear.determinant : GL_n(R) →* Rˣ`. `entrywiseAut σ n : GL_n(E) ≃* GL_n(E)` is the
entrywise action `g ↦ g^σ` of `σ : E ≃ₐ[F] E`, from the module `Langlands.BaseChange.Norm`
(Task 7405). For a representation `P` of `GL_m(E)` and `i : ℕ`, `P^{σ^i}` denotes
`P.comp (entrywiseAut (σ ^ i) m).toMonoidHom`, the representation `g ↦ P(g^{σ^i})`.
`twist χ ρ` is the Library's `Langlands.twist`, the representation `g ↦ χ(g) ρ(g)` on the
space of `ρ`.

## Definitions

1. `IsNormTrivial E κ`, for a field `F`, a commutative `F`-algebra `E` (explicit argument)
   and a character `κ : Fˣ →* ℂˣ`, holds when `κ (N_{E/F}(x)) = 1` for every `x : Eˣ`. In
   Lean the norm on units is `Units.map (Algebra.norm F : E →* F)`, built from Mathlib's
   `Algebra.norm`. The characters with this property form HL's group `K(E/F)` (II.1.3).
   Mathlib's `Algebra.norm F` is the determinant of multiplication when `E` has a finite
   `F`-basis and is the constant `1` otherwise; in the statements of this programme `E` is a
   finite field extension of `F`, so the norm is the usual one.
2. `normTwistStabilizer E π : Subgroup (Fˣ →* ℂˣ)`, for `F` and `E` as in 1, `n : ℕ` and a
   representation `π : Representation ℂ (GL_n(F)) V` on a complex vector space `V`, is the
   subgroup whose elements are the `κ` with `IsNormTrivial E κ` and
   `Nonempty (π.Equiv (twist (κ.comp det) π))`, that is, `κ ∈ K(E/F)` and
   `π ≅ (κ ∘ det) ⊗ π`. It is the stabilizer of the isomorphism class of `π` in `K(E/F)`
   (HL II.4.12, Proposition: "le stabilisateur de la classe d'isomorphisme … dans
   `K(E/F)`"). The subgroup axioms are proved from the Library's `twist_one`,
   `twist_twist`, `twist_inv_twist` and `twistEquiv`. The name differs from the Library's
   `Langlands.CuspidalSupport.TwistStabilizerKernel.twistStabilizer`, which is the
   stabilizer in the group of unramified characters, a different object.
3. `sigmaOrbitProduct σ s hn₁ P`, for a field `F`, a nonarchimedean local field `E`
   (`[Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]`) with
   `[Algebra F E]`, `σ : E ≃ₐ[F] E`, `s n₁ : ℕ`, `hn₁ : 0 < n₁` and
   `P : Representation ℂ (GL_{n₁}(E)) W`, is
   `(LocalFieldData.ofInstances E).normalizedProductInduced
   (GeneralLinear.BlockShape.uniform s n₁ hn₁) (fun i => P^{σ^i})`, a representation of
   `GL_{s * n₁}(E)`. This is HL's product `P × P^σ × ⋯ × P^{σ^{s-1}}` (II.4.12): see the
   section on the product below.

## Lemmas (with proofs)

4. - `isNormTrivial_one : IsNormTrivial E 1`, the trivial character is norm-trivial.
   - `IsNormTrivial.mul`: if `κ` and `η` are norm-trivial, so is `κ * η`.
   - `IsNormTrivial.inv`: if `κ` is norm-trivial, so is `κ⁻¹`.
   - `mem_normTwistStabilizer`: `κ ∈ normTwistStabilizer E π ↔ IsNormTrivial E κ ∧
     Nonempty (π.Equiv (twist (κ.comp det) π))` (by `Iff.rfl`).

   In `IsNormTrivial.mul` and `IsNormTrivial.inv` the algebra `E` is an implicit argument
   (it is determined by the hypotheses); in `isNormTrivial_one` it is explicit.
5. `sigmaOrbitProduct_one_equiv`: for every `P` that is smooth (the Library's `IsSmooth`,
   for the topology of `GL_{n₁}(E)` coming from `E`),
   `Nonempty ((sigmaOrbitProduct σ 1 hn₁ P).Equiv
   (P.comp (GeneralLinear.reindex (R := E) (finCongr (Nat.one_mul n₁).symm)).symm.toMonoidHom))`:
   for `s = 1` the product is `P` itself, after the rank transport
   `GL_{1 * n₁}(E) ≃* GL_{n₁}(E)`.

   Proof. The one-block shape `BlockShape.uniform 1 n₁ hn₁` has length `1` by `rfl`. Its
   only index is `0`, and the factor `P^{σ^0}` equals `P` because
   `entrywiseAut (σ ^ 0) n₁` is the identity (`pow_zero` and `entrywiseAut_one_apply` of
   the Norm module); so the factor is smooth. The Library's
   `LocalFieldData.singleBlockNormalizedProductEquiv` then gives an isomorphism of the
   product with `P^{σ^0}` composed with the inverse of `GeneralLinear.reindex`, and the
   identity of `W` is an isomorphism from that representation to `P` composed with the
   same map, again because `entrywiseAut (σ ^ 0) n₁ g = g`.

## The group `K(E/F)`

Let `F` be a nonarchimedean local field and `E/F` a cyclic extension of degree `l`. By local
class field theory, `N_{E/F}(E^×)` is an open subgroup of `F^×` of index `l` and
`F^×/N_{E/F}(E^×)` is cyclic (isomorphic to `Gal(E/F)`). Hence `K(E/F)` is cyclic of order
`l`, and its elements, which factor through this finite quotient by an open subgroup, are
automatically continuous; definition 1 therefore asks no continuity. These facts are not
formalized here. Since `K(E/F)` is finite, so is `normTwistStabilizer E π`, and its order
divides `l` by Lagrange's theorem; the statement modules use its order as
`Nat.card (normTwistStabilizer E π)` (where `Nat.card` of an infinite type is `0`; the
statement modules explain why this causes no problem).

## Convention for `Π^σ`

`P^{σ^i}` is `g ↦ P(g^{σ^i})`, as in HL II.1.3 and in Task 7432 (`SigmaIntertwiner`). The set
`{P^{σ^i} : 0 ≤ i < s}` of factors of `sigmaOrbitProduct σ s hn₁ P` is the orbit of `P`
under the group generated by `σ` when `σ^s` generates the stabilizer of the class of `P`;
with the other convention (`g ↦ P(g^{σ⁻¹})`) one gets the same factors in another order.
For pairwise unlinked cuspidal factors (the case of interest, see the existence statement)
the product does not depend on the order of the factors (Bernstein–Zelevinsky); this is
not formalized here.

## The product

`sigmaOrbitProduct` is normalized parabolic induction, which is the meaning of HL's
notation `×` (the Bernstein–Zelevinsky product). Concretely, `GeneralLinear.BlockShape.uniform
s n₁ hn₁` (`Langlands/Representation/Classification/Segments.lean`) is the block shape with
`s` diagonal blocks of size `n₁` of `GL_{s * n₁}`, and
`LocalFieldData.normalizedProductInduced` (`Langlands/AllField/Representation/Induction/BlockFactors.lean`)
induces, from the standard block upper triangular parabolic subgroup of that shape, the
external tensor product of the block representations twisted by the square root of the
modulus character, computed with the normalized absolute value of `E`. The `i`-th block
carries `P^{σ^i}`. The carrier of `sigmaOrbitProduct σ s hn₁ P` is the Library's space of
smooth induced functions (`Induction.SmoothFunctions`), and its topologies are those of
`LocalFieldData.ofInstances E`, that is, the given topology of `E`. The statement modules
transport it to `GL_n(E)` along `GeneralLinear.reindex (finCongr h)` for `h : s * n₁ = n`,
the same rank transport as in the Library's `singleBlockNormalizedProductEquiv` and in
lemma 5.

No continuity of `σ` is assumed in definition 3, and no relation between the topologies of
`F` and `E`. When `E` is a finite extension of a nonarchimedean local field `F` with the
topology induced from `F` (as in the statement modules, `[IsModuleTopology F E]`), every
`F`-algebra automorphism of `E` is continuous, being `F`-linear on a finite-dimensional
space; the definition does not need this, and lemma 5 only uses the factor `P^{σ^0} = P`.

## Prime degree

If the degree `l` is prime, the order `s` of the stabilizer divides `l`, so `s = 1` or
`s = l`. Lemma 5 gives the form of the product for `s = 1`: it is the single factor `P`.
This is how the structure statement yields the first case of Arthur–Clozel's Lemma 6.10
(see `CuspidalSigmaLiftStructureStatement.md`).

## Provenance

Definitions 1–3 are HL's objects (II.1.3, II.4.12) expressed with the Library's character
twist, normalized product induction and block shapes. Lemmas 4 are internal: they supply
the subgroup structure of definition 2. Lemma 5 is internal: it records the case `s = 1` of
definition 3 in the form used to derive Arthur–Clozel's dichotomy in prime degree.
