# Central extensions of spectra of Hopf algebras

Worker 1395 wrote this module. It translates the geometric hypotheses of
`CentralTorusExtensionStatement` into Hopf-algebra conditions for affine group
schemes given as spectra of Hopf algebras. Let `R` be a commutative ring,
`φ : B ⟶ A` and `π : A ⟶ C` maps in `CommHopfAlgCat R`, and let
`z = (hopfSpec R).map π.op` and `p = (hopfSpec R).map φ.op`. Suppose `z` is a
central closed subgroup and `p` is an fppf quotient map with kernel the range
of `z`. Then `π` is surjective, `φ` is faithfully flat, `π ∘ φ` is trivial, the
two coactions of `C` on `A` through `π` agree, and coaction-invariant elements
of `A` come from `B`. For split tori `Spec B = 𝔾_m^I` and `Spec C = 𝔾_m^J`,
these are the fields of `CentralTorusExtensionHopf.IsCentralExtension`
([`CentralTorusExtensionHopf`](../../Algebra/CentralTorusExtensionHopf.md)).

The module is an internal helper for the proof of
[`CentralTorusExtensionStatement`](CentralExtensionProof.md). Points of
`hopfSpec` are handled with
[`HopfSpecPoints`](../HopfSpecPoints.md). The translations are standard and are
not taken from a numbered result of a source.

## Contents

* `surjective_of_isClosedImmersion`: if `Spec.map f` is a closed immersion, the
  ring map `f` is surjective. Mathlib's
  `IsClosedImmersion.isAffine_surjective_of_isAffine` gives surjectivity on
  global sections, and `Scheme.ΓSpecIso_naturality` identifies that map with
  `f`.
* `surjective_of_isClosedSubgroup π h`: if `Spec π` is a closed subgroup, `π`
  is surjective.
* `faithfullyFlat_of_isFppfQuotient φ h`: if `Spec φ` is an fppf quotient map,
  `φ` is faithfully flat. Flat and surjective spectrum maps correspond to
  faithfully flat ring maps (`flat_and_surjective_SpecMap_iff`).
* `comp_eq_of_range_kernelι φ π h`: if the range of `kernelι (Spec φ)` is the
  range of `Spec π`, then `π ∘ φ = algebraMap ∘ ε`. The point of `Spec A` with
  values in `Spec C` classified by `π` lies in the kernel of `Spec φ`, which
  says exactly this by `specPoint_comp_map`, `specPoint_one` and
  `specPoint_injective`.
* `rTensor_comul_eq_of_isCentral π hc a`: if `Spec π` is central, then
  `(π ⊗ id)(Δ a) = comm ((id ⊗ π)(Δ a))`. Take the points of `Spec A` with
  values in `Spec (C ⊗ A)` classified by `includeLeft ∘ π` and by
  `includeRight`. The first lies in the centre (`commute_of_mem_center`), so
  the two products agree. By `specPoint_mul` this is the equality of the two
  convolutions, evaluated at `a`.
* `exists_eq_of_lTensor_comul_eq φ π hz hq a ha`: if `Spec π` is a
  monomorphism, `Spec φ` is an fppf quotient map with kernel the range of
  `Spec π`, and `(id ⊗ π)(Δ a) = a ⊗ 1`, then `a = φ b` for some `b`. Regard
  `A` as a faithfully flat `B`-algebra through `φ`. The two inclusions
  `A → A ⊗[B] A` give points `x, y` of `Spec A` with the same image under
  `Spec φ`. By `IsFppfQuotient.fibers_iff`, `x = y · z(ω)` for a point `ω` of
  `Spec C`. Evaluating at `a` and using the hypothesis on `a` gives
  `a ⊗ 1 = 1 ⊗ a` in `A ⊗[B] A`. Faithfully flat descent
  (`Algebra.IsEffective.of_faithfullyFlat` and
  `eqLocus_includeLeft_includeRight`) then puts `a` in the image of `B`.
* `isCentralExtension φ π hz hc hq`: over a field `K`, for
  `φ : Diagonalizable.hopfAlgebra (CommRingCat.of K) (I → ℤ) ⟶ A` and
  `π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) (J → ℤ)`, the
  hypotheses `IsClosedSubgroup (Spec π)`, `IsCentral (Spec π)` and
  `IsFppfQuotient (range (Spec π)) (Spec φ)` give
  `CentralTorusExtensionHopf.IsCentralExtension φ.hom π.hom`. The five fields
  come from the lemmas above. For `invariants`, an element of degree `0`
  satisfies `(id ⊗ π)(Δ a) = a ⊗ 1` after `scalarTensorEquiv`, and a closed
  immersion is a monomorphism.
