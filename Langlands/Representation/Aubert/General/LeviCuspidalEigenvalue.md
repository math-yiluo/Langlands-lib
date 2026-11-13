# The cuspidal eigenvalue of the unadjusted operator inside a standard Levi

Authors: Worker 1254 (original proof), Worker 3941 (reuse of published helpers).

This module proves the inside-Levi form of Aubert, Theorem 1.7(4)
(Trans. Amer. Math. Soc. 347 (1995), printed p.2181, PDF p.3): if `σ` is a
representation of the standard Levi `L_J` all of whose proper Jacquet modules
vanish, then `D_{L_J}(σ) = (-1)^{|J|} σ`. Aubert's proof is the remark that
the assertion "résulte clairement de la définition de D_G" (Definition 1.5,
`D_G = Σ_{I ⊆ S} (-1)^{|I|} i_{L_I} ∘ r_{L_I}`, with cuspidality meaning
`r_{L_I}(π) = 0` for every `I ⊊ S`). It is the step used inside `L_J` by the
proof of Corollary 1.10(a), printed p.2183 / PDF p.5, which "résulte
immédiatement du théorème 1.7".

The Lean statements are slightly more general than the literature. No
irreducibility of `σ` is assumed, only finite length and the vanishing of the
proper Jacquet modules as zero objects. The family of decompositions is
arbitrary. The other declarations are internal adapters for this argument.
No new literature assertion is introduced.

## Reused published declarations

- `Langlands.Aubert.General.class_eq_zero_of_isZero` (module
  `CorollaryExchangeAssembly`): a finite-length smooth representation that is
  a zero object has class `0` in the exact finite-length Grothendieck group.
- `Langlands.Aubert.General.RationalPointFamily.inductionJacquetClass_of_top_bot`
  (module `RationalCuspidalEigenvalueProof`): for a semidirect decomposition
  with `P = ⊤`, `U = ⊥` and a unimodular radical, the class of
  `(inductionJacquetFunctor h hU).obj A` equals the class of `A`. Despite its
  namespace, the theorem is stated for an arbitrary locally compact
  nonarchimedean group.

## Declarations

- `IsSemidirectDecomposition.disjoint_levi_unipotent`: in a semidirect
  decomposition `P = M ⋉ U`, the subgroups `M` and `U` of `G` meet trivially.
  It is read off the complement field of the decomposition.

- `isUnimodularModulus_of_eq_bot`: the trivial subgroup `U = ⊥` is
  unimodular in the sense of `IsUnimodularModulus`. Every element of `U` is
  `1`, and the modulus is a homomorphism.

- `alternatingOperator_ofRepresentation_of_isZero_jacquet`: let a finite
  family `(P I, M I, U I)`, `I : Finset ι`, of semidirect decompositions with
  finite-length witnesses `hfl` satisfy `P univ = ⊤` and `U univ = ⊥`. Let `A`
  be a finite-length representation such that `(jacquetFunctor (h I) (hU I)).obj A`
  is a zero object for every `I ≠ univ`. Then the published unadjusted
  operator `alternatingOperator P M U h hU hfl` maps `[A]` to
  `(-1)^{card ι} • [A]`. The proof expands the defining sum
  `Σ_I (-1)^{|I|} i_I(r_I [A])` (`alternatingOperator_apply`) and keeps only
  the full term (`Finset.sum_eq_single`). Each proper term vanishes:
  `jacquetK0_ofRepresentation` turns `r_I [A]` into the class of the Jacquet
  module, which is `0` by `class_eq_zero_of_isZero`. The full term is `[A]`.
  `jacquetK0_ofRepresentation` and `inductionK0_ofRepresentation` give the
  class of `i_univ(r_univ A)`, and `inductionJacquetClass_of_top_bot`
  identifies it with `[A]`. The unimodularity input comes from
  `isUnimodularModulus_of_eq_bot`.

- The published `CuspidalEmbedding.leviIndex_univ` from
  `RationalLeviCuspidalJacquet` supplies `leviIndex J univ = J`: the image of
  the full finset of the subtype `J` under the subtype inclusion is `J`.

- `leviAlternatingOperator_ofObject_of_isCorollaryLeviCuspidal` (main
  result): let `J : Finset ι`, let the ambient
  `P J = M J ⋉ U J` be a semidirect decomposition, and let `M J` be closed.
  Take the inside-Levi decompositions `hJ`, the closedness proofs `hU` and the
  finite-length witnesses `hfl` exactly as in the published
  `leviAlternatingOperator`. Then for every finite-length object `σ` of
  `M J` satisfying the published `IsCorollaryLeviCuspidal P M U J hM hJ hU σ`,

  `leviAlternatingOperator P M U J hM hJ hU hfl [σ] = (-1)^{|J|} • [σ]`.

  The restricted family at `leviIndex J univ = J` has
  `(P J).subgroupOf (M J) = ⊤`, because `M J ≤ P J`, and
  `(U J).subgroupOf (M J) = ⊥`, by the disjointness lemma. The previous
  theorem applies with index type the subtype `J`, whose cardinality is
  `J.card`. `IsCorollaryLeviCuspidal` is exactly its vanishing hypothesis.

## Scope

The result holds for any finite-length witnesses `hfl`. In particular it
applies, definitionally, to `rationalLeviAlternatingOperator`, which is
`leviAlternatingOperator` with the witnesses
`standardLeviParabolicFiniteLength`. The module proves nothing about
induction compatibility `D_G ∘ i_J = i_J ∘ D_{L_J}` (Theorem 1.7(2)) or about
Corollary 1.10(a) itself. It makes no field, characteristic, splitness or
irreducibility assumption. It uses no Langlands classification, character
independence, geometric lemma, adjointness or cuspidal-support theorem.
