# Renard VI.4.4 from VI.4.1 and VI.3.2(ii): conditional reductions

Author: Worker 1826.

This module derives the three statements of Renard VI.4.4 — the Theorem
`RationalSummandEndCenterStatement`, the Corollary
`RationalSummandEndNoetherianStatement` and the Proposition
`RationalSummandCenterGroupAlgebraStatement` — from two other published statements:

- `RationalSummandHomEquivalenceStatement` (Renard VI.4.1, Theorem): for π irreducible
  cuspidal and ρ an irreducible smooth representation of ⁰G with an injective
  equivariant map j : ρ → π|_{⁰G}, the compact induction I = ind_{⁰G}^G ρ lies in the
  inertia block of the carrier lift of π, and `Hom(I, •)` (Mathlib's
  `preadditiveCoyonedaObj`) is an equivalence from that block to modules over
  (End I)ᵐᵒᵖ;
- `RationalNormKernelFiniteRestrictionStatement` (Renard VI.3.2(ii)); only its second
  clause is used: the restriction of an irreducible π to ⁰G has finite length over
  the group algebra of ⁰G.

Neither premise is proved in the Library at the time of writing, so this module
proves none of the three targets. It provides three implications, each with the
target's quantifiers, premises and universes:

- `rationalSummandEndCenter_of_homEquivalence hEq hFin`;
- `rationalSummandEndNoetherian_of_homEquivalence hEq hFin`;
- `rationalSummandCenterGroupAlgebra_of_homEquivalence hEq hFin`;

where `hEq : RationalSummandHomEquivalenceStatement.{uF, uV}` and
`hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}`.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, printed
pp.155–159 / PDF pp.161–165; VI.4.1, printed pp.149–151 / PDF pp.155–157; VI.3.2,
printed pp.143–144 / PDF pp.149–150.

The mathematical content is in the generic module
`Langlands.Representation.CuspidalSupport.NormalHeckeCenter` (accepted candidate,
awaiting integration into the Library), which computes the center, the basis over the
center, noetherianity and the group-algebra description of End(ind_H^G ρ) for an open
normal subgroup H, given a degree p : G → ι for H and a representation B satisfying
explicit hypotheses (`hrank`, finite-dimensional and nontrivial Hom(I, B), `hcyc`,
`hiso`, `hT`). This module checks those hypotheses for G = G(F), H = ⁰G
(`rationalCommonNormKernel G`) and B = πL = `rationalInertiaBaseLift G π`, the carrier
lift of π. All declarations here are internal helpers; none of them is a statement of
the book.

## Generic lemmas (namespace `Langlands.CuspidalSupport.NormalHecke`)

**Finite dimension of Hom spaces.** k is a field and R a k-algebra.

- `finiteDimensional_linearMap_of_isSimpleModule S Q`: for simple R-modules S and Q
  (with compatible k-structures) such that End_R(S) is finite-dimensional over k,
  Hom_R(S, Q) is finite-dimensional over k. If some e : S → Q is nonzero it is
  bijective (Schur, Mathlib's `LinearMap.bijective_of_ne_zero`), and g ↦ e⁻¹ ∘ g is
  an injective k-linear map into End_R(S); otherwise Hom_R(S, Q) = 0.
- `finiteDimensional_linearMap_of_isFiniteLength S hM`: if moreover M has finite length
  over R (Mathlib's `IsFiniteLength`), then Hom_R(S, M) is finite-dimensional for every
  compatible k-structure on M. Induction on `IsFiniteLength`: for N ⊂ M with M/N simple,
  the kernel of f ↦ (M → M/N) ∘ f lies in the image of Hom_R(S, N), finite-dimensional
  by induction, and its image lies in Hom_R(S, M/N), finite-dimensional by the previous
  lemma; conclude with rank–nullity (`LinearMap.rank_range_add_rank_ker`).
- `homLinearEquiv A B`, reused from `NormalSubgroupHeckeCommutative`, is the
  ℂ-linear identification of morphisms of smooth representations A ⟶ B with
  their equivariant linear maps (`SmoothRep.hom`, inverse `SmoothRep.ofHom`).
- `finiteDimensional_hom_of_isFiniteLength ρ B hrank hB`: for a group H, an irreducible
  smooth ρ with `Module.rank ℂ ρ ≤ ℵ₀` and a smooth B of finite length over ℂ[H],
  ρ ⟶ B is finite-dimensional. Schur's lemma for countable dimension
  (`countableDimensionalSchur`) shows that the equivariant endomorphisms of ρ are the
  scalars; Mathlib's `Representation.IntertwiningMap.equivLinearMapAsModule` turns
  equivariant maps into ℂ[H]-linear maps of the associated modules, and the previous
  lemma applies.

**Irreducible subquotients, twists and characters.**

- `nonempty_iso_of_isSubquotient hA hD h`: an irreducible smooth D that is a subquotient
  (`SmoothRep.IsSubquotient`) of an irreducible smooth A is isomorphic to A. By
  `SmoothRep.isSubquotient_iff_exists` there are C, an injective i : C → A and a
  surjective q : C → D. As D ≠ 0, i ≠ 0, so i is bijective (A irreducible); then
  q ∘ i⁻¹ : A → D is surjective and nonzero, hence injective (A irreducible).
- `continuous_of_isOpen_ker ω hω`: a homomorphism from a topological group into a
  topological monoid with continuous multiplication is continuous when its kernel is
  open (it is constant near 1; Mathlib's `continuous_of_continuousAt_one`).
- `liftTwistIso ω hω π` (**definition**): the isomorphism
  (universe lift of π ⊗ ω) ≅ (universe lift of π) ⊗ ω, the identity on the common
  carrier `ULift π` (`SmoothRep.mkIso`).

## The rational setting (namespace `Langlands.CuspidalSupport`)

F is a nonarchimedean local field and G an affine group scheme of locally finite type
over F; G(F) = `GroupScheme.rationalPoints G` carries `rationalPointTopology F G.X`
(module-local instances, with the topological-group structure
`rationalPoint_isTopologicalGroup`). ⁰G = `rationalCommonNormKernel G` is open
(`isOpen_rationalCommonNormKernel`) and normal (instance
`rationalCommonNormKernel_normal`).

- `isDegree_rationalValuation G`: g ↦ `Additive.ofMul (rationalValuationImageProjection G g)`,
  with values in ι = `Additive (rationalDiscreteValuationImage G)`, is a degree for ⁰G
  (`IsDegree`): it is additive, and vanishes exactly on ⁰G by
  `rationalValuationImageProjection_ker`.
- `rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ`: an irreducible smooth ρ of ⁰G has
  countable dimension. G(F) is second countable (F is, and G(F) embeds in its affine
  points), so ⁰G is separable and `Whittaker.MirabolicRigidity.rank_le_aleph0` applies.
- `rationalUnramifiedOfOpen G ω hω hωH` (**definition**): a homomorphism ω : G(F) → ℂˣ
  with open kernel containing ⁰G, as an element of the group of unramified characters
  `unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)`; its continuity
  is `continuous_of_isOpen_ker`, and its underlying homomorphism is ω.
- `mem_rationalTwistGroup_iff g`: g lies in
  T = ⨅ over unramified ω with π ⊗ ω ≅ π of ker ω (the group T of the targets) if and
  only if ω(g) = 1 for every ω : G(F) → ℂˣ with open kernel containing ⁰G and
  πL ⊗ ω ≅ πL. The two conditions correspond through `rationalUnramifiedOfOpen`,
  `liftTwistIso` and the full faithfulness of the carrier lift
  (`SmoothRep.fullyFaithfulUniverseLiftFunctor`). This is the hypothesis `hT` of
  `NormalHeckeCenter` for B = πL.

From now on π is irreducible (`hπ`).

- `isIrreducible_rationalInertiaBaseLift hπ`: πL is irreducible
  (`SmoothRep.isIrreducible_universeLift_iff`).
- `rationalInertiaBlockProperty_baseLift hπ`: πL lies in the inertia block of πL: an
  irreducible subquotient of πL is isomorphic to πL (`nonempty_iso_of_isSubquotient`),
  hence inertia-related to it.
- `rationalInertiaBlockProperty_baseLift_twist hπ ω hω hωH`: πL ⊗ ω lies in the same
  block, for ω with open kernel containing ⁰G: its irreducible subquotients are
  isomorphic to πL ⊗ ω, the twist of πL by the unramified character
  `rationalUnramifiedOfOpen G ω hω hωH`.
- `finiteDimensional_rationalSummandHom hρ hlen`: if ρ is irreducible and the
  restriction of π to ⁰G has finite length (`hlen`), then I ⟶ πL is finite-dimensional:
  it is identified with ρ ⟶ π|_{⁰G} by Frobenius reciprocity
  (`inducedLiftHomEquiv`), which is finite-dimensional by
  `finiteDimensional_hom_of_isFiniteLength`.
- `nontrivial_rationalSummandHom hρ j hj`: an injective j : ρ → π|_{⁰G} (ρ ≠ 0, as ρ is
  irreducible) gives a nonzero map I → πL through `inducedLiftHomEquiv`.

Assume further `hmem`: I lies in the inertia block of πL, and that `Hom(P, •)` is an
equivalence of categories for the block object P = ⟨I, hmem⟩ (instance argument
`hEqv`). These are the conclusions of VI.4.1.

- `rationalSummand_cyclic hπ hmem φ hφ ψ`: for maps φ, ψ : I → πL with φ ≠ 0 there is
  α ∈ End(I) with α ≫ φ = ψ (the hypothesis `hcyc`). Since πL is irreducible, φ is
  surjective, hence an epimorphism P → ⟨πL, _⟩ in the block
  (`rationalInertiaBlock_epi_iff_surjective`). The equivalence `Hom(P, •)` preserves
  epimorphisms, and epimorphisms of modules are surjective
  (`ModuleCat.epi_iff_surjective`), so x ↦ x ≫ φ is surjective on End(P) = End(I).
- `rationalSummand_twistIso hπ hmem ω hω hωH Ψ hΨ`: for ω with open kernel containing
  ⁰G, an ℂ-linear bijection Ψ : (I ⟶ πL ⊗ ω) ≃ (I ⟶ πL) with Ψ(α ≫ φ) = α ≫ Ψ(φ) gives
  an isomorphism πL ⊗ ω ≅ πL (the hypothesis `hiso`). Both objects lie in the block;
  Ψ is an isomorphism of (End P)ᵐᵒᵖ-modules Hom(P, πL ⊗ ω) ≅ Hom(P, πL)
  (`LinearEquiv.toModuleIso`), which the fully faithful functor `Hom(P, •)` reflects to
  an isomorphism in the block (`Functor.preimageIso`), and the inclusion of the block
  sends it to an isomorphism of smooth representations.

## The three reductions

Each proof introduces the target's data, obtains the block membership and the
equivalence from `hEq` applied to the same data, and the finite-length clause from
`(hFin F G hG π hπ).2.1`. With the lemmas above, all hypotheses of `NormalHeckeCenter`
hold for H = ⁰G, the degree of `isDegree_rationalValuation` and B = πL.

- `rationalSummandEndCenter_of_homEquivalence`. The center clause is
  `mem_center_iff_endValue`, since `endValue (⁰G) ρ _ α g` is the linear map
  w ↦ eval(α(f_w))(g) (`endValue_apply`, by definition), so it vanishes exactly when
  every value in the target vanishes. For the rank clause, m is
  `Module.finrank ℂ (ρ ⟶ π|_{⁰G})`: this space is finite-dimensional, so its rank is
  m (`Module.finrank_eq_rank`), and it has the same dimension as I ⟶ πL
  (`inducedLiftHomEquiv`), so the basis of `exists_basis_center` is indexed by
  `Fin (m ^ 2)`.
- `rationalSummandEndNoetherian_of_homEquivalence` is `isNoetherianRing_end`; the degree
  group ι is a finitely generated ℤ-module, by the published basis
  `rationalReductiveValuationBasis G hG`.
- `rationalSummandCenterGroupAlgebra_of_homEquivalence` is
  `exists_algEquiv_center_quotient`: its support condition gives the vanishing of
  eval(ψ_t(f_w))(g) when g t ∉ ⁰G, and its twist condition, for the homomorphism
  underlying an unramified character ω (open kernel by
  `isOpen_rationalUnramifiedCharacter_ker`, containing ⁰G by membership), gives
  ψ_t ≫ φ = ω(t) φ for φ : I → `rationalUnramifiedTwist G ω πL`.

## Relation to the source

Renard obtains the finiteness of m as an index: m = [N : H] for a subgroup H of G
containing ⁰G Z(G), which has finite index in G (VI.4.4, preliminary remarks). Here m
is finite because π|_{⁰G} has finite length, the second clause of
`RationalNormKernelFiniteRestrictionStatement`.

In the book, VI.4.1 enters through the equivalence M(G)[π] ≃ mod-A, which identifies
the simple right A-modules with the spaces Hom_{⁰G}(ρ, π ⊗ ω) (Corollary of VI.4.3);
the proof of the Theorem then compares the scalars by which central elements act on
them. Here VI.4.1 is used in two places: the equivalence `Hom(Π, •)` preserves
epimorphisms, which makes Hom(Π, π) generated by each nonzero element (`hcyc`), and it
reflects isomorphisms, so an End(Π)-equivariant bijection
Hom(Π, π ⊗ ω) ≃ Hom(Π, π) comes from an isomorphism π ⊗ ω ≅ π (`hiso`). Renard's Lemma
of VI.4.4 (the groups T ⊂ H ⊂ N and the restriction isomorphism (VI.4.4.3)) is not
used; the center, the basis and the group algebra come from the abstract rank-one
graded algebra of `NormalHeckeCenter` (see the Markdown of that module).
