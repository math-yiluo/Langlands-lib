# Detecting kernels and twists through End(ind_H^G ρ)

Author: Worker 5102. The three conditional theorems at the end reuse, almost line for
line, Worker 1826's proofs in `RationalSummandEndCenterReduction`. Only the two
hypotheses that came from VI.4.1 are replaced.

This supporting module serves the proofs of Renard VI.4.4: the Theorem
`RationalSummandEndCenterStatement`, the Corollary
`RationalSummandEndNoetherianStatement` and the Proposition
`RationalSummandCenterGroupAlgebraStatement`. Worker 1826's generic module
`NormalHeckeCenter` computes the center, the basis over the center, noetherianity and
the group-algebra description of End(ind_H^G ρ) from two hypotheses on a representation
B:

- `hcyc`: every map I → B is α ≫ φ for any nonzero φ : I → B and some α ∈ End(I);
- `hiso`: an End(I)-equivariant ℂ-linear bijection Hom(I, B ⊗ ω) ≃ Hom(I, B), for a
  character ω with open kernel containing H, forces B ⊗ ω ≅ B.

Worker 1826's `RationalSummandEndCenterReduction` derives both from the VI.4.1
equivalence `RationalSummandHomEquivalenceStatement`, which is not proved. This module
proves both directly for an irreducible B, from the semisimplicity of the restriction of
I to H. Hence VI.4.4 follows from the finite-length clause of VI.3.2(ii) alone.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`), VI.4.1, printed
pp.149–151 / PDF pp.155–157, and VI.4.4, printed pp.155–159 / PDF pp.161–165. The
declarations are internal helpers, and none of them is a statement of the book. The
route through kernels is not Renard's.

## Generic part (namespace `Langlands.CuspidalSupport.NormalHecke`)

G is a topological group, H a normal subgroup and ρ a smooth complex representation of
H. I = `inducedRep H ρ` = ind_H^G ρ is the published compact induction. It consists of
functions f with f(h x) = ρ(h) f(x), and G acts by right translation.

- `evalAt H ρ x` (**definition**): F ↦ F(x), as an H-equivariant map from the
  restriction of I to H into the conjugate ρ ∘ `conjHom H x`, where
  `conjHom H x h = x h x⁻¹`. Equivariance is F(x h) = F((x h x⁻¹) x) = ρ(x h x⁻¹) F(x),
  from covariance (`eval_mul_left`). `evalAt_apply` holds by `rfl`.
- `conjHom_conjHom_inv`: conjHom x (conjHom x⁻¹ k) = k.
- `translateBack H ρ x S` (**definition**): for an H-map S from ρ ∘ conjHom x into the
  restriction of I, the map w ↦ I(x) S(w) is an H-map from ρ into the restriction of I.
  The proof writes ρ(k) as (ρ ∘ conjHom x)(x⁻¹ k x) and uses
  I(x) I(x⁻¹ k x) = I(k) I(x).

From here on, H is open (`hH`) and ρ is irreducible.

- `eq_zero_of_comp_eq_zero` (**kernel detection**). Let τ₁, τ₂ be representations of G
  and T₁, T₂ G-maps out of I such that T₁ ∘ β = 0 implies T₂ ∘ β = 0 for every
  β ∈ End(I). Then T₁ F = 0 implies T₂ F = 0.

  Proof. The restriction of I to H is a semisimple ℂ[H]-module (the published
  `isSemisimpleModule_res` of `NormalSubgroupHeckeCommutative`). So the kernel K of T₁,
  as a ℂ[H]-submodule, is the supremum of its simple submodules (Mathlib's
  `IsSemisimpleModule.sSup_simples_le`). By `Submodule.iSup_induction` it suffices to
  show that T₂ vanishes on every simple ℂ[H]-submodule U ⊆ K. Let u ∈ U. If every value
  of u vanishes, then u = 0 (`compactFunctions_ext`). Otherwise u(x) ≠ 0 for some x.
  Then `evalAt H ρ x` restricted to U is a nonzero ℂ[H]-linear map between simple
  modules, because ρ ∘ conjHom x is irreducible (`isIrreducible_comp`). By Mathlib's
  `LinearMap.bijective_of_ne_zero` it is bijective. Its inverse, followed by the
  inclusion of U, is an H-map S from ρ ∘ conjHom x into the restriction of I, with image
  in K and S(u(x)) = u. Put σ = `translateBack H ρ x S` and let β ∈ End(I) correspond to
  σ under Frobenius reciprocity (the published `frobenius`), so that β(f_w) = σ(w) for
  the unit functions f_w. Then T₁(β(f_w)) = τ₁(x) T₁(S w) = 0. Since `frobenius` is
  injective, T₁ ∘ β = 0. By hypothesis T₂ ∘ β = 0, so τ₂(x) T₂(S(u(x))) = 0. Applying
  τ₂(x⁻¹) gives T₂ u = 0.

- `exists_comp_eq_of_ne_zero` (`hcyc`): for B irreducible, φ : I → B nonzero and
  ψ : I → B, there is α ∈ End(I) with α ≫ φ = ψ. The map φ is surjective
  (`surjective_of_ne_zero`), and the published `exists_end_comp_eq` lifts ψ through it.
  That lemma also rests on the semisimplicity of the restriction.

- `nonempty_twist_iso_of_linearEquiv` (`hiso`): let B be irreducible with
  Hom(I, B) ≠ 0, ω : G → ℂˣ a character with open kernel, and Ψ an End(I)-equivariant
  ℂ-linear bijection Hom(I, B ⊗ ω) ≃ Hom(I, B). Then B ⊗ ω ≅ B. The proof does not use
  that ω is trivial on H.

  Proof. Pick φ' ≠ 0 in Hom(I, B) and put φ = Ψ⁻¹(φ'), which is nonzero. Ψ and Ψ⁻¹ are
  both equivariant, so β ≫ φ = 0 if and only if β ≫ φ' = 0. Kernel detection, applied
  in both directions, gives ker φ = ker φ'. Both maps are surjective, since B and
  B ⊗ ω are irreducible (`SmoothRep.isIrreducible_twist_iff`). The linear map
  f = (liftQ of φ' along ker φ) ∘ (`quotKerEquivOfSurjective` of φ)⁻¹ : B ⊗ ω → B
  satisfies f(φ F) = φ' F. It is injective because ker φ' ⊆ ker φ, and surjective
  because φ' is. It is G-equivariant because φ and φ' are. `SmoothRep.mkIso` turns it
  into the isomorphism.

## Rational part (namespace `Langlands.CuspidalSupport`)

F is a nonarchimedean local field and G an affine group scheme of locally finite type
over F. G(F) carries `rationalPointTopology F G.X` (module-local instances), and
H⁰ = `rationalCommonNormKernel G` is open and normal. π is a smooth representation of
G(F) and ρ one of H⁰, both with carriers in `Type uV`.

- `rationalSummand_cyclic_of_isIrreducible hπ hρ`: `hcyc` for
  B = `rationalInertiaBaseLift G π`, the carrier lift of π (irreducible by
  `isIrreducible_rationalInertiaBaseLift`). It applies `exists_comp_eq_of_ne_zero`.
- `rationalSummand_twistIso_of_isIrreducible hπ hρ`: `hiso` for the same B, given that
  Hom(I, B) is nontrivial. It applies `nonempty_twist_iso_of_linearEquiv` and has
  exactly the form of the hypothesis `hiso` of `NormalHeckeCenter`.

Both replace `rationalSummand_cyclic` and `rationalSummand_twistIso` of
`RationalSummandEndCenterReduction`, which assume the VI.4.1 block membership and
equivalence.

## VI.4.4 from VI.3.2(ii) alone

Each of the following theorems has the premise
`hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}` and concludes the
corresponding VI.4.4 statement at the same universes:

- `rationalSummandEndCenter_of_finiteRestriction` gives `RationalSummandEndCenterStatement`;
- `rationalSummandEndNoetherian_of_finiteRestriction` gives
  `RationalSummandEndNoetherianStatement`;
- `rationalSummandCenterGroupAlgebra_of_finiteRestriction` gives
  `RationalSummandCenterGroupAlgebraStatement`.

Each proof introduces the statement's data and installs the instances of the
connected reductive group. It takes the finite-length clause `(hFin F G hG π hπ).2.1`
(the restriction of π to H⁰ has finite length over ℂ[H⁰]). From the published lemmas of
`RationalSummandEndCenterReduction` it then obtains:

- I ⟶ B is finite-dimensional (`finiteDimensional_rationalSummandHom`);
- I ⟶ B is nontrivial, from the injective map j (`nontrivial_rationalSummandHom`);
- ρ has countable dimension (`rank_le_aleph0_of_rationalCommonNormKernel`);
- the valuation g ↦ `rationalValuationImageProjection G g` is a degree for H⁰
  (`isDegree_rationalValuation`);
- the group T of the statements is the twist group of `NormalHeckeCenter`
  (`mem_rationalTwistGroup_iff`).

With `hcyc` and `hiso` from the rational part, the generic results of
`NormalHeckeCenter` conclude:

- **Theorem.** The center clause is `mem_center_iff_endValue`. The value
  `endValue H⁰ ρ _ α g` is the linear map w ↦ α(f_w)(g), so it vanishes exactly when
  every α(f_w)(g) does. For the rank clause, m = `Module.finrank ℂ (ρ ⟶ Res π)`. Its rank
  is m (`Module.finrank_eq_rank`), it equals the finite rank of I ⟶ B through Frobenius
  reciprocity (`inducedLiftHomEquiv`), and `exists_basis_center` gives a basis of End(I)
  over its center indexed by `Fin (m ^ 2)`.
- **Corollary.** `isNoetherianRing_end` gives noetherianity of End(I) and End(I)ᵐᵒᵖ.
  The degree group `Additive (rationalDiscreteValuationImage G)` is a finitely
  generated ℤ-module by the published basis `rationalReductiveValuationBasis G hG`.
- **Proposition.** `exists_algEquiv_center_quotient` gives the isomorphism
  e : ℂ[T ⧸ (H⁰ ∩ T)] ≃ center. Its support clause yields
  eval(ψ_t(f_w))(g) = 0 when g t ∉ H⁰. Its twist clause is applied to the homomorphism
  underlying an unramified character ω, whose kernel is open
  (`isOpen_rationalUnramifiedCharacter_ker`) and contains H⁰ (`ω.property`). It gives
  ψ_t ≫ φ = ω(t) φ for φ : I → `rationalUnramifiedTwist G ω B`.

## Relation to the source

Renard proves VI.4.4 inside the category M(G)[π], through the equivalence of VI.4.1 with
right modules over the Hecke algebra and his Lemma on the groups T ⊂ H_W ⊂ N. The
present route needs neither. The only representation-theoretic input is the
decomposition of the restriction of I to H⁰ into simple submodules, which is the
semisimplicity step in Renard's projectivity argument for (VI.4.1.1). Kernel detection
replaces the full faithfulness of Hom(I, ·) on the block. The finiteness of m comes
from VI.3.2(ii), not from Renard's index formula m = [N : H_W].
