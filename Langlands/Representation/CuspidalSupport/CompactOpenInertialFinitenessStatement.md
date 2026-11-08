# Compact open subgroups meet finitely many Bernstein components: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.CompactOpenInertialFinitenessStatement`, namespace `Langlands.CuspidalSupport`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.6, Theorem and its proof, printed pp.213–214 / PDF pp.219–220. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

The theorem reads as follows. Let `(π, V) ∈ M(G)`, with Bernstein decomposition `V = ⊕_{𝔰 ∈ B(G)} V_𝔰`, and let `K` be a compact open subgroup of `G`. Then `V_𝔰^K = 0` except for finitely many components `V_𝔰`. More precisely, let `Irr(G)_K` be the set of classes of irreducible smooth representations with nonzero `K`-fixed vectors, and `Ω(G)_K` the set of their cuspidal supports. Then `Ω(G)_K` is a finite set of connected components of `Ω(G)`, and their inertial supports are written `B(G)_K`.

The proof shows two things. A cuspidal support `θ = (M, ρψ)_G` lies in `Ω(G)_K` if and only if `i_P^G(ρψ)^K ≠ 0`, the fibre `Sc⁻¹(θ)` being the set of composition factors of `i_P^G(ρψ)`. This condition does not depend on `ψ ∈ X(M)`, so `Ω(G)_K` is a union of components. And `B(G)_K` is finite, by reduction to the finiteness of supercuspidal inertial classes with `K'`-fixed vectors (Remark VI.3.4).

## The Lean statement

`CompactOpenInertialFinitenessStatement` states the "more precisely" part, in the published framework of actual standard cuspidal data (modules `BernsteinData` and `BernsteinBlock`, Worker 1153). It is a statement unit: nothing is proved.

It quantifies over a nonarchimedean local field `F : Type uF`, a group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, `T`, `i : T.toGrp ⟶ G` and `ν : cocharacterLattice T`. `G(F)` carries the canonical topology `pointTopology` and is assumed locally compact and nonarchimedean. The statement also takes `family : BernsteinStandardFamily i ν`, the published structural hypotheses: `G` connected reductive, `i` a maximal split torus, `ν` generic, finitely many simple roots, and the semidirect decompositions and closedness of the standard subgroups. Finally it takes `K : OpenSubgroup (rationalPoints G)` with `IsCompact (K : Set _)`.

Write `HasFixed π` for "`π` has a nonzero `K`-fixed vector": `∃ x : π, x ≠ 0 ∧ ∀ k ∈ K, π.representation k x = x`. Representations, cuspidal data and inertial classes are taken at the carrier universe `max uF uV`, the universe of the published normalized inductions, as in the published targets of `BernsteinSupportComparison`. The conclusion is the conjunction of:

1. **Finiteness of `B(G)_K`.** The set of `s : BernsteinInertialClass i ν family` such that some `π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)` satisfies `IsBernsteinInertialSupport i ν family s π` and `HasFixed π` is `Set.Finite`.
2. **`Ω(G)_K` is a union of inertial classes.** For cuspidal data `a` and `b` with `IsBernsteinInertiaRelated i ν family a b`: if some `π` with `IsBernsteinCuspidalSupport i ν family a π` has `HasFixed π`, then some `π'` with `IsBernsteinCuspidalSupport i ν family b π'` has `HasFixed π'`.

The published relations have the following meaning. `IsBernsteinCuspidalSupport a π` says that `π` is irreducible and an actual subquotient of the normalized induction `bernsteinInduction a` of the datum `a`. This is exactly Renard's description, in the proof, of the fibre `Sc⁻¹(θ)` as the composition factors of `i_P^G(ρψ)`. `IsBernsteinInertialSupport s π` says that some datum in the class `s` supports `π`. `IsBernsteinInertiaRelated a b` is conjugacy of the standard Levis by an actual element together with a full unramified twist. Thus part 1 is the finiteness of `B(G)_K`, and part 2 says that `Ω(G)_K` contains, with one cuspidal support, its whole inertial class, i.e. its connected component.

## Not stated

- The first sentence of the theorem, about the Bernstein decomposition `V = ⊕ V_𝔰` of an arbitrary smooth `V`, needs the decomposition theorem VI.7.2, which is not available as a published construction. In the presence of the decomposition, it follows from part 1. Every irreducible subquotient of `V_𝔰` has inertial support `𝔰`. A nonzero `K`-fixed vector `v` of `V_𝔰` generates a finitely generated subrepresentation, which has an irreducible quotient, and the image of `v` there is a nonzero `K`-fixed vector.
- The VI.10.6 Proposition (the category `M(G)_K` and the Hecke algebra `H(G, K)`) is a separate unit.
- The proof, including the identification `i_P^G(ρψ)^K ≅ ⊕_{P \ G / K} W^{p(K_g)}` of Lemma III.2.2, is not formalized.
