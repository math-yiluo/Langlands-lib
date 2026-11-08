# The length of an induced supercuspidal representation: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.SupercuspidalInductionLengthStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.3, Corollary, printed p.209 / PDF p.215. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The group `W(D)` is described again in VI.10.4, printed p.210 / PDF p.216, as the stabilizer of `D` in `W(A_M) = N_G(M)/M`.

Renard's corollary reads: the length of `i_P^G(ρ)` is at most `|W(D)|`, where `W(D) = {w ∈ W(M, M) | w · D = D} / W_M`. In particular, if `|W(D)| = 1`, then `i_P^G(ρ)` is irreducible. Here `(M, (ρ, W))` is a cuspidal datum: `M` is a standard Levi subgroup, `P` the standard parabolic with Levi factor `M`, `ρ` an irreducible supercuspidal representation of `M`, and `D = [M, ρ]_M` its inertial class in `M`, the set of unramified twists `ρ ⊗ χ`, `χ ∈ X(M)`, up to isomorphism.

`SupercuspidalInductionLengthStatement` states this in a derived form. It is a statement unit: nothing is proved.

## Hypotheses

- `k : Type u` is a nonarchimedean local field (`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`), of any characteristic.
- `G` is a group scheme over `Spec k` with `hG : IsConnectedReductive G`. Its rational points carry the canonical topology `RationalPointFamily.pointTopology` and are assumed locally compact and nonarchimedean, as in the published represented-parabolic statements.
- `P = MN` is an actual rational parabolic: `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l`, `LeviSubgroup.IsGeometricUnipotentRadical r` and `IsIso (subgroupMultiplication l r)`. The parabolic need not be standard. The source takes `P` standard. Parabolics with the same Levi factor give inductions with the same composition factors (VI.5.4, Corollary; published as `LeviSupercuspidalInductionSameLeviStatement`), so the length does not depend on this choice, and the published VI.5.4 statements already work with arbitrary parabolics.
- `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` (topology `leviPointTopology l hl`) is irreducible (`ρ.IsIrreducible`) and supercuspidal in the published sense `IsSupercuspidal ρ`: its normalized Jacquet module along every proper actual rational parabolic of `M` vanishes.

## The set `W`

`W` is the set of double cosets `x ∈ P(F) \ G(F) / P(F)` (Mathlib `DoubleCoset.Quotient` of the point image `pointImage p`) for which there exist

- `w : rationalPoints G` with `DoubleCoset.mk _ _ w = x`,
- an automorphism `φ : M ≅ M` of the group scheme with `φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom`, i.e. `w ι(m) w⁻¹ = ι(φ m)` for the embedding `ι = l ≫ p` (the published `innerIso w` is conjugation `g ↦ w g w⁻¹`), so that `w` normalizes `M` and `φ` is the induced automorphism,
- a topological group isomorphism `e : rationalPoints M ≃ₜ* rationalPoints M` equal to `φ` on rational points, and
- an unramified character `χ` of `M(F)` (the published `Plancherel.unramifiedCharacters` for the norms of all rational characters of `M`, Renard's `X(M)`)

such that the conjugate `SmoothRep.pullback e ρ` (`m ↦ ρ(φ m)`) is isomorphic to the twist `ρ ⊗ χ` (published `SmoothRep.twist` with `Plancherel.unramifiedCharacter_isOpen_ker`).

### Comparison with `W(D)`

`W` has the cardinality of Renard's `W(D)`. The argument is the following; it is not formalized. Renard's `W(D)` is the stabilizer of `D` in `N_G(M)(F) / M(F)`. Since `M(F)` acts trivially on isomorphism classes, the condition only depends on the class `n M(F)`. The map `n M(F) ↦ P(F) n P(F)` from `N_G(M)(F) / M(F)` to `P(F) \ G(F) / P(F)` is injective. After conjugating `P` to a standard parabolic and `n` into the normalizer of a maximal split torus of `M`, using conjugacy of maximal split tori in `M`, this follows from the Bruhat decomposition, as in V.4. `W` is the image of the elements `n` with `ρ ∘ Ad(n) ∈ D`. This is the stabilizer of `D` up to the inversion `n ↦ n⁻¹`, which is a bijection of stabilizers. Renard's convention `(w · ρ)(m) = ρ(w⁻¹ m w)` therefore gives the same count.

## Conclusion

Write `π = (leviInductionFunctor p l r hp hr hl hmul).obj ρ`, the published normalized induction `i_P^G(ρ)`, an object of `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`. The conclusion is the conjunction of:

1. `Module.length (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule ≤ W.encard`. Mathlib's `Module.length` is the length of `π` as a module over the group algebra `ℂ[G(F)]`, valued in `ℕ∞`; submodules are exactly the subrepresentations. This is the published notion behind `SmoothRep.HasFiniteLength`. The bound uses `Set.encard`, so it asserts in particular that `i_P^G(ρ)` has finite length and that `W` is finite.
2. `W.encard ≤ 1 → π.IsIrreducible`, the "in particular" of the corollary. `W` always contains the trivial double coset, with `w = 1`, `φ = 𝟙` and `χ = 1`, so `W.encard ≤ 1` is Renard's `|W(D)| = 1`.

## Remarks

- Renard deduces the corollary from the VI.10.3 Proposition (the functor `r_D : M(G)_𝔰 → M(M)_D` kills no nonzero object) and from the geometric lemma, which bounds the length of `r_D i_P^G(ρ)` by `|W(D)|`. Neither is formalized here.
- The published VI.5.4 statement `LeviSupercuspidalInductionAssociationStatement` leaves the VI.5.4 length bound `l(M)` unstated. The set `W` above is an actual-group formulation of a Weyl-group count that could serve such statements.
