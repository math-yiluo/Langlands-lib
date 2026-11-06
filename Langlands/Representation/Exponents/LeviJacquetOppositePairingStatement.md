# The pairing between opposite Jacquet modules

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviJacquetOppositePairingStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviJacquetOppositePairingStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.6, the Proposition stated after the proof that the two Theorems of VI.9.6 are equivalent, printed p.202 / PDF p.208, with its proof on printed pp.202–205 / PDF pp.208–211. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, for a parabolic `P = MN` with split component `A`, the opposite parabolic `P̄ = M N̄` and a smooth representation `(π, V)` of `G`:

> There is an `M`-equivariant duality `⟨·,·⟩_P : r_P^G(V) × r_{P̄}^G(Ṽ) → ℂ` such that, for every `v ∈ V`, every `λ ∈ Ṽ`, every `t ∈ C_A^{++}` and every sufficiently large `m ∈ ℕ`,
>
> `⟨r_P^G(π)(t^m)·v̄, λ̄⟩_P = δ_P^{1/2}(t^m) λ(π(t^m)·v)`, (VI.9.6.4)
>
> where `v̄ = j_N(v)` and `λ̄ = j_{N̄}(λ)`. This duality induces an isomorphism `r_{P̄}^G(Ṽ) ≃ r_P^G(V)~`. For every `v ∈ V` and every `λ ∈ Ṽ` there is `ε > 0` such that for every `t ∈ C_A^+(ε)`,
>
> `⟨r_P^G(π)(t)·v̄, λ̄⟩_P = δ_P^{1/2}(t) λ(π(t)·v)`. (VI.9.6.5)

The source introduces this Proposition as a reformulation of the second Theorem of VI.9.6, `r_{P̄}^G π̃ = (r_P^G π)~`, which is the published `LeviJacquetContragredientStatement`. The cones come from V.3.21–V.3.23 (printed pp.116–117 / PDF pp.122–123): `C_A` is the lift of `X_*(A)` to `A` from V.2.5 (printed p.107 / PDF p.113), `C_A^{++} = C_A ∩ M^{++}`, that is, the `a ∈ C_A` with `|α(a)|_F < 1` for every `α ∈ Δ(P)`, and `C_A^+(ε) = C_A ∩ A^+(ε)` with `A^+(ε) = {a ∈ A_M : |α(a)|_F < ε for every α ∈ Δ(P)}` (V.3.22.1). The normalization `δ_P^{1/2}` is the one of `r_P^G` in (VI.1.2.2) (printed p.135 / PDF p.141), `r_P^G(π, V) = (π_N ⊗ δ_P^{1/2}, V_N)`. The last lines of the source proof use exactly this: `δ_P^{1/2}(t^m) π_N(t^m)·v̄ = r_P^G(π)(t^m)·v̄`.

This is a **derived** formulation (see "Provenance").

## Statement

The ambient data are those of `LeviJacquetContragredientStatement`. The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It quantifies over two actual rational parabolic triples with the same Levi group scheme `M`:

- `P = MN`: `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `hp`, `hm`, `hn`, `hmul`;
- `P̄ = M N̄`: `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with `hpbar`, `hmbar`, `hnbar`, `hmulbar`.

It assumes `mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`, that is, the same Levi embedding and `P(F) ∩ P̄(F) = M(F)`. The Markdown of `LeviSecondAdjointnessStatement` explains why these hypotheses characterize the opposite parabolic. On `rationalPoints M` it installs `hm.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology m hm`, and the derived instances `leviPoints_locallyCompactSpace p m hp hm` and `leviPoints_nonarchimedeanGroup p m hp hm`.

For every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, with arbitrary carrier universe `v`, it asserts that there is an isomorphism

`E : (leviJacquetFunctor pbar mbar nbar …).obj π.contragredient ≅ ((leviJacquetFunctor p m n …).obj π).contragredient`

in `SmoothRep ℂ (rationalPoints M)`, that is, `r_{P̄}^G(π̃) ≅ (r_P^G π)~`, with the following property. For every commutative group scheme `A`, every `a : A.toGrp ⟶ M` and every `pres : ParabolicRootPresentation p m a`, the following two clauses hold, with this notation:

- `Δ` is the set of characters `pres.data.f ≫ α` of `A`, for `α` in `simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J`. These are the restrictions to `A` of the simple relative roots outside `J`, that is, Renard's `Δ(P)`. Its image in the real character space is the published `pres.restrictedRoots`. The published standard-parabolic contraction statements use the same restriction, written through rational characters as `standardParabolicComponentCharacters`; the two encodings are not identified in Lean here.
- `rP` is `(leviJacquetFunctor p m n …).obj π`, Renard's `r_P^G(π)`.
- `pairing x y` is `smoothDualPairing rP.representation (E.hom y) x`, that is, `E(y)(x)` for `x ∈ r_P^G(V)` and `y ∈ r_{P̄}^G(Ṽ)`. This is Renard's `⟨x, y⟩_P`.
- `jN x` is `Jacquet.Localization.mk π.representation (pointImage (n ≫ p)) 1 x`, the class of `x` in the actual `N(F)`-coinvariants, which carry `r_P^G(π)`. This is Renard's `j_N`. Likewise `jNbar ℓ` is the class of `ℓ ∈ Ṽ` in the `N̄(F)`-coinvariants of the contragredient, Renard's `j_{N̄}`.
- `δ x` is the value at `leviPointsEquiv p m hp hm x` of `HaarModulus.closedInverseHalfCharacter` for the radical image `pointImage (n ≫ p)` and the Levi image `pointImage (m ≫ p)`. This is the character by which `leviJacquetFunctor` twists the coinvariants, so `rP(x)(jN v) = δ(x) · jN(π(x) v)`. It is Renard's `δ_P^{1/2}` of (VI.1.2.2). The published `ArbitraryParabolicCasselmanStatement` Markdown checks that Renard's `δ_P` is the inverse of the usual modulus `|det Ad(m)|_{Lie N}|_F`, so this character is the inverse square root of the usual modulus.
- `incM t` is `rationalPoints.map a t ∈ M(F)` and `incG t` is its image in `G(F)` through `leviPointsEquiv`.

The two clauses are:

- (VI.9.6.4) for all `x : π`, `ℓ : π.contragredient` and `t ∈ CocharacterUniformizer.CAstrict k A Δ`, there is `j₀ : ℕ` such that for all `j ≥ j₀`,
  `pairing (rP(incM (t ^ j)) (jN x)) (jNbar ℓ) = δ(incM (t ^ j)) * ℓ(π(incG (t ^ j)) x)`;
- (VI.9.6.5) for all `x : π` and `ℓ : π.contragredient` there is a real `ε > 0` such that for all `t ∈ CocharacterUniformizer.CAepsilon k A Δ ε`,
  `pairing (rP(incM t) (jN x)) (jNbar ℓ) = δ(incM t) * ℓ(π(incG t) x)`.

Here `ℓ(·)` is `smoothDualPairing π.representation ℓ`.

## The cones

`CocharacterUniformizer.CA k A` is the image of the published homomorphism `c ↦ c(ϖ)` from `X_*(A)` to `A(F)`, for the fixed uniformizer `ϖ` of the Library. This is Renard's lift `C_A` of `X_*(A)` (V.2.5, V.3.23). `CAstrict k A Δ` is the set of `a ∈ C_A` with `characterNorm k A α a < 1` for every `α ∈ Δ`, and `CAepsilon k A Δ ε` is the set of `a ∈ C_A` with `characterNorm k A α a < ε` for every `α ∈ Δ`. `characterNorm k A α a` is the published normalized norm `|α(a)|_F` of the rational character attached to `α`. These are Renard's `C_A^{++}` (V.3.21) and `C_A^+(ε)` (V.3.22–V.3.23), relative to `P`. As in the source, `C_A^+(ε)` carries no additional condition `|α(a)|_F ≤ 1`.

`ParabolicRootPresentation p m a` is the published verified presentation of `P`, its Levi and the split component: it requires `IsSplitComponent a`, so `A` is the split component `A_M` of the Levi, together with a maximal split torus containing it, a generic cocharacter and a set `J` of simple relative roots such that `P` and `M` are the standard parabolic and Levi attached to `J`. So `Δ` is the set `Δ(P)` of V.3.21.

## Faithfulness notes

- **Pairing and isomorphism.** The source asserts an `M`-equivariant duality that induces an isomorphism `r_{P̄}^G(Ṽ) ≃ r_P^G(V)~`. The statement asserts the isomorphism `E` and defines the pairing as `⟨x, y⟩_P = E(y)(x)`. Then `y ↦ ⟨·, y⟩_P` is the isomorphism `E`, so the pairing induces it, and it is nondegenerate. `M`-equivariance is automatic. `E` is a morphism of representations of `M(F)` and the contragredient action is the inverse transpose, so `⟨rP(m) x, r_{P̄}^G(π̃)(m) y⟩_P = ⟨x, y⟩_P`. Conversely, a pairing with the source's properties gives such an `E`, so nothing is lost.
- **One pairing for every presentation.** `E` is chosen before the split component and the presentation, so one pairing satisfies (VI.9.6.4) and (VI.9.6.5) for every compatible presentation. In the source `A` is the split component of `M` and `Δ(P)` is determined by `P`, and the pairing is defined independently of these choices.
- **Presentations are not asserted to exist.** The clauses are tested for every `pres : ParabolicRootPresentation p m a`, and none is required to exist. For a parabolic without a compatible presentation, the statement asserts only the existence of `E`. The published Casselman statement handles presentations the same way. The existence of presentations for actual parabolics is a structural question not addressed here.
- **Quantifier order.** In (VI.9.6.4) the threshold `j₀` depends on `x`, `ℓ` and `t`, as in the source ("pour tout `m ∈ ℕ` assez grand", after `v`, `λ` and `t`). In (VI.9.6.5) `ε` depends on `x` and `ℓ` only, and the identity holds for all `t ∈ C_A^+(ε)`.
- **Naturality.** The Proposition does not assert that `E` is natural in `π`. Naturality is part of the published `LeviJacquetContragredientStatement`, which asserts a natural isomorphism with no formula. Neither statement is asserted to imply the other.
- **No admissibility.** As in the source, `π` is an arbitrary smooth representation.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `M(F)` are derived from them.

## Remaining obligations

The proof is a separate obligation. The source constructs the pairing level by level. For an open compact subgroup `K` with an Iwahori decomposition with respect to `P`, the proof of the Jacquet lemma gives `V^K = V^K_0 ⊕ V^K_*` with `V^K_* ≅ V_N^{K_M}` (VI.9.1, using a contracting element `t ∈ C_A^{++}` and the operators `a_{t^m,K}`). The same holds for `Ṽ` and `N̄`. The source checks that `V^K_*` is orthogonal to `Ṽ^K_0` and `V^K_0` is orthogonal to `Ṽ^K_*`, defines the pairing on `V_N^{K_M} × Ṽ_{N̄}^{K_M}` through the sections `s^K_P`, `s^K_{P̄}`, and proves independence of `K` by (VI.9.6.6)–(VI.9.6.7). `M`-equivariance uses that the normalizations `δ_P^{1/2}` and `δ_{P̄}^{1/2}` compensate (V.5.4). (VI.9.6.4) follows from (VI.9.1.1). (VI.9.6.5) follows in the same way from Remark 3 of VI.9.1: for `t ∈ C_A^+(ε)`, `V^K = ker a_{t,K} ⊕ Im a_{t,K}`. A proof needs the generalized Jacquet lemma VI.9.1 for actual rational parabolics, Iwahori decompositions with respect to `P` and `P̄`, and the contracting elements of `C_A`. None of this is asserted here.

## Provenance

This is a derived statement of the Proposition of VI.9.6 for the represented-parabolic interface. The functors are the published `leviJacquetFunctor` and `SmoothRep.contragredient`. The opposite parabolic is given, as in `LeviJacquetContragredientStatement`, by an actual rational parabolic triple with the same Levi whose rational points meet those of `P` exactly in the Levi image. The duality is encoded by the isomorphism it induces. `Δ(P)` comes from a published `ParabolicRootPresentation`, and every compatible presentation is tested. The cones are the published `CocharacterUniformizer.CAstrict` and `CocharacterUniformizer.CAepsilon`. `δ_P^{1/2}` is the character `HaarModulus.closedInverseHalfCharacter` that normalizes the published Jacquet functor.
