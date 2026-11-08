# The Langlands classification: statement

Author: Worker 6. Module `Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.4.2, Theorem, printed p.243 / PDF p.249 (proof to printed p.246 / PDF p.252). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Langlands triplets are those of VII.4.1, Definition, printed p.241 / PDF p.247, formalized as `IsLanglandsTriplet` in the module `LanglandsTriplet`.

Renard's theorem has three parts:

- (i) if `(P = MN, (σ, E), ψ)` is a Langlands triplet, `i_P^G(σ ⊗ ψ, E)` has a unique irreducible quotient, written `J(P, σ, ψ)`;
- (ii) if `J(P₁, σ₁, ψ₁) = J(P₂, σ₂, ψ₂)`, then `M₁ = M₂`, `ℜ(ψ₂ ψ₁⁻¹) = 0` and `σ₁ψ₁ ≃ σ₂ψ₂`;
- (iii) every `(π, V) ∈ Irr(G)` is isomorphic to `J(P, σ, ψ)` for some Langlands triplet.

The module states these as three propositions and their conjunction `LanglandsClassificationStatement.{u', v'}`. It is a statement unit: nothing is proved.

## Common setting

Each proposition quantifies over:

- a nonarchimedean local field `k : Type u` (`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`), with no restriction on the characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`; its rational points carry the canonical topology `RationalPointFamily.pointTopology` and are assumed locally compact and nonarchimedean, as in the published representation-theoretic statements;
- a commutative group scheme `T`, a map `i : T.toGrp ⟶ G` with `[Mono i.hom.hom.left]`, a cocharacter `ν : cocharacterLattice T`, and reflection data `D : RelativeRootReflectionData i`. These fix the minimal parabolic `P_∅` and the coroots, as in `IsLanglandsTriplet`.

A triplet is given by group schemes `P, M, U` and a commutative group scheme `A`, maps `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`, `a : A.toGrp ⟶ M` with `hp : IsParabolicSubgroup p`, `hl : IsRationalLeviSubgroup l`, `hr : LeviSubgroup.IsGeometricUnipotentRadical r`, `hmul : IsIso (subgroupMultiplication l r)` and `ha : IsSplitComponent a`, a simple-root index `J : Set (characterLattice T)`, a factor `f : A ⟶ T`, a smooth representation `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` (Levi topology `leviPointTopology l hl`) and `ψ : leviUnramifiedCharacters l hl`. The triplet condition is `IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ`. The radical `r` is needed only to form the induced representation.

The twist `σ ⊗ ψ` is the published `σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)` on the carrier of `σ`, using the instance `leviPoints_nonarchimedeanGroup p l hp hl`; this is the same expression as in the published `RenardGenericIrreducibilityStatements`. The induced representation `i_P^G(σ ⊗ ψ)` is `(leviInductionFunctor p l r hp hr hl hmul).obj` of the twist, an object of `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`: Renard's normalized parabolic induction, transported along the published identification of `M(F)` with its image in `P(F)`.

## (i) `LanglandsQuotientUniqueStatement`

For every triplet as above, there is `π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with

`Classification.IsIrreducibleHead (i_P^G(σ ⊗ ψ)).representation π.representation`.

The published `IsIrreducibleHead ρ π` says that `π` is irreducible, there is a surjective intertwining map `q : ρ → π`, and every surjective intertwining map from `ρ` onto an irreducible representation on a carrier in the same universe has the same kernel as `q`. This is "`i_P^G(σ ⊗ ψ)` has a unique irreducible quotient", uniqueness being as a quotient object, which is stronger than uniqueness up to isomorphism. The common carrier universe is `max u v`, the universe of the induced representation. Quotients of smooth representations are smooth, so using `Representation.IsIrreducible` on the underlying representations loses nothing.

## (ii) `LanglandsQuotientInjectiveStatement`

It takes two triplets `(P₁, M₁, U₁, A₁, p₁, l₁, r₁, a₁, …, J₁, f₁, σ₁, ψ₁)` and `(P₂, …, J₂, f₂, σ₂, ψ₂)` for the same `(T, i, ν, D)`, and any `π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` that is an irreducible quotient of both induced representations (`Classification.IsIrreducibleQuotient`: `π` irreducible with a surjective intertwining map). Write `τⱼ` for the twist `σⱼ ⊗ ψⱼ`. The conclusion is the conjunction of:

1. `J₁ = J₂`. Both presentations share `T`, `i` and `ν`, so this says that `P₁` and `P₂` are the same standard parabolic and `M₁` and `M₂` the same standard Levi. It is Renard's `M₁ = M₂`.
2. For all `m₁ : rationalPoints M₁` and `m₂ : rationalPoints M₂` with the same image in `G(F)` (`rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂`), `‖ψ₁ m₁‖ = ‖ψ₂ m₂‖`. This is Renard's `ℜ(ψ₂ ψ₁⁻¹) = 0`. By V.3.20 (printed p.116 / PDF p.122), an unramified character has real part `0` exactly when it is unitary, and `ψ₂ψ₁⁻¹` is unitary exactly when `|ψ₁| = |ψ₂|`.
3. There is a linear equivalence `φ : τ₁ ≃ₗ[ℂ] τ₂` with `φ (τ₁ m₁ x) = τ₂ m₂ (φ x)` whenever `m₁` and `m₂` have the same image in `G(F)`. This is Renard's `σ₁ψ₁ ≃ σ₂ψ₂`.

Renard's conditions compare objects of the single group `M₁ = M₂`. Here `M₁` and `M₂` are separate group schemes with their own embeddings in `G`, so conditions 2 and 3 compare them through pairs of points with equal images. When `J₁ = J₂`, the two standard Levi subgroups have the same image, and since both point maps `M_j(F) → G(F)` are injective, each `m₁` has exactly one partner `m₂`. Conditions 2 and 3 then say exactly that `|ψ₁| = |ψ₂|` and `σ₁ψ₁ ≅ σ₂ψ₂` after identifying `M₁(F)` with `M₂(F)` inside `G(F)`. This identification is a reading of the statement and is not formalized.

Renard's hypothesis is equality of the two Langlands quotients. The formal hypothesis is that one irreducible `π` is a quotient of both induced representations. Given part (i), these agree: if `π` is an irreducible quotient of `i_{Pⱼ}^G(σⱼ ⊗ ψⱼ)`, then `π ≅ J(Pⱼ, σⱼ, ψⱼ)`.

## (iii) `LanglandsQuotientExhaustiveStatement`

It assumes `IsMaximalSplitTorus i`, `IsGenericCocharacter i ν` and `IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))`. This is Renard's standing choice of a maximal split torus `A_∅` and a minimal parabolic `P_∅ ⊇ A_∅`. Without such hypotheses no presentation could be compatible, and the existence claim would fail. For every irreducible `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` (`π.IsIrreducible`), it asserts the existence of group schemes `P, M, U, A`, maps and witnesses as in the common setting, `J`, `f`, `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` and `ψ` such that `IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ` holds and there is a surjective intertwining map from `i_P^G(σ ⊗ ψ)` onto `π`. With part (i), `π ≅ J(P, σ, ψ)`.

Renard's `Irr(G)` consists of irreducible smooth representations. Admissibility is not assumed; it is a consequence that the proof may use. The carrier of `σ` is required to lie in the universe `v` of `π`. This is a valid choice: in Renard's proof, `σ ⊗ ψ` embeds in a Jacquet module of `π`, a quotient of `V`, so it has an isomorphic copy on a carrier in `Type v`.

## Conventions and departures

- Temperedness and the chamber condition use the published normalized parameter (`q^(-s)` lift; see the `LanglandsTriplet` and `ArbitraryParabolicTempered` Markdown). With this parameter, for `GL_2` with upper triangular Borel `B`, `ℜ(δ_B^{1/2})` is half the positive root, in the open chamber, and the trivial representation is the unique irreducible quotient of `i_B^G(δ_B^{1/2})`, as part (i) predicts. Under the opposite (raw-logarithm) sign the statements would be false.
- Standard parabolics are given by compatible root presentations with respect to the fixed `(T, i, ν)`. Renard fixes `P_∅` and `A_∅` once and for all, so this matches his use of standard parabolics.
- Renard's remark after the proof of (i), that `J(P, σ, ψ)` is characterized among the irreducible subquotients of `i_P^G(σ ⊗ ψ)` by `ℜ(ψ) ∈ ℜ(Exp(A_M, r_{P̄}^G(π)))`, is not part of the theorem and is not stated.
- The proof (VII.4.1 Lemma, second adjointness, the geometric lemma and Langlands's combinatorial lemma V.3.18) is not formalized here.
