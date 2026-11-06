# Inputs for the unitary case of Renard VII.1.3

Author: Worker 1507. Module `Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module has eight `Prop`-valued definitions and nothing else. None of them is assumed or proved here. They are the results of Chapters III, IV and VI that the proof of Renard VII.1.3 uses once the induced representation has a unitary central character, i.e. for the published `MaximalLeviSupercuspidalReducibilityUnitaryStatement` (module `MaximalLeviReducibilityReductionStatements`). Each one is stated for the represented-parabolic interface of the published target `MaximalLeviSupercuspidalReducibilityStatement`. A later proof module will derive the unitary statement from them (see "How the statements are used" below).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source ID `renard-2026-representations-groupes-reductifs-padiques`. The proof of VII.1.3 (printed pp.224–226 / PDF pp.230–232) cites VI.5.3, VI.5.4, VI.3.6, VI.7.2, VI.8.5, VI.9.6.2, Casselman's criterion VII.1.2 and the facts that square-integrable representations are unitary and that inductions of unitary representations are unitary and semisimple. The locators for each statement are given below.

## Common setup

Every statement starts with the binder block of the published target: a nonarchimedean local field `k` (`Field`, `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`, `T2Space`), a connected reductive group scheme `G` over `Spec k` whose rational points `rationalPoints G` carry the canonical topology `RationalPointFamily.pointTopology` and are assumed locally compact and a nonarchimedean group, and actual rational parabolic data `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P` with `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l`, `LeviSubgroup.IsGeometricUnipotentRadical r` and `IsIso (subgroupMultiplication l r)`. The Levi points `rationalPoints M` carry `leviPointTopology l hl`, the canonical point topology of `M`.

- "Normalized induction" is the published `leviInductionFunctor p l r hp hr hl hmul`, from `SmoothRep.{0, u, v} ℂ (rationalPoints M)` to `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`.
- "Supercuspidal" is the Jacquet-vanishing premise of the target, verbatim: for every actual parabolic `p' : P' ⟶ M` (resp. `⟶ H`) with rational Levi and matching radical, if `p'` is not an isomorphism then the normalized Jacquet module `(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ` is a subsingleton.
- "Maximal proper" (statements K1, K2, C) is the target's pair of premises `¬ IsIso p` and: every parabolic `q : Q ⟶ G` through which `p` factors as `j ≫ q` has `j` or `q` an isomorphism.
- `IsUnitarizable π.representation` is the published existence of an invariant positive definite Hermitian form (`Unitary/Basic`). `UnitaryCentralCharacter` is the published structure of `MatrixCoefficient/ModuloCenter`: a character of `Subgroup.center` with open kernel and values of norm `1`, by which the center acts. `SmoothRep.twist χ hχ` twists by an open-kernel character `χ` on the same carrier.
- A "nonzero morphism" `f` is one with `∃ x, SmoothRep.hom f x ≠ 0`. A subrepresentation is given by an injective morphism, and a quotient by a surjective one.

## The statements

### I1. `SupercuspidalUnitaryCentralCharacterUnitarizableStatement`

For a connected reductive `H` (with locally compact nonarchimedean points in the canonical topology), every irreducible supercuspidal `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H)` with a `UnitaryCentralCharacter` is unitarizable.

Source: VI.2.1, Théorème (PDF pp.143–144: a smooth representation is supercuspidal if and only if its coefficients are compactly supported modulo the center `Z(G)`), VI.2.2 (PDF p.146: an irreducible supercuspidal representation is admissible) and IV.3.2, Lemme (PDF p.106: an admissible representation that is square-integrable modulo the center, with its unitary central character, is unitary). With a unitary central character, compactly supported coefficients modulo the center are square-integrable modulo the center. VII.1.3 uses this in the first case of the trichotomy: "le caractère central de `ρ` est unitaire, et comme `ρ` est supercuspidale, `ρ` est alors unitaire" (PDF p.231). It is stated for a general group `H` because the proof applies it to the Levi `M` (`H = M`, `hH = hl.isConnectedReductive`; then `leviPointTopology l hl` is by definition the topology installed here).

### IA. `LeviInductionAdmissibleStatement`

Normalized induction sends admissible representations of `M(F)` to admissible representations of `G(F)`. No properness or maximality is assumed.

Source: III.2.3, Lemme (PDF p.78: if `H\G` is compact, induction from `H` preserves admissibility), applied to the normalized induction `i_P^G(τ) = Ind_P^G(τ ⊗ δ_P^{-1/2})` of VI.1.2 (PDF p.141); `G/P` is compact (VI.1.1, Remarque). The proof of VI.2.2 (PDF p.146) applies it in exactly this form: "D'après le lemme III.2.3, `i_P^G(τ,E)` est admissible".

### IU. `LeviInductionUnitarizableStatement`

Normalized induction sends unitarizable representations of `M(F)` to unitarizable representations of `G(F)`.

Source: IV.2.3 (PDF p.104: for `H\G` compact, the normalized induction of a unitary representation is unitary), with VI.1.2. VII.1.3 uses it in the first case: "`π = i_P^G(ρ)` est encore unitaire, donc complètement réductible".

### N. `LeviInductionNontrivialStatement`

Normalized induction sends nonzero representations of `M(F)` to nonzero representations of `G(F)` (`Nontrivial` of the carriers).

Source: this is the standard fact that a nonzero `σ` has nonzero induction: for `v ≠ 0` and a small compact open `K`, the function supported on `P(F)K` with `f(pk) = δ_P^{-1/2}(p) σ(p) v` is well defined once the image of `P(F) ∩ K` in `M(F)` fixes `v`, and is a nonzero smooth vector of `i_P^G σ` (Renard III.2.2, PDF p.77, and VI.1.2.1, PDF p.141, for the functions defining the induction). The source uses it implicitly when it treats `i_P^G ρ` as a representation having composition factors. It is recorded separately because `admissibleUnitarySemisimplicity` and the decomposition argument need a nonzero `π`.

### Hd. `LeviInductionHermitianDualityStatement`

Let `σ` be an admissible unitarizable representation of `M(F)` and `χ, χ' : rationalPoints M →* ℂˣ` characters with open kernels such that `χ'(m) · conj(χ(m)) = 1` for all `m`. Let `W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` be nonzero, admissible and unitarizable. Then:

1. if there is an injective morphism `W ⟶ i_P^G(σ ⊗ χ)`, there is a nonzero morphism `i_P^G(σ ⊗ χ') ⟶ W`;
2. if there is a surjective morphism `i_P^G(σ ⊗ χ) ⟶ W`, there is a nonzero morphism `W ⟶ i_P^G(σ ⊗ χ')`.

Source: (IV.2.1.2) (PDF p.103: the hermitian dual of a normalized induction from a cocompact subgroup is the induction of the hermitian dual, `(i_H^G τ)^h = i_H^G(τ^h)`) and IV.2.1, Remarque 1 (PDF p.103: an admissible representation with a nondegenerate invariant hermitian form is isomorphic to its hermitian dual). With these, `(σ ⊗ χ)^h ≃ σ^h ⊗ conj(χ)^{-1} ≃ σ ⊗ χ'`. Dualizing `W ↪ i_P^G(σ ⊗ χ)` gives a surjection `i_P^G(σ ⊗ χ') ≃ (i_P^G(σ ⊗ χ))^h ↠ W^h ≃ W`, which is nonzero because `W` is. Dualizing a surjection `i_P^G(σ ⊗ χ) ↠ W` gives an injection `W ≃ W^h ↪ i_P^G(σ ⊗ χ')`. VII.1.3 uses this as `π_1^h = π_1` for the unitary constituent `π_1` and `π^h = i_P^G(ρ^h)` (PDF pp.231–232).

Derived form: the statement records only these two consequences, not the hermitian dual functor itself, which the represented interface does not provide. The condition on `χ, χ'` is how the proof expresses `ρ^h` for `ρ = σ ⊗ χ` with `σ` unitary: for a positive real `χ`, `χ' = χ^{-1}`.

### K1. `MaximalLeviSupercuspidalInductionEndomorphismStatement`

For a maximal proper `P` and an irreducible supercuspidal `ρ` of `M(F)`, every endomorphism `f` of `i_P^G ρ` is a scalar (`∃ c, ∀ x, f x = c • x`), unless there are `g : rationalPoints G` and `φ : M ≅ M` with `φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom` and `g ∉ pointImage (l ≫ p)`, and a linear bijection `T : ρ ≃ₗ[ℂ] ρ` with `T (ρ m x) = ρ (φ(F) m) (T x)`, i.e. `ρ ≃ ρ ∘ φ(F)`.

The normalizing data `g, φ` are those of the target's conclusion; `φ(F) = rationalPoints.map φ.hom`.

Source: III.2.5 (PDF p.79, Frobenius reciprocity) with VI.1.2 (PDF p.141: `r_P^G` is left adjoint to `i_P^G`), giving `End_G(i_P^G ρ) ≃ Hom_M(r_P^G i_P^G ρ, ρ)`, and VI.5.3 (PDF p.179, consequences of the geometric lemma: for supercuspidal `ρ`, the composition factors of `r_P^G i_P^G ρ` are `ρ` and, when the nontrivial `w ∈ W(M, *)` normalizes `M`, `ρ^w`). If no `w` normalizing `M` has `ρ^w ≃ ρ`, Schur's lemma bounds the dimension of this Hom space by `1`. This is the computation (VII.1.3.1) on PDF p.231, applied with `P' = P`.

### K2. `MaximalLeviSupercuspidalInductionHomStatement`

For a maximal proper `P` and irreducible supercuspidal `τ, τ'` of `M(F)`, a nonzero morphism `f : i_P^G τ' ⟶ i_P^G τ` forces `Nonempty (τ' ≅ τ)`, or the existence of `g, φ` as in K1 and a linear bijection `T : τ ≃ₗ[ℂ] τ'` with `T (τ m x) = τ' (φ(F) m) (T x)`, i.e. `τ ≃ τ' ∘ φ(F)`.

Source: the same adjunction and geometric lemma: `Hom_G(i_P^G τ', i_P^G τ) ≃ Hom_M(r_P^G i_P^G τ', τ)`, whose source has composition factors `τ'` and possibly `τ'^w`; a nonzero morphism to the irreducible `τ` makes `τ` isomorphic to one of them. This is how VII.1.3 identifies `ρ' = ρ^w` with `ρ^h` (PDF p.232: "`ρ' = ρ^w = r_{P̄}^G(π_1) = … = ρ^h`"); the proof module uses it on the composite of the morphisms from Hd and C. Replacing `(g, φ)` by `(g⁻¹, φ⁻¹)` exchanges `τ ≃ τ' ∘ φ(F)` and `τ' ≃ τ ∘ φ(F)`, so the direction of `T` is no restriction.

### C. `MaximalLeviSupercuspidalUnitarizableConstituentStatement`

For a maximal proper `P` and an irreducible supercuspidal `ρ` of `M(F)` with no unitary central character (`IsEmpty (UnitaryCentralCharacter ρ.representation)`, for the center of `M(F)`), if `i_P^G ρ` is not irreducible and has a `UnitaryCentralCharacter` (for the center of `G(F)`), then there is an irreducible unitarizable `W : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with an injective morphism `W ⟶ i_P^G ρ` or a surjective morphism `i_P^G ρ ⟶ W`.

Source: VII.1.3, proof, PDF pp.230–232, with VII.1.2 (Casselman's criterion, PDF p.227). By VI.5.3 and VI.5.4 (PDF p.179), `π = i_P^G ρ` has length exactly `2`, `0 → π_1 → π → π_2 → 0`. Since `A_M/A_G` has dimension `1` and the central character of `ρ` is not unitary, its absolute value is `> 1` or `< 1` on `A_M^{++}`. In the third case Casselman's criterion (VII.1.2) shows that `π_1` is square-integrable modulo the center, hence unitary (IV.3.2). In the second case the source passes to the contragredient, and the same argument shows that the quotient `π_2` is square-integrable, hence unitary. So `W = π_1` (a subrepresentation) or `W = π_2` (a quotient).

Derived form: the source draws the contradiction (`M ≠ M'`) or the identification `ρ' = ρ^h` (`M = M'`) from this constituent. The statement records only the existence of the unitary constituent, which holds in both cases. It does not assert admissibility of `W`, which follows from irreducibility by the published `Langlands.Aubert.General.RationalPointsIrreducibleAdmissibleStatement` (Renard VI.2.2).

## How the statements are used

The planned proof of `MaximalLeviSupercuspidalReducibilityUnitaryStatement` (not part of this module) has two cases.

- If `ρ` has a unitary central character: I1 makes `ρ` unitarizable, `RationalPointsIrreducibleAdmissibleStatement` makes it admissible, IA and IU make `π = i_P^G ρ` admissible and unitarizable, and N makes `π` nonzero. The published `admissibleUnitarySemisimplicity` (Renard IV.2.2, Corollaire) makes `π` semisimple, so a reducible `π` has a nonscalar endomorphism (a projection onto a proper summand). K1 then gives `g`, `φ` and `ρ ≃ ρ ∘ φ(F)`, which is the target's conclusion with `ψ = 1`.
- If not: an unramified positive twist `ρ_0 = ρ ⊗ ψ` has a unitary central character (VI.8.5, to be supplied by Worker 1517's general twist lemma, which is not stated here). Then `ρ_0` is unitarizable by I1, `ρ ≃ ρ_0 ⊗ ψ^{-1}` and C gives an irreducible unitarizable sub or quotient `W` of `π`. Hd with `σ = ρ_0`, `χ = ψ^{-1}`, `χ' = ψ` gives a nonzero morphism between `i_P^G(ρ ψ^2)` and `π`, and K2 gives `ρ ≃ (ρ ψ^2) ∘ φ(F)` up to inverting `(g, φ)`. The alternative `ρ ψ^2 ≃ ρ` is excluded on the center of `M(F)`: it would make `ψ^2`, hence `ψ`, trivial there, so the central character of `ρ` would be that of `ρ_0`, which is unitary.

## Faithfulness notes

- **Represented interface.** All objects are the published ones of `ArbitraryParabolicLeviPoints` and `ArbitraryParabolic`: actual parabolic and Levi subgroup schemes, their canonical point topologies, the transported normalized induction and Jacquet functors, and `pointImage (l ≫ p)` for "`g` outside the Levi". There are no standard-parabolic or root-datum choices; the source's `w ∈ W(M, *)` normalizing `M` is the pair `(g, φ)` exactly as in the target.
- **Supercuspidality** is the target's Jacquet-vanishing premise in every statement, for parabolics of `M` (or of `H` in I1).
- **Weaker hypotheses.** IA, IU, N and Hd assume neither properness nor maximality. I1 is stated for every connected reductive group.
- **Admissibility.** Hd requires `σ` and `W` admissible, which the source needs for `σ^h ≃ σ` and `W^h ≃ W`. C does not assert admissibility of `W` (see above). K1, K2 and C assume irreducible supercuspidal representations, which are admissible (VI.2.1, VI.2.2).
- **Universes.** As in the target, representations of `M(F)` are in `SmoothRep.{0, u, v}` and their inductions in `SmoothRep.{0, u, max u v}`; the constituent `W` of C and Hd lives in the latter.

## Provenance

All eight statements are derived from the proof of Renard VII.1.3 and the results it cites, as listed per statement above. I1, IA and IU are the cited results for the represented interface. N is a standard elementary fact made explicit. Hd, K1, K2 and C are the specific consequences of IV.2.1.2, III.2.5 with VI.5.3, and Casselman's criterion that the proof of VII.1.3 uses, stated in the form in which the proof applies them rather than as the underlying general theorems (for which the represented interface has no hermitian dual, contragredient of inductions or geometric-lemma filtration yet).
