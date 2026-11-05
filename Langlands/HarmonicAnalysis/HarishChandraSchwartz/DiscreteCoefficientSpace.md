# Coefficients of unitary admissible representations (Waldspurger, Theorem VIII.4.2, inclusion `p_χ(°C(G)) ⊂ A₂(G)_χ`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteCoefficientSpace`,
namespace `Langlands.HarishChandraSchwartz`. It imports and uses:

- `SquareIntegrableSemisimplicity` (Lemma III.1.3): `subrepresentationAsModuleEquiv`; through it
  `CentralSubgroupCoefficients`: `IsSquareIntegrableModCentralSubgroup`,
  `centralSubgroupCoefficientNorm_mk`;
- `Plancherel.CoefficientTensors`: `smoothCoefficientBilinear`, `coefficientTensorMap`;
- `Unitary.CentralCharacterProof`: `unitarizableCentralCharacter`;
  `Unitary.AdmissibleSemisimplicityProof`: `admissibleUnitarySemisimplicity`;
- `Unitary.Basic` and `Unitary.HermitianDual`: `InvariantPositiveForm`,
  `InvariantPositiveForm.comap`, `InvariantPositiveForm.toSmoothDual`,
  `InvariantPositiveForm.smoothDualEquiv`;
- `Smooth.Transfer.SubquotientProof`: `isSmooth_of_injective`;
  `Smooth.Admissibility.EmbeddingProof`: `isAdmissible_of_injective`;
  `Smooth.Contragredient.Definitions`: `contragredientMap`;
  `ScalarSubReduction`: `ScalarSubReduction.inclusion`, `ScalarSubReduction.inclusion_injective`;
- Mathlib: `Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`,
  `Representation.irreducible_iff_isSimpleModule_asModule`, `Representation.asModuleEquiv`,
  `Subrepresentation.ofSubmodule'`, `IsSemisimpleModule.sSup_simples_eq_top`, `sSup_eq_iSup'`,
  `Submodule.iSup_induction`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Printed p. 330 (PDF p. 96): "Pour `χ ∈ Â_G`, notons `E₂(G)_χ` l'ensemble des `ω ∈ E₂(G)` tels
que la restriction `χ_ω` à `A_G` de leur caractère central soit égale à `χ`. Posons
`A₂(G)_χ = ⊕_{ω ∈ E₂(G)_χ} A(ω)`." "Théorème VIII.4.2. Pour tout `χ ∈ Â_G`, on a l'égalité
`p_χ(°C(G)) = A₂(G)_χ`."

This module concerns the second half of the proof (printed pp. 330–331, PDF pp. 96–97), the
inclusion `p_χ(°C(G)) ⊂ A₂(G)_χ`. For a compact open subgroup `H`, `V = p_χ(°C(H \ G))` with
`G` acting by right translations `ρ`. "La représentation `(ρ, V)` est unitaire […] Elle est
admissible […] Elle est donc semi-simple. L'espace des coefficients `A(ρ)` est engendré par les
fonctions `g ↦ (f₁, ρ(g) f₂)_{A_G\G}` pour `f₁, f₂ ∈ V`." Formula (2) gives
`(f₁, ρ(g) f₂)_{A_G\G} = (p_χ(φ̌̄₁ ∗ φ₂))(g)`, "En particulier cette fonction est de carré
intégrable sur `A_G \ G`. Donc toute sous-représentation irréductible de `(ρ, V)` est de carré
intégrable. Comme la restriction à `A_G` du caractère central d'une telle sous-représentation est
évidemment égale à `χ`, on a `A(ρ) ⊂ A₂(G)_χ`." Then, with `e` the characteristic function of
`H`, Remark VIII.2.2 and Lemma VIII.2.3 give `f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A_G\G}`, "Donc
`f ∈ A(ρ)`. Cela démontre l'inclusion `V ⊂ A₂(G)_χ`", and `p_χ(°C(G))` is the union of the
`p_χ(°C(H \ G))`. The computation of (2) starts with
`(f₁, ρ(g) f₂) = ∫_{A_G\G} conj(f₁(g′)) f₂(g′g) dg′` (bar on the first factor, checked on the
page image of p. 331), so the product is conjugate-linear in the first argument, as is
`InvariantPositiveForm.inner` (Mathlib's `InnerProductSpace.Core` convention). Since `mes(H)` is
real, `mes(H)⁻¹ (p_χ °e, ρ(g) f) = (mes(H)⁻¹ p_χ °e, ρ(g) f)`.

## Scope: abstract data and explicit hypotheses

This module proves the representation-theoretic part of the argument for an abstract
representation; it does not construct `°C(H \ G)`, `p_χ`, the product `(·,·)_{A_G\G}` or
`A₂(G)_χ`, and it does not prove formula (2) or the reproducing identity. `G` is a topological
group (`[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`) and `ρ : Representation ℂ G V`
acts on a complex vector space `V` without topology. In the `Unitary` section `A` is a normal
subgroup (`[A.Normal]`) contained in the center (`hA : A ≤ Subgroup.center G`), `G ⧸ A` carries
a measurable structure and a Haar measure `μ` (`[μ.IsHaarMeasure]`). The hypotheses of each
result:

- `subrepresentationSmoothRep`, `subrepresentationCoefficientSpace`: `hs : IsSmooth ρ`.
- `subrepresentationCoefficientSpace_mono`: `hs` and `hpq : ∀ S, p S → q S`.
- `smoothCoefficient_mem_of_mem`: `hs`, a subrepresentation `S` with `hS : p S`, a vector `x`
  with `hx : x ∈ S.toSubmodule`, and `ℓ : SmoothDual ρ`.
- `smoothCoefficient_mem_irreducible`: `hs` and
  `hss : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule`.
- `formCoefficient_apply`: an invariant positive form `b : InvariantPositiveForm ρ` and `hs`.
- `formCoefficient_mem_irreducible`: `hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K`, `b`, and `ha : IsAdmissible ρ`.
- `isSquareIntegrable_of_irreducible_subrepresentation`: `hcof`, `b`, `ha`, a subrepresentation
  `S` with `hi : S.toRepresentation.IsIrreducible`, and
  `hL2 : ∀ e f : V, ∃ F : G ⧸ A → ℝ, MemLp F 2 μ ∧ ∀ g : G, F (QuotientGroup.mk g) =
  ‖b.inner e (ρ g f)‖` (the absolute values of the coefficients `g ↦ b(e, ρ(g) f)` descend to
  square-integrable functions on `G ⧸ A`).
- `formCoefficient_mem_squareIntegrable`: `hcof`, `b`, `ha`, `hL2`, a homomorphism
  `χ : A →* ℂˣ` and `hχ : ∀ (a : A) (x : V), ρ a x = (χ a : ℂ) • x`.
- `exists_mem_squareIntegrable_of_reproducing`: `hcof`, `b`, `ha`, `χ`, `hχ`, `hL2`, a map
  `ev : V → G → ℂ`, and `hrep : ∀ f : V, ∃ e : V, ∀ g : G, ev f g = b.inner e (ρ g f)`.

In Waldspurger's situation `b` is the product of Proposition VIII.4.1, `A = A_G`, `μ` the Haar
measure on `A_G \ G`, `hL2` is the consequence of formula (2) quoted above, `hχ` holds because the
functions in `V` are `χ`-covariant under the central `A_G`, `ev f = f`, and `hrep` is
`f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)` with `e = mes(H)⁻¹ p_χ °e`. Square integrability is the
published predicate `IsSquareIntegrableModCentralSubgroup A hA S.toRepresentation μ`
(admissibility, a unitary character of the full center, and square integrability on `G ⧸ A` of
the absolute values of all smooth matrix coefficients).

## Definitions

- `subrepresentationSmoothRep hs S`: a subrepresentation `S` of a smooth `ρ`, bundled as
  `SmoothRep ℂ G` (smooth because it embeds in `ρ`, `isSmooth_of_injective`).
- `subrepresentationCoefficientSpace hs p`: the submodule
  `⨆ (S : Subrepresentation ρ) (_ : p S), LinearMap.range (coefficientTensorMap
  (subrepresentationSmoothRep hs S))` of `LocallyConstant G ℂ`, the span of the coefficient
  spaces `A(S)` (functions `g ↦ λ(S(g) x)` with `x ∈ S` and `λ` a smooth functional on `S`) of
  the subrepresentations of `ρ` satisfying `p`. With `A = A_G` and `p S` = "irreducible, square
  integrable modulo `A`, and `A` acts on `S` by `χ`", each such `S` represents a class in
  Waldspurger's `E₂(G)_χ` and `A(S)` is its coefficient space, so this span is contained in
  `A₂(G)_χ`; `E₂(G)_χ` and `A₂(G)_χ` themselves are not defined here.

## Results

- `subrepresentationCoefficientSpace_mono`: the span is monotone in the predicate `p`.
- `smoothCoefficient_mem_of_mem`: for `x ∈ S` with `p S` and a smooth functional `ℓ` on `ρ`,
  the coefficient `g ↦ ℓ(ρ(g) x)` lies in `subrepresentationCoefficientSpace hs p`.
- `smoothCoefficient_mem_irreducible` (**coefficients of a semisimple representation**): if the
  `ℂ[G]`-module of the smooth `ρ` is semisimple, every coefficient `g ↦ ℓ(ρ(g) v)` lies in the
  span of the coefficient spaces of the irreducible subrepresentations of `ρ`.
- `formCoefficient_apply`: the coefficient of `f` and the smooth functional `b(e, -)` is
  `g ↦ b(e, ρ(g) f)`.
- `formCoefficient_mem_irreducible` ("Elle est donc semi-simple" and `A(ρ)` is generated by the
  `g ↦ (f₁, ρ(g) f₂)`): for admissible `ρ` with an invariant positive form, every
  `g ↦ b(e, ρ(g) f)` lies in the span of the coefficient spaces of the irreducible
  subrepresentations.
- `isSquareIntegrable_of_irreducible_subrepresentation` ("toute sous-représentation
  irréductible de `(ρ, V)` est de carré intégrable"): under `hL2`, every irreducible
  subrepresentation of `ρ` satisfies `IsSquareIntegrableModCentralSubgroup A hA _ μ`.
- `formCoefficient_mem_squareIntegrable` (**`A(ρ) ⊂ A₂(G)_χ`, abstract form**): under `hL2` and
  `hχ`, every `g ↦ b(e, ρ(g) f)` lies in the span of the coefficient spaces of the irreducible
  subrepresentations `S` of `ρ` that are square integrable modulo `A` and on which `A` acts by
  `χ`.
- `exists_mem_squareIntegrable_of_reproducing` (**`V ⊂ A₂(G)_χ`, abstract form**): under
  moreover `hrep`, for every `f ∈ V` there is `φ` in that span with `⇑φ = ev f`.

## Proof notes

1. `smoothCoefficient_mem_of_mem`: the coefficient is the image under `coefficientTensorMap` of
   `⟨x, hx⟩ ⊗ (ℓ restricted to S)`, the restriction being `contragredientMap` of the inclusion
   `ScalarSubReduction.inclusion ρ S`; both sides agree pointwise by definition.
2. `smoothCoefficient_mem_irreducible`: in a semisimple module the simple submodules have
   supremum `⊤` (`IsSemisimpleModule.sSup_simples_eq_top`), so `v` (read in `ρ.asModule` through
   `ρ.asModuleEquiv`) lies in the supremum of the simple `ℂ[G]`-submodules `N`.
   `Submodule.iSup_induction` reduces to `v ∈ N`, `0` and sums; for `v ∈ N` the subrepresentation
   `Subrepresentation.ofSubmodule' N` is irreducible (`subrepresentationAsModuleEquiv` and
   `Representation.irreducible_iff_isSimpleModule_asModule`), and step 1 applies; the
   coefficient is additive in the vector.
3. `formCoefficient_mem_irreducible`: `admissibleUnitarySemisimplicity` with the form `b` makes
   `ρ` semisimple, then step 2 with `ℓ = b.toSmoothDual ha.1 e`.
4. `isSquareIntegrable_of_irreducible_subrepresentation`: `S` is admissible
   (`isAdmissible_of_injective`) and carries the restricted form `b.comap`; being irreducible it
   has a unitary central character (`unitarizableCentralCharacter`). Every smooth functional on
   `S` is `b(e, -)` restricted to `S` for some `e ∈ S` (`smoothDualEquiv`, which uses `hcof`), so
   the norm function of its coefficient with `w ∈ S` is, on classes `A g`, `‖b(e, ρ(g) w)‖`
   (`centralSubgroupCoefficientNorm_mk`), i.e. the function `F` given by `hL2`.
5. `formCoefficient_mem_squareIntegrable`: step 3 and monotonicity, using step 4 and the fact
   that `A` acts on `S` by `χ` because it does on `V` (`hχ`).
6. `exists_mem_squareIntegrable_of_reproducing`: apply step 5 to the `e` given by `hrep f`.

The implemented route follows Waldspurger's. It works with subrepresentations of `ρ` and their
own coefficient spaces instead of isomorphism classes `ω ∈ E₂(G)_χ`, and it takes formula (2)
and the reproducing identity as the hypotheses `hL2` and `hrep`.

## Relation to the Library

- Lemma III.1.3 (`SquareIntegrableSemisimplicity`) gives semisimplicity for square-integrable
  representations; here semisimplicity comes from admissibility and unitarity
  (`admissibleUnitarySemisimplicity`), as in the source.
- `range_coefficientTensorMap` (`CoefficientTensors`) identifies `LinearMap.range
  (coefficientTensorMap _)` with the span of the smooth matrix coefficients; that range is the
  coefficient space `A(S)` used here.
- The positive definite product of Proposition VIII.4.1 on `χ`-covariant functions, read
  through a section, is the inner product of `IsSectionReproducingKernel.Space`
  (`SectionReproducingKernel`). Producing from it the form `b`, the admissibility `ha` and the
  hypothesis `hL2` for Waldspurger's `V` is not done here.

## Open obligations

Formula (2) (`hL2` for Waldspurger's `V`), the reproducing identity `hrep` (Remark VIII.2.2,
Lemma VIII.2.3), the admissibility of `V` (Proposition VIII.4.1), `hcof` for Waldspurger's `G`,
the construction of `A₂(G)_χ` as a direct sum over `E₂(G)_χ`, the union over `H`, and the
first inclusion `A₂(G)_χ ⊂ p_χ(°C(G))` (via Theorem VII.2.5) are not proved here.
