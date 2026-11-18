# Statement: matching of test functions at a split place

The module `Langlands.BaseChange.SplitMatchingStatement` (namespace `Langlands.BaseChange`)
states, as the proposition `SplitMatchingStatement.{u}`, that at a split place the split tensor
`ψ₀ ⊗ ⋯ ⊗ ψ_l` of test functions on `GL_n(F)` and their convolution product
`ψ₀ * ⋯ * ψ_l` are concordant when the Haar measure on `GL_n(F^{l+1})` is the product of the
Haar measure on `GL_n(F)`. The statement is **not proved** here.

## Sources

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14). Cited as AC. Chapter 1, §5 (printed pp. 48–49): the
  σ-centralizer equations (5.1), the change of variables (5.2), and the conclusion that the
  σ-twisted orbital integrals of `φ₁ ⊗ ⋯ ⊗ φ_m` coincide with the orbital integrals of
  `φ₁ * ⋯ * φ_m`, "the quotient measures [being] normalized in obvious ways".
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL. II.2.8 (printed pp. 67–68): the map
  `φ ↦ φ*`, `φ₁ ⊗ ⋯ ⊗ φ_r ↦ φ₁ * ⋯ * φ_r`, and its Remarque (printed p. 69):
  `Λ_σ^{G(E)}(φ, δ) = Λ_{σ₁}^{G(E₁)}(φ*, y)` with `y = N'₁(δ)`, so that `φ` and `f` concord at
  `(δ, γ)` if and only if `φ*` and `f` concord at `(y, γ)`; II.2.15 (printed pp. 76–77): the
  split case, `δ^σ = (δ₂, …, δ_d, δ₁)`, `N(O_σ(δ)) = O(N¹(δ))` with `N¹(δ) = δ₁ ⋯ δ_d`
  surjective, and `dg_E = (dg)^d`; I.2.5, Définition (printed p. 17): concordant functions;
  II.2.6 (printed p. 66): functions with a central character, compactly supported modulo the
  centre, and the passage of concordance to them by averaging over the centre; II.2.16
  (printed p. 77): the functions `Φ_{Λ,α}` on `G(E) = G(F)^d` and `F_{λ,α}` on `G(F)`
  concord strongly; II.6.7–II.6.10 (printed pp. 123–126): the global comparison.

## The statement

Let `F : Type u` be a nonarchimedean local field (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), `n l : ℕ`, and let `GL_n(F)` and
`GL_n(F^{l+1})` (with `F^{l+1} = Fin (l + 1) → F`) carry their Borel σ-algebras, introduced
locally with `letI ... := borel _` and `BorelSpace` instances `⟨rfl⟩`. Let
`σ = splitCyclicShift F (l + 1)`, `(σ x) i = x (i + 1)`. For every Haar measure `μF` on
`GL_n(F)`:

- **(a)** there is a Haar measure `μE` on `GL_n(F^{l+1})` with `IsSplitProductHaar μF μE`
  (`μE` integrates every split tensor `ψ₀ ⊗ ⋯ ⊗ ψ_l` to `∏ i, ∫ ψ i dμF`);
- **(b)** for every Haar measure `μE` on `GL_n(F^{l+1})` with `IsSplitProductHaar μF μE` and
  every `ψ : Fin (l + 1) → SchwartzBruhat (GL_n(F))`, the functions
  `splitTensor (fun i => ψ i)` on `GL_n(F^{l+1})` (Task 7457: `g ↦ ∏ i, ψ i (g_i)`) and
  `convolutionProduct μF ψ` on `GL_n(F)` (`ψ 0 * (ψ 1 * (⋯ * ψ l))`, convolution for `μF`)
  satisfy Task 7416's `AreConcordant σ (l + 1) μF μE`: the orbital integrals of the
  convolution product vanish at the regular semisimple non-norms, and for every pair
  `(δ, γ)` of associated elements with `γ` regular semisimple, the σ-orbital integral of the
  split tensor at `δ` equals the orbital integral of the convolution product at `γ`, for all
  associated right Haar measures on the centralizers and all compatible quotient measures.

The split convention, the definitions `splitCyclicShift`, `convolutionProduct` and
`IsSplitProductHaar`, and the reason why `IsSplitProductHaar` is stated through integrals of
split tensors are explained in the Markdown of `Langlands.BaseChange.SplitPlace`.

## Use

This statement is the local matching principle at a split place for compactly supported
test functions: in the split case `E₁ = F`, `σ₁ = id`, it is the content of the Remarque of
HL II.2.8 (printed p. 69) for pure tensors, namely that `φ₀ ⊗ ⋯ ⊗ φ_l` and its convolution
product `φ₀ * ⋯ * φ_l` concord, with `dg_E = (dg)^d` as in II.2.15.

In the global comparison of HL II.6.7–II.6.10 (printed pp. 123–126), the place `v₁` of the
cuspidal test function splits completely in `E` (`E_{v₁} = F_{v₁}^d`). II.6.7 (printed
pp. 123–124) fixes `f_{v₁} = F_{λ,α}`, and II.6.10 (printed p. 126) takes for `φ_{v₁}` the
tensor product `Φ_{Λ,α}` of functions on the factors, which concords with `F_{λ,α}` by the
lemma of II.2.16 (printed p. 77). HL prove that lemma directly, through
`(Φ_{Λ,α})* = F_{λ,α}` and the Remarque of II.2.8, in the setting of functions with a central
character: `Φ_{Λ,α}` and `F_{λ,α}` are compactly supported only modulo the centre (the spaces
of II.2.6, printed p. 66), and the convolution of II.2.16 is taken for a Haar measure `d¯g`
on the quotient by the centre. These functions are therefore not inputs of this statement,
which is about compactly supported `SchwartzBruhat` functions on `GL_n(F)` and convolution for
a Haar measure `μF` on `GL_n(F)`; II.2.6 explains how concordance passes in general from
compactly supported functions to functions with a central character, by averaging over the
centre (`f ↦ f_ω`, `φ ↦ φ_χ`), which is not formalized here. At the auxiliary place `v₂`,
split in `E` (II.6.8, printed p. 124), II.6.10 allows any concordant pair `(φ_{v₂}, f_{v₂})`
supported in `G(E_{v₂})_{σ-r} × G(F_{v₂})_r` and prescribes no pure tensor. Statement 10
(`SplitSigmaLiftStatement`) matches the representations at split places
(`Π_v = π_v ⊗ ⋯ ⊗ π_v`).

## Proof idea (not formalized)

AC's computation (5.1)–(5.2). The σ-centralizer of `δ = (γ, 1, …, 1)` consists of the
`x = (x₀, …, x_l)` with `x₀⁻¹ γ x₁ = γ` and `x_i = x_{i+1}` for `i ≥ 1` and `x_l = x₀`, that
is, of `G_γ(F)` embedded diagonally. The σ-orbital integral of `ψ₀ ⊗ ⋯ ⊗ ψ_l` at `δ` is
`∫ ψ₀(x₀⁻¹ γ x₁) ψ₁(x₁⁻¹ x₂) ⋯ ψ_l(x_l⁻¹ x₀) dx`, and the change of variables
`y_i = x₀⁻¹ γ x_i` (`i ≥ 1`) turns it into the orbital integral of `ψ₀ * ⋯ * ψ_l` at `γ`,
the product measure `μE` producing the convolutions for `μF`. Every `δ` is σ-conjugate to an
element `(γ, 1, …, 1)` with `γ` conjugate to `δ₀ ⋯ δ_l` (compare HL II.2.15,
`N(O_σ(δ)) = O(N¹(δ))`), and every `γ ∈ GL_n(F)` is the
norm of `(γ, 1, …, 1)`, so the condition `VanishesOffNorms` in `AreConcordant` is vacuous.
Part (a) is the existence of the product Haar measure on `GL_n(F)^{l+1}`, transported to
`GL_n(F^{l+1})` by the coordinate maps.

## Hypotheses

- No `CharZero F` hypothesis: the computation is valid in every characteristic, and HL
  II.2.15 is stated in their setting of arbitrary characteristic. `AreConcordant` tests the
  orbital integrals at regular semisimple elements in the Library's sense (separable
  characteristic polynomial); in positive characteristic this is a smaller set of test
  elements than HL's regular elements (I.2.3, printed p. 13, which allow inseparable
  irreducible factors), so there (b) asserts a weaker concordance than HL's.
- The statement is for `F^{l+1}`, not `F^l`: `F^0` is the zero ring, for which
  `IsCyclicAlgebra` fails, and `convolutionProduct` is defined for at least one factor.
- Over `F^{l+1}` with the shift, `IsCyclicAlgebra (splitCyclicShift F (l + 1)) (l + 1)` holds
  and is proved in `SplitPlace` (`isCyclicAlgebra_splitCyclicShift`); it is therefore not a
  hypothesis of the statement.

## Measures

Every measure is quantified: `μF` and `μE` are arbitrary Haar measures, with `μE` constrained
in (b) only by `IsSplitProductHaar μF μE`; the centralizer and quotient measures are
quantified inside `AreConcordant`. Part (b) is a pointwise identity between integrals, so it
depends on the normalization `IsSplitProductHaar`: replacing `μE` by `c • μE` multiplies the
compatible quotient measures on `G^σ_δ(F) \ GL_n(F^{l+1})`, hence the σ-orbital integrals,
by `c`, while the convolution product depends on `μF` only (an explanation, not part of the
statement). Part (a) shows that
the hypothesis of (b) can be met for every `μF`.

## Dependencies and names

The module imports `Langlands.BaseChange.SplitPlace` (this task: `splitCyclicShift`,
`convolutionProduct`, `IsSplitProductHaar`), Task 7457's `splitTensor` (through `SplitPlace`)
and Task 7416's `Langlands.BaseChange.OrbitalIntegral` (`AreConcordant`), with the names and
argument orders cited in the task.
