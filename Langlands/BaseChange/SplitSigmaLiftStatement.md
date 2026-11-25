# Statement: `π ⊗ ⋯ ⊗ π` is a σ-lift of `π` at a split place

The module `Langlands.BaseChange.SplitSigmaLiftStatement` (namespace `Langlands.BaseChange`)
states, as the proposition `SplitSigmaLiftStatement.{u, uV, uW}`, the base change of
representations at a split place: the tensor power `π ⊗ ⋯ ⊗ π` of an irreducible admissible
representation `π` of `GL_n(F)` is a σ-lift of `π` with constant `1` for the cyclic shift of
the tensor factors, and every irreducible admissible σ-stable representation of
`GL_n(F^{l+1})` is such a tensor power. The statement is **not proved** here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL. II.1.3 (printed p. 56): `Π^σ`, σ-stability and
  the condition `A ∘ Π(g) = Π(g^σ) ∘ A`; II.2.7, Définition (printed p. 67): σ-lifts
  ("σ-relèvement") with constant `c`; II.2.8 (printed pp. 67–69): after identifying `G(E)` with
  `G(E₁)^r`, an irreducible `Π` is `Π₁ ⊗ ⋯ ⊗ Π_r`, and it is σ-stable if and only if `Π₁` is
  σ₁-stable and every `Π_i` is isomorphic to `Π₁` (pp. 67–68); for `Π = Π₁^{⊗r}` and the
  operator `A` built from `A₁` (p. 68), `Θ^A_Π(φ) = Θ^{A₁}_{Π₁}(φ*)`; and by the Remarque
  (p. 69), `Π₁^{⊗r}` is a σ-lift of `π` if and only if `Π₁` is a σ₁-lift of `π`. II.2.15
  (printed pp. 76–77) treats the split case `E₁ = F`, with `δ^σ = (δ₂, …, δ_d, δ₁)`. For the
  level-zero cuspidal representations `Π_{ϑ,α} = (π_{ϑ,α})^{⊗d}` it derives from II.2.8 that
  `Θ^A_Π(φ) = Θ_π(φ*)`. So `Π_{ϑ,α}` is a σ-lift of `π_{ϑ,α}`, with `c(π_{ϑ,α}, A) = 1` when
  `dg_E = (dg)^d`. HL state this only for these representations. The formula they take from
  II.2.8 holds for every admissible `π`, and II.2.16 (printed p. 77) relies on the same fact for a
  generic `π'` with `Π' ≅ π'^{⊗d}`. Part (a) states it for every irreducible admissible `π`.
  II.6.15 (printed p. 131): the constant `c(π'_v, I_σ(Π'_v))` for
  HL's normalized intertwiner `I_σ` is `1` at every place of `F` split in `E`, in particular at
  `v₁` and `v₂`.
- Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math.
  33, part 1 (1979), pp. 179–183, source ID `flath-1979-tensor-products` (the registered file
  is the Corvallis volume, Part I, SHA256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`, in which the printed
  page is the PDF page plus 4). Theorem 1 (printed p. 179, PDF p. 175): for locally compact
  totally disconnected groups `G₁`, `G₂`, the tensor product of irreducible admissible representations
  of `G₁` and `G₂` is an irreducible admissible representation of `G₁ × G₂`, and every
  irreducible admissible representation of `G₁ × G₂` is such a tensor product, with factors
  determined up to isomorphism.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`) and
`n l : ℕ`. Let `σ = splitCyclicShift F (l + 1)` on `F^{l+1} = Fin (l + 1) → F`, and write
`splitTensorRep π` for the representation `g ↦ π(g₀) ⊗ ⋯ ⊗ π(g_l)` of `GL_n(F^{l+1})` on
`⨂[ℂ] _ : Fin (l + 1), V` (module `SplitPlace`, with `l + 1` factors).

- **(a)** For every complex vector space `V : Type uV` and every representation
  `π : Representation ℂ (GL_n(F)) V` with `hπ : IsAdmissible π` and `π.IsIrreducible`:
  `splitTensorRep π` is admissible (a proof `hP` of `IsAdmissible` is asserted to exist) and
  irreducible, and there is a σ-intertwiner `A : SigmaIntertwiner σ n (splitTensorRep π)` whose
  underlying linear equivalence `A.toLinearEquiv` is `splitTensorShift V (l + 1)`
  (`v₀ ⊗ v₁ ⊗ ⋯ ⊗ v_l ↦ v₁ ⊗ ⋯ ⊗ v_l ⊗ v₀`) such that
  `IsSigmaLift σ (l + 1) π hπ (splitTensorRep π) hP A 1` holds: `splitTensorRep π` is a σ-lift
  of `π` with constant `1`, that is, for all Haar measures `μF` on `GL_n(F)` and `μE` on
  `GL_n(F^{l+1})` and all concordant `(φ, f)`, the twisted trace of `φ` in `splitTensorRep π`
  and `A` equals the trace of `f` in `π`.
- **(b)** For every complex vector space `W : Type uW` and every
  `ρ : Representation ℂ (GL_n(F^{l+1})) W` that is admissible, irreducible and σ-stable
  (`IsSigmaStable σ n ρ`), there are a complex vector space `V : Type uW` and a representation
  `π : Representation ℂ (GL_n(F)) V`, admissible and irreducible, with an isomorphism of
  representations `ρ ≅ splitTensorRep π` (`Nonempty (Representation.Equiv ρ (splitTensorRep
  π))`).

`IsSigmaLift` takes `T2Space`, `LocallyCompactSpace` and `TotallyDisconnectedSpace` instances
for `GL_n(F)` and `GL_n(F^{l+1})`. The statement supplies them locally with `haveI` from the
Library's `LocalFieldTopology.generalLinear_t2Space`, `generalLinear_locallyCompactSpace` and
`generalLinear_totallyDisconnectedSpace` (for `GL_n(F)`) and from
`generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite` and
`generalLinear_totallyDisconnectedSpace_of_finite` of `Langlands.BaseChange.TwistedCharacter`
applied to `E = F^{l+1}` (with Mathlib's
instances `Module.Finite F (Fin (l + 1) → F)` and `IsModuleTopology.instPi`). These are
propositions, so the choice of proofs does not matter.

**Convention for the intertwiner.** HL II.2.15 write the operator
`A(v₁ ⊗ ⋯ ⊗ v_d) = v_d ⊗ v₁ ⊗ ⋯ ⊗ v_{d-1}` with `Π(δ^σ) = A⁻¹ ∘ Π(δ) ∘ A` (the operator of
II.2.8, p. 68, has the same direction when `A₁ = 1`). The condition of HL II.1.3 and of
`SigmaIntertwiner` (`Langlands.BaseChange.TwistedCharacter`) is `A ∘ Π(g) = Π(g^σ) ∘ A`. The inverse operator `splitTensorShift`
satisfies this condition (lemma `splitTensorShift_comp` of `SplitPlace`). With this `A` the
twisted trace of a split tensor is the trace of `π(ψ₀) ⋯ π(ψ_l)` (see the proof idea). This
matches the order of the convolution product of `SplitMatchingStatement`.

## Use

In the global comparison of HL II.6.7–II.6.10 (printed pp. 123–126), the place `v₁` (II.6.7)
and an auxiliary place `v₂` (II.6.8) split completely in `E`. There
`SplitMatchingStatement` matches the test functions, and this statement matches the
representations. The local component of a σ-stable cuspidal `Π` is `Π_v ≅ π_v ⊗ ⋯ ⊗ π_v`
(part (b)), and `Π_v` is a σ-lift of `π_v` with constant `1` for the cyclic shift `A` (part
(a)). HL II.6.15 (printed p. 131) uses the corresponding fact for the constant
`c(π'_v, I_σ(Π'_v))` of their normalized intertwiner `I_σ`: "elle vaut 1 en toute place v de
F scindée dans E".

## Proof ideas (not formalized)

- **(a)** For pure tensors, `splitTensorRep π (ψ₀ ⊗ ⋯ ⊗ ψ_l) ∘ splitTensorShift` sends
  `v₀ ⊗ ⋯ ⊗ v_l` to `π(ψ₀) v₁ ⊗ ⋯ ⊗ π(ψ_{l-1}) v_l ⊗ π(ψ_l) v₀`, whose trace is
  `trace(π(ψ₀) ⋯ π(ψ_l)) = trace π(ψ₀ * ⋯ * ψ_l)` (on the finite-dimensional invariants of a
  small compact open subgroup); with `SplitMatchingStatement` and `μE = μF^{⊗(l+1)}`, this is HL II.2.8's
  `Θ^A_Π(φ) = Θ_π(φ*)`. Split tensors span the test functions on `GL_n(F^{l+1})`, and in
  characteristic zero a test function whose regular semisimple orbital integrals vanish has
  trace zero in every admissible representation (density of regular semisimple orbital
  integrals); so the identity passes from `(φ, φ*)` to every concordant pair `(φ, f)`, for
  every pair of Haar measures since both sides scale in the same way. Irreducibility and
  admissibility of `π ⊗ ⋯ ⊗ π` are Flath's Theorem 1.
- **(b)** Flath's Theorem 1, applied `l` times, gives `ρ ≅ π₀ ⊗ ⋯ ⊗ π_l` with irreducible
  admissible `π_i`; σ-stability gives `π_i ≅ π_{i+1}` for all `i` (as in HL II.2.8), so
  `ρ ≅ π₀ ⊗ ⋯ ⊗ π₀`; and `π₀` can be realized on a space in the universe of `W` (for instance
  inside `W`, as a subrepresentation of the restriction of `ρ` to the first factor), which is
  why `V : Type uW`.

## Hypotheses

- `CharZero F`, as in other base-change statements of the Library (for instance
  `RegularTransferStatement`, `TwistedCharacterRegularValuesStatement` and
  `CuspidalPseudoCoefficientExistenceStatement`): the Library's `IsRegularSemisimple` (used in
  `AreConcordant`) asks for a separable characteristic polynomial, which is HL's regularity in
  characteristic zero, and the proof idea of (a) uses the density of regular semisimple
  orbital integrals in characteristic zero.
- The statement is for `F^{l+1}`, because `F^0` is the zero ring.
- `IsCyclicAlgebra (splitCyclicShift F (l + 1)) (l + 1)` is proved in `SplitPlace` and is not
  a hypothesis.
- In (a), irreducibility and admissibility of `π` are hypotheses, and the admissibility of
  `splitTensorRep π` is part of the conclusion (it is needed to state `IsSigmaLift`).

## Measures

No measure appears outside `IsSigmaLift`, which quantifies over all Haar measures `μF` on
`GL_n(F)` and `μE` on `GL_n(F^{l+1})` (Borel σ-algebras, introduced inside `IsSigmaLift`) and
over all concordant pairs for them. So part (a) is **not** tied to `IsSplitProductHaar`: the
constant `1` of HL II.2.15 is the constant for every pair of Haar measures, because
concordance of `(φ, f)` and both twisted and ordinary traces scale compatibly (an
explanation, not proved here). In contrast,
`SplitMatchingStatement` (b), a pointwise matching of the functions `ψ₀ ⊗ ⋯ ⊗ ψ_l` and `ψ₀ * ⋯ * ψ_l`,
is tied to `IsSplitProductHaar`.

## Dependencies and names

The module imports `Langlands.BaseChange.SplitPlace` (`splitCyclicShift`,
`splitTensorRep`, `splitTensorShift`), `Langlands.BaseChange.TwistedCharacter`
(`SigmaIntertwiner`, `IsSigmaStable`, `IsSigmaLift` and the topology lemmas
`generalLinear_*_of_finite`), the Library's `Langlands.Group.GL.LocalFieldTopology` and
`IsAdmissible`, and Mathlib's `Representation.IsIrreducible` and `Representation.Equiv`. The
names and argument orders are those of these modules.
