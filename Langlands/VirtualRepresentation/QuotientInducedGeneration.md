# Brauer induction for groups with a commutative open kernel of finite index

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`.
It proves the general theorem from which the target follows. Let `G` be a
topological group and `π : G →* Q` a homomorphism to a finite group whose kernel
is open and commutative. Then the continuous exact virtual group of `G`, with
carriers in the universe `max uG uV`, is spanned over `ℤ` by
`quotientInducedGenerators π hπ`. These are the classes
`Ind_{π⁻¹ H}^G θ` for subgroups `H` of `Q` and continuous characters
`θ : π⁻¹ H →ₜ* ℂˣ`. All declarations are in the namespace
`Langlands.VirtualRepresentation.ExactGrothendieckGroup`.

## Declarations

- `mem_of_forall_ofRepresentation_mem`: a submodule of an exact Grothendieck
  group containing every genuine class `ofRepresentation P A` is everything.
  The group is a quotient of the free module on genuine classes, so
  `Finsupp.induction_linear` and induction on the quotient apply.
- `subgroupOfContinuousInv hTS : T →ₜ* T.subgroupOf S` is the inverse of
  `subgroupOfContinuousHom` from `ExactInductionTransitivity`.
- `continuousInduce_mem_quotientInducedGenerators`: let `S` be an open
  finite-index subgroup containing `ker π`. Induction from `S` to `G` sends every
  generator of `S` for `π ∘ S.subtype` to a generator of `G`. A generator of
  `S` is induced from `H' = π⁻¹ H` inside `S`. Put `T = H'.map S.subtype`. Then
  `T ⊇ ker π`, and `T.subgroupOf S = H'`
  (`Subgroup.comap_map_eq_self_of_injective`), so
  `continuousInduce_characterClass_congr` changes the subgroup to
  `T.subgroupOf S`. Transitivity (`continuousInduce_continuousInduce_characterClass`)
  then gives `Ind_T^G θ₂`, a generator by `mem_quotientInducedGenerators_of_ker_le`.
- `ofRepresentation_mem_span_quotientInducedGenerators`: every genuine class
  lies in the span. This is proved by strong induction on the rank `n`.
  1. A zero-dimensional representation has class `0`.
  2. Otherwise the operators `ρ n`, `n ∈ ker π`, commute. The published
     `LieKolchin.exists_common_eigenvector` gives a nonzero common eigenvector
     `v` with eigenvalue function `χ`. Let `S = weightStabilizer N χ`; it contains
     `N = ker π`, so it is open and of finite index. Let
     `B = FiniteRepresentation.of (weightRep N ρ χ)`. It is continuous: it
     embeds in the restriction of `A` to `S`. It is nonzero, because it
     contains `v`.
  3. With `Ψ = cliffordMap`, injective by `cliffordMap_injective`, its range is
     a subrepresentation. The quotient `C = A / range Ψ` is continuous (the
     published `isContinuous_quotient`). The published defining exact relation
     `ofRepresentation_shortExact` gives `[A] = [Ind_S^G B] + [C]`. The published
     `rank_eq_add_of_shortExact` and `rank_induce` give
     `rank C < rank A`, so `[C]` is in the span by the induction hypothesis.
  4. `N` acts on `B` by scalars (`weightRep_scalar`). So
     `ScalarKernel.ofRepresentation_mem_span_of_scalar`, applied to
     `π ∘ S.subtype`, puts `[B]` in the span of the generators of `S`. Then
     `continuousInduce_mem_quotientInducedGenerators` carries `Ind_S^G [B]` into
     the span of the generators of `G`.
- `span_quotientInducedGenerators_eq_top π hπ hcomm` is the theorem:
  `Submodule.span ℤ (quotientInducedGenerators π hπ) = ⊤`.

No semisimplicity, unitarity or finite-image hypothesis is used. The only
hypotheses are that `Q` is finite and that `ker π` is open and commutative.

## Dependencies

The module imports `Langlands.VirtualRepresentation.CliffordReduction`,
`Langlands.VirtualRepresentation.ScalarKernelBrauer` and
`Langlands.VirtualRepresentation.ExactInductionTransitivity`. It uses the
published `LieKolchin.exists_common_eigenvector`,
`FiniteRepresentation.isContinuous_of_injective_intertwiner`,
`isContinuous_restrict`, `isContinuous_quotient`, `isContinuous_induce`,
`rank_induce`, `rank_eq_add_of_shortExact`,
`ExactGrothendieckGroup.ofRepresentation_shortExact` and
`induce_ofRepresentation`.
