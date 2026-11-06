# A central-kernel character for the split component of a maximal parabolic

## The definition

Let `A` be a commutative group scheme over a field `k` and `i : A ⟶ G` a
homomorphism to a group scheme `G`. The internal predicate
`HasCentralKernelCharacter i` says that there is an integral character
`α₀ : characterLattice A` with this property: every integral cocharacter
`ν : cocharacterLattice A` with `latticePairing A α₀ ν = 0` becomes central in
`G` through `i`. That is, `IsCentral (CommGroupScheme.groupHom ν ≫ i)` holds.

The predicate puts no condition on `α₀` other than the displayed implication.
If every cocharacter is central through `i`, any `α₀` works.

## Linear algebra on a split torus

These results assume `IsSplitTorus A.toGrp`. Then the real pairing
`pair A` of `Vstar A = ℝ ⊗ X^*(A)` with `ℝ ⊗ X_*(A)` is perfect, by the
published `isPerfPair_of_isSplitTorus`.

- `eq_zero_of_pair_one_tmul_eq_zero` shows that a real character vanishing
  on every `1 ⊗ ν` is zero. Indeed `r ⊗ ν = r • (1 ⊗ ν)` and pure tensors span,
  so the character pairs to zero with everything. Left injectivity of the
  perfect pairing then gives zero.
- `exists_smul_of_pair_kernel hA α₀` gives a vector `e : Vstar A`. Every real
  character `y` that vanishes on `1 ⊗ ν` for all `ν` in the integral kernel
  of `α₀` is a real multiple of `e`. If `α₀` pairs to zero with every `ν`,
  then `e = 0` and `y = 0` by the previous lemma. Otherwise pick `ν₀` with
  `n₀ = ⟨α₀, ν₀⟩ ≠ 0` and take `e = 1 ⊗ α₀`. For every `ν`, the integral
  cocharacter `w = n₀ • ν - ⟨α₀, ν⟩ • ν₀` lies in the kernel of `α₀`. So
  `n₀ · y(ν) = ⟨α₀, ν⟩ · y(ν₀)`. Hence `y - (y(ν₀)/n₀) • (1 ⊗ α₀)` vanishes on
  every `1 ⊗ ν`, and it is zero by the previous lemma.
- `mem_span_of_hasCentralKernelCharacter hA hK hx0 hx y hy` combines the two
  lemmas. Let `x` be a nonzero real character that vanishes on `1 ⊗ ν` for
  every `ν` central through `i`, and let `y` be another such character. Then
  `y ∈ Submodule.span ℝ {x}`. A central-kernel character `α₀` puts both `x`
  and `y` on the line of the vector `e`. Since `x ≠ 0`, the coefficient of
  `x` is nonzero, so `y` is a multiple of `x`.

## Maximal parabolics

`hasCentralKernelCharacter_of_maximal` assumes `ParabolicDynamicStatement.{u}`
as an explicit hypothesis `hPD`. It does not prove that statement. Its
remaining hypotheses are those of `MaximalLeviConeComplementStatement`:

- `G` is connected reductive over a field;
- `p : P ⟶ G` is a parabolic subgroup that is not an isomorphism;
- `P` is maximal, in the target's form: every parabolic `q' : Q' ⟶ G` with a
  factorization `j ≫ q' = p` has `j` or `q'` an isomorphism;
- `l : M ⟶ P` is a rational Levi subgroup and `a : A ⟶ M` is its split
  component.

Under these hypotheses, `a ≫ l ≫ p` has a central-kernel character. The
proof goes as follows; write `i = a ≫ l ≫ p`.

1. `hPD` makes `P` a dynamic parabolic. The published
   `IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
   gives `ζ ∈ X_*(A)`. The map `p` represents `P(ζ ≫ i)`, and
   `Z(ζ ≫ i)` is the range of `l ≫ p`.
2. `Z(ζ ≫ i)` is proper. Otherwise `Dynamic.parabolic_eq_top_of_centralizer`
   makes the range of `p` everything. The shared lemma `isIso_of_full_range`
   would then make `p` an isomorphism. So by the published
   `rootAnnihilatorCentrality`, some relative root `α₀` of `i` has
   `⟨α₀, ζ⟩ ≠ 0`. This root is the central-kernel character.
3. Let `⟨α₀, ν⟩ = 0` and suppose `ν` is not central. The split component is
   central in `M`, so `isCentral_comp_iff_le_dynamicCentralizer` gives
   `Z(ζ ≫ i) ≤ Z(ν ≫ i)`. The inclusion is strict:
   `relativeRoot_pairing_eq_zero_of_centralizer_le` would otherwise force
   `⟨α₀, ζ⟩ = 0`. The published `exists_properCentralizerCoarsening` then
   gives `μ` with three properties: `P(ζ ≫ i) ≤ P(μ ≫ i)`,
   `Z(ζ ≫ i) < Z(μ ≫ i)`, and `Z(μ ≫ i) ≠ ⊤`.
4. The represented dynamic parabolic `q' : P(μ ≫ i) ⟶ G` is a parabolic
   subgroup by `hPD`, and `p` factors through it. By maximality, either the
   factor `j` or `q'` is an isomorphism.
   - If `j` is an isomorphism, `p` represents `P(μ ≫ a ≫ l ≫ p)`. Then
     `IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic` gives
     `Z(μ ≫ i) = range (l ≫ p) = Z(ζ ≫ i)`, which contradicts strictness.
   - If `q'` is an isomorphism, `P(μ ≫ i)` is everything. Then
     `Dynamic.parabolic_eq_top_iff_centralizer_eq_top` (`G` has trivial
     unipotent radical) gives `Z(μ ≫ i) = ⊤`, which contradicts properness.

The shared lemmas `isIso_of_full_range` and `full_range_of_isIso` relate
isomorphisms with full ranges of subgroup functors.

## Provenance

This module is internal, with no external literature source. The route of
`hasCentralKernelCharacter_of_maximal` is Worker 1785's argument from the
now-published `MaximalLeviDynamicReduction` module (original candidate
`a5baa80d`). The two identical range lemmas are reused from that module. This
module serves the proof of `MaximalLeviConeComplementStatement`: given a
nonzero real character `x` that vanishes on the central cocharacters, the
module puts every such character on the line of `x`.

The identical helper proofs are reused from `Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction`; their local copies have been removed.
