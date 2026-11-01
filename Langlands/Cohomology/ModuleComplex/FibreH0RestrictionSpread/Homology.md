# Homology of cochain complexes of modules with vanishing differentials

Author: Worker 1119.

Module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Homology`, namespace
`Langlands.Cohomology.ModuleComplex.FibreH0Spread`. It is a helper for the proof of
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement` (see `Main.md`). It
contains elementary facts about `ℤ`-indexed cochain complexes in `ModuleCat`, using only
Mathlib's homology API (`iCyclesIso`, `isoHomologyπ`, `homologyπ_naturality`). No `sorry` and
no new axioms.

## Over a ring `R`

- `jointly_injective_f_of_homologyMap`: let `f₁ : C ⟶ D₁` and `f₂ : C ⟶ D₂` be chain maps, and
  suppose `C.d (i - 1) i = 0` and `C.d i (i + 1) = 0`. If `H^i(f₁)` and `H^i(f₂)` are jointly
  injective (an element killed by both is zero), then so are `f₁.f i` and `f₂.f i` on `C.X i`.
  Proof: since `d^i = 0`, every `x : C.X i` is a cycle `c` (`iCyclesIso`). If `fⱼ` kills `x`,
  then `cyclesMap fⱼ` kills `c` (`iCycles` is injective), so `H^i(fⱼ)` kills the class of `c`
  (`homologyπ_naturality`). Hence the class is zero, and since `d^{i-1} = 0` the projection to
  homology is injective (`isoHomologyπ`). So `c = 0` and `x = 0`.
- `termIsoHomology C i h₀ h₁ : C.X i ≅ C.homology i`: if both differentials at `i` vanish, the
  term is its homology, `(iCyclesIso).symm ≪≫ isoHomologyπ`.
- `termIsoHomology_hom_naturality`: for a chain map `f : C ⟶ D` with both differentials at `i`
  zero in `C` and in `D`, `termIsoHomology` intertwines `f.f i` and `H^i(f)`.
- `bijective_homologyMap_iff`: under the same hypotheses, `H^i(f)` is bijective iff `f.f i` is
  bijective. This follows from the naturality square, since the horizontal maps are
  isomorphisms.

## Over a field `F`

- `d_eq_zero_of_finrank_homology`: if `C.X i` is finite dimensional and
  `finrank (C.homology i) = finrank (C.X i)`, then `C.d i (i + 1) = 0`. Proof:
  `finrank H^i ≤ finrank Z^i ≤ finrank C.X i`, since `homologyπ` is surjective and `iCycles` is
  injective. So the injection `Z^i → C.X i` is a map between spaces of equal finite dimension,
  hence surjective. Every element is then a cycle, and `iCycles_d` gives `d^i = 0`.

## Over a commutative ring `T`

- `d_zero_one_eq_zero`: let `Q` have zero term in degree `-1`, a term `Q.X 0 ≃ₗ[T] T`, a free
  term in degree `1`, and `Q.homology 0 ≃ₗ[T] T`. Then `Q.d 0 1 = 0`. Proof: since
  `d^{-1} = 0`, `H⁰ = Z⁰ ⊆ Q.X 0`. Transported to `T`, the inclusion is an injective `T`-linear
  map `j : T → T`, `j t = t * a` with `a = j 1`. The element of `Q.X 0` corresponding to `a` is
  a cycle, so `a • v = 0`, where `v = d⁰(e₀⁻¹ 1)`. Each coordinate `vᵢ` of `v` in a basis of
  `Q.X 1` satisfies `j vᵢ = vᵢ * a = 0`, so `vᵢ = 0` by injectivity of `j`. Then `v = 0`, and
  `d⁰` vanishes on `Q.X 0 = T · e₀⁻¹ 1`. No rank comparison over `T` is needed, so `T` may be
  any commutative ring.
- `bijective_of_comp_eq_smul`: let `M ≃ₗ[T] T` and `N ≃ₗ[T] T`, `f : M →ₗ[T] N`,
  `g : N →ₗ[T] M`, and `g ∘ₗ f = u • id` with `u` a unit. Then `f` is bijective. Proof: in the
  coordinates, `f` and `g` are multiplication by `t` and `s` with `t * s = u`. So `t` is a unit.
  Injectivity follows from `g ∘ f = u • id`, and surjectivity from invertibility of `t`.

## Provenance

Internal helper lemmas for the proof of Stacks tag 0BF2 (`more-morphisms.tex`, lines
9543–9619, registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The source uses that a minimal complex has
homology equal to its terms over the residue field and that the rank-one degree-zero term
with rank-one `H⁰` has vanishing outgoing differential. These lemmas state those facts in
`ModuleCat`.
