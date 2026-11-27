# Maps of the end ring to henselian local rings

Module `Langlands.Correspondence.Laumon.EndRingStageMaps`. It proves the universal property in
`EndTraitHenselizationStatement` (module `Langlands.Correspondence.Laumon.Traits`): for a ring
map `φ : k[x] → B` to a henselian local ring with `φ⁻¹(𝔪_B) = (x)`, there is a unique local ring
map `endRing k → B` whose composite with the chart coordinate `ι : k[x] → endRing k`, `x ↦ t`, is
`φ` (`existsUnique_endRing_hom`). The stage rings and simple points are those of the modules
`Langlands.Correspondence.Laumon.EndRingStages` and
`Langlands.Correspondence.Laumon.EndRingSimplePoints`.

## The polynomials vanishing at a simple point

`exists_dvd_of_isSimplePoint`: for a simple point `b` there is `μ ∈ k[x][Y]` with `μ(b) = 0`,
`μ'(b)` a unit, and `μ ∣ p` for every `p ∈ k[x][Y]` with `p(b) = 0`. Here `b` is algebraic over
`k(t)`; `μ` is the primitive part (`Polynomial.primPart`) of an integral multiple of its minimal
polynomial, so the image of `μ` over `k(t)` is a nonzero multiple of the minimal polynomial and
divides the image of every `p` vanishing at `b`, and Gauss's lemma
(`Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`) gives `μ ∣ p` in `k[x][Y]`.
Writing the polynomial `G` of the simple point as `μ H`, `G'(b) = μ'(b) H(b)` shows that `μ'(b)`
is a unit.

## Residues

- `constantResidue k φ : k → κ_B` is `c ↦ (φ(c) mod 𝔪_B)` (an internal abbreviation).
- `residue_comp_eq`: `(φ(a) mod 𝔪_B) = constantResidue k φ (a(0))` for `a ∈ k[x]`, because
  `φ(x) ∈ 𝔪_B`.
- `residue_eval₂`: if `y ∈ B` has residue `constantResidue k φ (b(0))`, then the residue of
  `p^φ(y)` is the image of the residue of `p(b)`, for every `p ∈ k[x][Y]`.
- `residue_apply_of_isLocalHom`: a local map `ψ : endRing k → B` with `ψ ∘ ι = φ` sends every
  `x` to an element with residue `constantResidue k φ (x(0))`, as `x - x(0)` is a nonunit.

## Maps out of a stage ring

- `exists_stageHom`: for a simple point `b`, there is a ring map `ψ : stage k b → B` with
  `ψ(ι a) = φ(a)` and residues compatible with `constantResidue k φ`. Take `μ` as above. The
  polynomial `μ^φ` has the simple residual root `b(0)`, so by
  `Langlands.CommutativeAlgebra.exists_isRoot_sub_mem_maximalIdeal` (for a polynomial that need
  not be monic) it has a root `β ∈ B` with the residue of `b`. Evaluation at `β` sends the
  complement of `stagePrime k b` to units of `B` (`residue_eval₂`), hence extends to the
  localization `StageLocalization k b`; it kills the kernel of `stageMap k b`, since `p(b) = 0`
  implies `μ ∣ p` and `μ^φ(β) = 0`. So it factors through `stage k b`
  (`exists_ringHom_comp_eq`, a restatement of Mathlib's `RingHom.liftOfSurjective`). Residue
  compatibility is checked on the localization (`IsLocalization.ringHom_ext`).
- `stageHom_ext`: two ring maps `stage k b → B` that agree with `φ` on `ι(k[x])` and send `b` to
  elements with the residue of `b` are equal. Both send `b` to roots of `G^φ`, congruent modulo
  `𝔪_B`, at which `(G^φ)'` is a unit; simple roots are unique in a local ring
  (`Langlands.CommutativeAlgebra.eq_of_isRoot_of_sub_mem_maximalIdeal`). So both maps agree on
  the image of `k[x][Y]`, hence on the localization, hence on `stage k b`.

## Gluing

`existsUnique_endRing_hom`. Choose for every `x` a simple point `b₀(x)` with `x ∈ stage k b₀(x)`,
and for every simple point `b` the map `ψ_b` of `exists_stageHom`. If `b ∈ stage k b'`, then
`ψ_b` is the restriction of `ψ_{b'}` (`stage_le_stage`, `stageHom_ext`). As any two simple points
lie in a common stage ring (`exists_isSimplePoint_mem_stage`), `ψ_{b₀(x)}(x) = ψ_b(x)` for every
simple point `b` with `x ∈ stage k b`. Hence `ψ(x) = ψ_{b₀(x)}(x)` is additive and multiplicative
(put `x`, `y` in one stage ring), extends `φ`, and is local because residues are compatible. If
`ψ'` is another local map extending `φ`, its restriction to `stage k b₀(x)` satisfies the
hypotheses of `stageHom_ext` (by `residue_apply_of_isLocalHom`), so `ψ'(x) = ψ(x)`.

This is the universal property of the henselization of `k[x]_(x)` (Stacks Project, Section
10.155) for the ring `endRing k`.

Provenance: internal. The argument is an elementary form, for subrings of `k⟦t⟧`, of the
construction of the henselization as a filtered colimit over pointed étale neighbourhoods
(Stacks Project, Lemma 10.155.1): the stage rings, local rings of `k[x][Y] / (μ)` at a point over
`x = 0` where `∂μ/∂Y` does not vanish, play the role of the étale neighbourhoods, and the
uniqueness of maps out of them into a henselian local ring is the uniqueness of simple roots.
