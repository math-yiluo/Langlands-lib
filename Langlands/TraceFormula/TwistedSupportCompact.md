# Compact support condition from closed twisted orbits

Module `Langlands.TraceFormula.TwistedSupportCompact`, namespace `Langlands.TraceFormula`.

The Library's abstract simple twisted trace formula (`AbstractSimpleTwistedTraceFormulaStatement`,
module `Langlands.TraceFormula.AbstractSimpleTwistedStatement`) has the support hypothesis

`∃ C : Set G, IsCompact C ∧ ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y`,

which is automatic when `Γ \ G` is compact but not in general. This module derives it from two
geometric properties of finitely many representatives `r j`: the `θ`-twisted orbit of `r j` is
closed, and the rational quotient `(Γ ∩ C_{r j}) \ C_{r j}` of its `θ`-centralizer is compact.

## Declarations

- `exists_isCompact_subset_image_of_isOpenMap hf hs hK`: for a continuous open surjection
  `f : X → Y` (only openness and surjectivity are used) from a weakly locally compact space and a
  compact `K ⊆ Y`, there is a compact `L ⊆ X` with `K ⊆ f '' L`. Proof: the images of the
  interiors of compact neighbourhoods of all points of `X` are open and cover `Y`; finitely many
  cover `K`, and `L` is the union of the corresponding compact neighbourhoods.

- `exists_isCompact_twistedConj_mem Γ θ r hc ho hK`: let `G` be a Hausdorff, locally compact,
  σ-compact topological group, `Γ` a subgroup, `θ : G ≃ₜ* G`, `r : G`, with
  `hc : CompactSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r)))` and
  `ho : IsClosed (TwistedOrbit θ r)`. For every compact `K ⊆ G` there is a compact `C ⊆ G` such
  that every `x` with `twistedConj θ x r = x⁻¹ r θ(x) ∈ K` is `g * y` with `g ∈ Γ` and `y ∈ C`.

  Proof. Write `H` for the `θ`-centralizer of `r`; it is closed, hence locally compact. Since the
  orbit is closed, `twistedOrbitHomeomorph` (module `Langlands.TraceFormula.TwistedOrbitHomeomorph`)
  identifies `H \ G` with the orbit, so the set `Q` of cosets `H x` with `x⁻¹ r θ(x) ∈ K` is
  compact. Lift `Q` to a compact `L ⊆ G` and the compact space `(Γ ∩ H) \ H` to a compact
  `D ⊆ H`, both by the first lemma. If `x⁻¹ r θ(x) ∈ K`, then `H x = H y` for some `y ∈ L`, so
  `c = x y⁻¹ ∈ H`; then `(Γ ∩ H) c = (Γ ∩ H) d` for some `d ∈ D`, so `c d⁻¹ ∈ Γ`, and
  `x = (c d⁻¹) (d y)` with `d y` in the compact set `C = {d y | d ∈ D, y ∈ L}`.

- `exists_isCompact_twistedSupport Γ θ r hc ho f hf hcover`: with `G` as above, a finite index
  type `ι`, `r : ι → G` satisfying `hc` and `ho` for every `j`, a function `f : G → A` (`A` with a
  zero) whose closed support is compact, and the covering hypothesis
  `hcover : ∀ γ ∈ Γ, (∃ x, f (x⁻¹ * γ * θ x) ≠ 0) → ∃ j, IsTwistedConjugate Γ θ (r j) γ`, the
  support hypothesis above holds. Proof: take `C = ⋃ j, C j` for the sets `C j` of the previous
  lemma applied to `K = tsupport f`. If `f (x⁻¹ γ θ(x)) ≠ 0` and `γ = h⁻¹ (r j) θ(h)` with
  `h ∈ Γ`, then `(h x)⁻¹ (r j) θ(h x) = x⁻¹ γ θ(x)` lies in `tsupport f`, so `h x = g y` with
  `g ∈ Γ`, `y ∈ C j`, and `x = (h⁻¹ g) y`.

## Origin

The two geometric hypotheses mirror those of the simple relative trace formula in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), registered
`getz-hahn-2024-automorphic-representations`, Theorem 18.2.5 (printed p. 479): the orbits meeting
the support of the test function are closed, and their elements are relatively elliptic, so that
the centralizer volumes (18.14) are finite. The deduction of the support hypothesis above, through
the homeomorphism of `C_r \ G` with the closed orbit and the lifting of compact sets, is the
Library's own. Here compactness of the rational centralizer quotient is assumed, which for the
regular elliptic elements of `GL_n` is what the Library proves
(`adelicRegularCentralizerCompactQuotient`, module
`Langlands.TraceFormula.AdelicRegularCentralizerCompact`). The formulation, with a general
continuous automorphism `θ` and any finite family of representatives, is derived content of the
Library; `Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaProof` applies it with `θ` the
identity of `GL_n(𝔸_F)¹`.
