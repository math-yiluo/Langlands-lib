import Langlands.TraceFormula.TwistedOrbitHomeomorph

/-!
# Compact support condition from closed twisted orbits and compact centralizer quotients

Let `G` be a Hausdorff, locally compact, σ-compact group, `Γ` a subgroup, `θ` a continuous
automorphism of `G` and `r ∈ G`. Suppose that the `θ`-twisted orbit `{x⁻¹ r θ(x)}` is closed
and that `(Γ ∩ C_r) \ C_r` is compact, where `C_r` is the `θ`-centralizer of `r`. Then for every
compact `K ⊆ G` the set `{x | x⁻¹ r θ(x) ∈ K}` lies in `Γ · C` for one compact `C ⊆ G`: the
closed orbit is homeomorphic to `C_r \ G`, so the preimage of `K` there is compact and lifts to a
compact set of `G`, and `C_r` is `(Γ ∩ C_r)` times a compact set.

For a function `f` with compact support whose nonzero twisted conjugates `x⁻¹ γ θ(x)`, `γ ∈ Γ`,
come from finitely many such `r j` up to `Γ`-twisted conjugacy, this gives the compact support
hypothesis of the Library's abstract simple twisted trace formula
(`AbstractSimpleTwistedTraceFormulaStatement`).
-/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.QuotientIntegration Topology

/-- A compact subset of the target of a continuous open surjection from a weakly locally compact
space is covered by the image of a compact set. -/
theorem exists_isCompact_subset_image_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f)
    (hs : Function.Surjective f) {K : Set Y} (hK : IsCompact K) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ f '' L := by
  choose N hNc hNx using fun x : X => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => f '' interior (N x))
    (fun x => hf _ isOpen_interior) (by
      intro y _
      obtain ⟨x, rfl⟩ := hs y
      exact Set.mem_iUnion.2 ⟨x, Set.mem_image_of_mem f (mem_interior_iff_mem_nhds.2 (hNx x))⟩)
  refine ⟨⋃ x ∈ t, N x, t.isCompact_biUnion fun x _ => hNc x, ?_⟩
  intro y hy
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
  obtain ⟨z, hz, rfl⟩ := hyx
  exact ⟨z, Set.mem_biUnion hx (interior_subset hz), rfl⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- If the `θ`-twisted orbit of `r` is closed and `(Γ ∩ C_r) \ C_r` is compact, then for every
compact `K` the conjugators `x` with `x⁻¹ r θ(x) ∈ K` lie in `Γ · C` for a compact `C`. -/
theorem exists_isCompact_twistedConj_mem [SigmaCompactSpace G] (Γ : Subgroup G)
    (θ : G ≃ₜ* G) (r : G)
    (hc : CompactSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r))))
    (ho : IsClosed (TwistedOrbit θ r)) {K : Set G} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧
      ∀ x : G, twistedConj θ x r ∈ K → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y := by
  let H := twistedCentralizer θ r
  have hH : IsClosed (H : Set G) := by
    change IsClosed {x : G | x⁻¹ * r * θ x = r}
    exact isClosed_eq ((continuous_inv.mul continuous_const).mul θ.continuous) continuous_const
  let : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let e := twistedOrbitHomeomorph θ r ho.isLocallyClosed
  have hK' : IsCompact ((Subtype.val : TwistedOrbit θ r → G) ⁻¹' K) :=
    ho.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQ : IsCompact (e ⁻¹' ((Subtype.val : TwistedOrbit θ r → G) ⁻¹' K)) :=
    e.isCompact_preimage.2 hK'
  obtain ⟨L, hL, hQL⟩ := exists_isCompact_subset_image_of_isOpenMap
    (leftQuotient_isOpenQuotientMap H).isOpenMap (leftQuotient_isOpenQuotientMap H).surjective hQ
  obtain ⟨D, hD, hDuniv⟩ := exists_isCompact_subset_image_of_isOpenMap
    (leftQuotient_isOpenQuotientMap (Γ.subgroupOf H)).isOpenMap
    (leftQuotient_isOpenQuotientMap (Γ.subgroupOf H)).surjective isCompact_univ
  refine ⟨(fun p : H × G => (p.1 : G) * p.2) '' (D ×ˢ L),
    (hD.prod hL).image ((continuous_subtype_val.comp continuous_fst).mul continuous_snd), ?_⟩
  intro x hx
  have hxQ : leftQuotientMap H x ∈ e ⁻¹' ((Subtype.val : TwistedOrbit θ r → G) ⁻¹' K) := hx
  obtain ⟨y, hyL, hy⟩ := hQL hxQ
  have hxy : x * y⁻¹ ∈ H := QuotientGroup.rightRel_apply.1 (Quotient.exact hy)
  let c : H := ⟨x * y⁻¹, hxy⟩
  obtain ⟨d, hdD, hd⟩ := hDuniv (Set.mem_univ (leftQuotientMap (Γ.subgroupOf H) c))
  have hcd : c * d⁻¹ ∈ Γ.subgroupOf H := QuotientGroup.rightRel_apply.1 (Quotient.exact hd)
  refine ⟨x * y⁻¹ * (d : G)⁻¹, Subgroup.mem_subgroupOf.1 hcd, (d : G) * y,
    ⟨(d, y), ⟨hdD, hyL⟩, rfl⟩, ?_⟩
  group

/-- If `f` has compact support and every `γ ∈ Γ` with a nonzero value `f(x⁻¹ γ θ(x))` is
`Γ`-`θ`-conjugate to one of finitely many `r j` with closed twisted orbits and compact
`(Γ ∩ C_{r j}) \ C_{r j}`, then every `x` with `f(x⁻¹ γ θ(x)) ≠ 0` for some `γ ∈ Γ` lies in
`Γ · C` for one compact `C`. This is the support hypothesis of
`AbstractSimpleTwistedTraceFormulaStatement`. -/
theorem exists_isCompact_twistedSupport [SigmaCompactSpace G] (Γ : Subgroup G) (θ : G ≃ₜ* G)
    {ι : Type*} [Finite ι] (r : ι → G)
    (hc : ∀ j, CompactSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r j)))))
    (ho : ∀ j, IsClosed (TwistedOrbit θ (r j)))
    {A : Type*} [Zero A] (f : G → A) (hf : IsCompact (tsupport f))
    (hcover : ∀ γ ∈ Γ, (∃ x : G, f (x⁻¹ * γ * θ x) ≠ 0) →
      ∃ j, IsTwistedConjugate Γ θ (r j) γ) :
    ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y := by
  choose C hC hCx using fun j => exists_isCompact_twistedConj_mem Γ θ (r j) (hc j) (ho j) hf
  refine ⟨⋃ j, C j, isCompact_iUnion hC, ?_⟩
  intro x γ hγ hfx
  obtain ⟨j, h, hh, rfl⟩ := hcover γ hγ ⟨x, hfx⟩
  have hmem : twistedConj θ (h * x) (r j) ∈ tsupport f := by
    apply subset_tsupport
    convert hfx using 2
    simp only [twistedConj_apply, mul_inv_rev, map_mul, mul_assoc]
  obtain ⟨g, hg, y, hy, hxy⟩ := hCx j (h * x) hmem
  refine ⟨h⁻¹ * g, Γ.mul_mem (Γ.inv_mem hh) hg, y, Set.mem_iUnion.2 ⟨j, hy⟩, ?_⟩
  rw [mul_assoc, ← hxy, inv_mul_cancel_left]

end Langlands.TraceFormula
