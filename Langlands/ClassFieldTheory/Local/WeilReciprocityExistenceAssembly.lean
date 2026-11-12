import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityExistenceProof
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityCompletionProof
import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationProof
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.Weil.Local.AssemblyProof

/-! # Assembly of geometric local Weil reciprocity from range facts

The candidate isomorphism is built from the two embeddings of the Weil
abelianization and of the field units into the product of the Galois
abelianization with the degree group.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

namespace WeilReciprocityExistence

open Weil Weil.Local ReciprocitySystemUniqueness Langlands.ClassFieldTheory.Local

section Topology

variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [DiscreteTopology D]

omit [IsTopologicalGroup D] in
/-- A homomorphism into a discrete group with open kernel is continuous. -/
theorem continuous_of_isOpen_ker [ContinuousMul D] (d : G →* D)
    (h : IsOpen (d.ker : Set G)) : Continuous d := by
  apply continuous_of_continuousAt_one d
  rw [ContinuousAt, map_one, nhds_discrete D, Filter.tendsto_pure]
  exact Filter.mem_of_superset (h.mem_nhds d.ker.one_mem) fun _ hx => hx

/-- A continuous injective homomorphism into a Hausdorff group, paired with a
continuous homomorphism to a discrete group whose kernel is compact, is
inducing. -/
theorem isInducing_prod_of_isCompact_ker (f : G →* H) (hf : Continuous f)
    (hinj : Function.Injective f) (d : G →* D) (hd : Continuous d)
    (hK : IsCompact (d.ker : Set G)) :
    Topology.IsInducing (f.prod d) := by
  rw [IsTopologicalGroup.isInducing_iff_nhds_one]
  have hc : Continuous (f.prod d) := by
    rw [MonoidHom.coe_prod]
    exact hf.prodMk hd
  apply le_antisymm
  · have h := (hc.tendsto 1).le_comap
    rwa [map_one] at h
  · intro S hS
    let K := d.ker
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hemb : Topology.IsClosedEmbedding (fun k : K => f k) :=
      (hf.comp continuous_subtype_val).isClosedEmbedding
        (hinj.comp Subtype.val_injective)
    have hS' : ((↑) : K → G) ⁻¹' S ∈ nhds (1 : K) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hS
    rw [hemb.isInducing.nhds_eq_comap] at hS'
    obtain ⟨O, hO, hOS⟩ := hS'
    refine ⟨O ×ˢ {1}, ?_, ?_⟩
    · rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (by simpa using hO) (by simp [nhds_discrete])
    · rintro g ⟨hgO, hgd⟩
      have hgK : g ∈ K := hgd
      exact hOS (show f g ∈ O from hgO) (a := ⟨g, hgK⟩)

end Topology

section Assembly

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

/-- The normalized order on field units is continuous for the supplied topology,
and its kernel, the integral units, is compact. -/
theorem orderHom_continuous_isCompact_ker :
    letI := T.topology
    Continuous T.orderHom ∧ IsCompact (T.orderHom.ker : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hker : T.orderHom.ker = T.unitSubgroup := by
    ext x
    exact (T.mem_unitSubgroup_iff_orderHom x).symm
  refine ⟨continuous_of_isOpen_ker T.orderHom ?_, ?_⟩
  · rw [hker]
    exact isOpen_unitSubgroup F T
  · rw [hker, ← T.unitFiltration_zero]
    exact T.isCompact_unitFiltration 0

/-- The degree on the actual Weil abelianization is continuous with compact
kernel, the image of compact Weil inertia. -/
theorem weilDegree_isCompact_ker :
    IsCompact ((WeilQuotients.degree (localResidueDegree F)).toMonoidHom.ker :
      Set (WeilQuotients.Abelianization (localResidueDegree F))) := by
  change IsCompact (WeilQuotients.inertia (localResidueDegree F) :
    Set (WeilQuotients.Abelianization (localResidueDegree F)))
  rw [WeilQuotients.inertia_eq_image, Subgroup.coe_map]
  exact (localInertia_isCompact F).image (WeilQuotients.projection _).continuous

/-- A continuous injective homomorphism from field units to the Galois
abelianization, whose pairing with the normalized order has the same image as
the pairing of the Weil-to-Galois map with the Weil degree, comes from a
candidate with geometric order whose induced Galois map is the given one. -/
theorem exists_candidate_of_range :
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      Function.Injective r →
      (∀ a : F.Carrierˣ, ∃ w : WeilQuotients.Abelianization (localResidueDegree F),
        WeilQuotients.toGroupAbelianization (localResidueDegree F) w = r a ∧
          WeilQuotients.degree (localResidueDegree F) w = T.orderHom a) →
      (∀ w : WeilQuotients.Abelianization (localResidueDegree F), ∃ a : F.Carrierˣ,
        r a = WeilQuotients.toGroupAbelianization (localResidueDegree F) w ∧
          T.orderHom a = WeilQuotients.degree (localResidueDegree F) w) →
      ∃ e : WeilReciprocityCandidate T (localResidueDegree F),
        GeometricOrderRelation T (localResidueDegree F) e ∧
          candidateGaloisHom T (localResidueDegree F) e = r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let := abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  intro r hinj hR₁ hR₂
  let φ := localResidueDegree F
  let ι := WeilQuotients.toGroupAbelianization φ
  let δ := WeilQuotients.degree φ
  let JW := ι.toMonoidHom.prod δ.toMonoidHom
  let JF := r.toMonoidHom.prod T.orderHom
  have hJWinj : Function.Injective JW := fun x y h =>
    WeilReciprocityUniqueness.toGroupAbelianization_injective F (congrArg Prod.fst h)
  have hJFinj : Function.Injective JF := fun x y h => hinj (congrArg Prod.fst h)
  have hrange : JW.range = JF.range := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨a, ha₁, ha₂⟩ := hR₂ w
      exact ⟨a, Prod.ext ha₁ ha₂⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨w, hw₁, hw₂⟩ := hR₁ a
      exact ⟨w, Prod.ext hw₁ hw₂⟩
  let e₀ : WeilQuotients.Abelianization φ ≃* F.Carrierˣ :=
    ((MonoidHom.ofInjective hJWinj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hJFinj).symm
  have he₀ : ∀ w, JF (e₀ w) = JW w := by
    intro w
    have h := MonoidHom.ofInjective_apply hJFinj (x := e₀ w)
    rw [show MonoidHom.ofInjective hJFinj (e₀ w) =
      MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hJWinj w) from
        MulEquiv.apply_symm_apply _ _] at h
    rw [← h]
    exact MonoidHom.ofInjective_apply hJWinj
  have he₀' : ∀ a, JW (e₀.symm a) = JF a := by
    intro a
    rw [← he₀, MulEquiv.apply_symm_apply]
  have hord := orderHom_continuous_isCompact_ker F T
  have hJF : Topology.IsInducing JF :=
    isInducing_prod_of_isCompact_ker r.toMonoidHom r.continuous hinj T.orderHom hord.1 hord.2
  have hJW : Topology.IsInducing JW :=
    isInducing_prod_of_isCompact_ker ι.toMonoidHom ι.continuous
      (WeilReciprocityUniqueness.toGroupAbelianization_injective F) δ.toMonoidHom δ.continuous
      (weilDegree_isCompact_ker F)
  have hJWc : Continuous JW := by
    rw [MonoidHom.coe_prod]
    exact ι.continuous.prodMk δ.continuous
  have hJFc : Continuous JF := by
    rw [MonoidHom.coe_prod]
    exact r.continuous.prodMk hord.1
  have hc : Continuous e₀ := by
    rw [hJF.continuous_iff, show JF ∘ e₀ = JW from funext he₀]
    exact hJWc
  have hcs : Continuous e₀.symm := by
    rw [hJW.continuous_iff, show JW ∘ e₀.symm = JF from funext he₀']
    exact hJFc
  let e : WeilReciprocityCandidate T φ :=
    { e₀ with continuous_toFun := hc, continuous_invFun := hcs }
  refine ⟨e, ?_, ?_⟩
  · ext w
    exact congrArg Prod.snd (he₀ w)
  · ext a
    exact congrArg Prod.fst (he₀' a)

/-- Existence and uniqueness of geometric local Weil reciprocity follow once,
for every geometric profinite reciprocity map, the pairing of the map with the
normalized order and the pairing of the Weil-to-Galois map with the Weil degree
have the same image. -/
theorem weilReciprocityExistenceUniqueness_of_range
    (hR : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
      letI := T.topology
      ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
        GeometricProfiniteReciprocityRelation F T r →
          (∀ a : F.Carrierˣ, ∃ w : WeilQuotients.Abelianization (localResidueDegree F),
            WeilQuotients.toGroupAbelianization (localResidueDegree F) w = r a ∧
              WeilQuotients.degree (localResidueDegree F) w = T.orderHom a) ∧
          ∀ w : WeilQuotients.Abelianization (localResidueDegree F), ∃ a : F.Carrierˣ,
            r a = WeilQuotients.toGroupAbelianization (localResidueDegree F) w ∧
              T.orderHom a = WeilQuotients.degree (localResidueDegree F) w) :
    WeilReciprocityExistenceUniqueness.{u} := by
  intro p _ F T
  let := T.topology
  obtain ⟨r, hr, -⟩ := profiniteReciprocityExistenceUniqueness p F T
  have hinj := (profiniteReciprocityCompletion p F T r hr).1
  obtain ⟨hR₁, hR₂⟩ := hR p F T r hr
  obtain ⟨e, horder, hcand⟩ := exists_candidate_of_range F T r hinj hR₁ hR₂
  have he : GeometricWeilReciprocityRelation F T e := ⟨horder, hcand ▸ hr⟩
  exact ⟨e, he, fun e' he' => geometricWeilReciprocityUniqueness p F T e' e he' he⟩

end Assembly

end WeilReciprocityExistence

end Langlands.LocalClassField
