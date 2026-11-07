import Langlands.Representation.Finite.DegreeZeroBrauerProof

/-!
# Degree-zero Brauer induction relative to a normal subgroup

For a finite group `G` and a normal subgroup `N`, a degree-zero virtual representation
spanned by actual representations on which `N` acts trivially is an integral
combination of inductions `Ind_H (χ - 1)`. Here `H` contains `N` and the rank-one
character `χ` is trivial on `N`.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped Classical

namespace Langlands.FiniteRep

universe uG

/-- Actual inductions `Ind_S (χ - 1)` from subgroups `S ⊇ N`, for rank-one characters
`χ` of `S` trivial on `N`. -/
def relativeDegreeZeroGenerators (G : Type uG) [Group G] [Fintype G] (N : Subgroup G) :
    Set (VirtualRep ℂ G) :=
  {x | ∃ (S : Subgroup G) (hNS : N ≤ S) (χ : S →* ℂˣ),
    (∀ n : N, χ (Subgroup.inclusion hNS n) = 1) ∧
    x = virtualInduce S (ofClass (classOf (oneDimensional χ)) -
      ofClass (classOf (oneDimensional (1 : S →* ℂˣ))))}

/-- The integral span of those inductions in the split representation group. -/
def relativeDegreeZeroSpan (G : Type uG) [Group G] [Fintype G] (N : Subgroup G) :
    Submodule ℤ (VirtualRep ℂ G) :=
  Submodule.span ℤ (relativeDegreeZeroGenerators G N)

/-- The integral span of the classes of actual representations on which `N` acts
trivially. -/
def trivialOnSpan (G : Type uG) [Group G] (N : Subgroup G) : Submodule ℤ (VirtualRep ℂ G) :=
  Submodule.span ℤ {x | ∃ V : FDRep ℂ G, (∀ n ∈ N, V.ρ n = 1) ∧ x = ofClass (classOf V)}

/-- Degree-zero Brauer induction relative to a normal subgroup `N`: a degree-zero
virtual representation spanned by representations trivial on `N` lies in the span of
the inductions `Ind_S (χ - 1)` with `N ≤ S` and `χ` trivial on `N`. -/
def RelativeDegreeZeroBrauerStatement (G : Type uG) [Group G] [Fintype G] : Prop :=
  ∀ N : Subgroup G, N.Normal → ∀ x ∈ trivialOnSpan G N,
    x ∈ degreeZeroVirtualReps G → x ∈ relativeDegreeZeroSpan G N

namespace RelativeDegreeZeroBrauer

open DegreeZeroBrauer

variable {G : Type uG} [Group G] [Fintype G] (N : Subgroup G)

/-- The character image of the relative span. -/
def relCharSpan : Submodule ℤ (G → ℂ) :=
  (relativeDegreeZeroSpan G N).map (virtualCharacter (k := ℂ) (G := G))

theorem ind_sub_one_mem (S : Subgroup G) (hNS : N ≤ S) (χ : S →* ℂˣ)
    (hχ : ∀ n : N, χ (Subgroup.inclusion hNS n) = 1) :
    ind S ((fun s => (χ s : ℂ)) - fun _ => 1) ∈ relCharSpan N := by
  refine ⟨virtualInduce S (ofClass (classOf (oneDimensional χ)) -
    ofClass (classOf (oneDimensional (1 : S →* ℂˣ)))),
    Submodule.subset_span ⟨S, hNS, χ, hχ, rfl⟩, ?_⟩
  rw [virtualCharacter_induce]
  congr 1
  simp only [map_sub, virtualCharacter_ofClass, character_classOf]
  ext s
  simp [character_oneDimensional]

theorem ind_sub_mem (S : Subgroup G) (hNS : N ≤ S) (χ χ' : S →* ℂˣ)
    (hχ : ∀ n : N, χ (Subgroup.inclusion hNS n) = 1)
    (hχ' : ∀ n : N, χ' (Subgroup.inclusion hNS n) = 1) :
    ind S ((fun s => (χ s : ℂ)) - fun s => (χ' s : ℂ)) ∈ relCharSpan N := by
  have he : ((fun s => (χ s : ℂ)) - fun s => (χ' s : ℂ)) =
      ((fun s => (χ s : ℂ)) - fun _ => 1) - ((fun s => (χ' s : ℂ)) - fun _ => 1) := by
    funext s
    simp
  rw [he, map_sub]
  exact Submodule.sub_mem _ (ind_sub_one_mem N S hNS χ hχ) (ind_sub_one_mem N S hNS χ' hχ')

variable [N.Normal]

/-- Inflation from `G ⧸ N` carries the degree-zero character image into the relative one. -/
theorem pullback_mem_rel {f : (G ⧸ N) → ℂ} (hf : f ∈ characterSpan (G ⧸ N)) :
    pullback (QuotientGroup.mk' N) f ∈ relCharSpan N := by
  obtain ⟨x, hx, rfl⟩ := hf
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, χ, χ', rfl⟩ := hy
    rw [virtualCharacter_induce]
    simp only [map_sub, virtualCharacter_ofClass, character_classOf]
    rw [show (oneDimensional χ).character = (fun t => (χ t : ℂ)) from
      funext (character_oneDimensional χ),
      show (oneDimensional χ').character = (fun t => (χ' t : ℂ)) from
      funext (character_oneDimensional χ')]
    rw [← map_sub, ← map_sub]
    change (ind S ((fun t => (χ t : ℂ)) - (fun t => (χ' t : ℂ)))) ∘ (QuotientGroup.mk' N) ∈
      relCharSpan N
    rw [← ind_comap (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)]
    have hNS : N ≤ S.comap (QuotientGroup.mk' N) := fun n hn => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact S.one_mem
    have h1 : ∀ n : N,
        (QuotientGroup.mk' N).subgroupComap S (Subgroup.inclusion hNS n) = 1 := fun n =>
      Subtype.ext (by exact (QuotientGroup.eq_one_iff (n : G)).mpr n.2)
    exact ind_sub_mem N _ hNS (χ.comp ((QuotientGroup.mk' N).subgroupComap S))
      (χ'.comp ((QuotientGroup.mk' N).subgroupComap S))
      (fun n => by rw [MonoidHom.comp_apply, h1 n, map_one])
      (fun n => by rw [MonoidHom.comp_apply, h1 n, map_one])
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    simpa only [map_zsmul] using Submodule.smul_mem _ a ih

omit [Fintype G] in
/-- A representation trivial on `N` descends to `G ⧸ N` with the same character. -/
theorem exists_descent (V : FDRep ℂ G) (hV : ∀ n ∈ N, V.ρ n = 1) :
    ∃ W : FDRep ℂ (G ⧸ N), ∀ g : G, W.character (g : G ⧸ N) = V.character g :=
  ⟨FDRep.of (QuotientGroup.lift N V.ρ (fun n hn => MonoidHom.mem_ker.mpr (hV n hn))),
    fun _ => rfl⟩

omit [Fintype G] in
/-- Every element of the trivial-on-`N` span has the character of an inflation. -/
theorem exists_pullback {x : VirtualRep ℂ G} (hx : x ∈ trivialOnSpan G N) :
    ∃ y : VirtualRep ℂ (G ⧸ N), virtualCharacter (k := ℂ) x =
      pullback (QuotientGroup.mk' N) (virtualCharacter (k := ℂ) y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨V, hV, rfl⟩ := hx
    obtain ⟨W, hW⟩ := exists_descent N V hV
    refine ⟨ofClass (classOf W), ?_⟩
    rw [virtualCharacter_ofClass, virtualCharacter_ofClass, character_classOf,
      character_classOf]
    funext g
    exact (hW g).symm
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨n • a, by rw [map_zsmul, map_zsmul, map_zsmul, ha]⟩

end RelativeDegreeZeroBrauer

open RelativeDegreeZeroBrauer DegreeZeroBrauer in
/-- Degree-zero Brauer induction relative to a normal subgroup. -/
theorem relativeDegreeZeroBrauer (G : Type uG) [Group G] [Fintype G] :
    RelativeDegreeZeroBrauerStatement G := by
  intro N hN x hx hx0
  have : N.Normal := hN
  obtain ⟨y, hy⟩ := exists_pullback N hx
  have hy0 : y ∈ degreeZeroVirtualReps (G ⧸ N) := by
    have h1 : virtualCharacter (k := ℂ) x 1 = 0 := hx0
    rw [hy] at h1
    change virtualCharacter (k := ℂ) y 1 = 0
    simpa [pullback] using h1
  rw [← finiteDegreeZeroBrauer (G ⧸ N)] at hy0
  have hmem : virtualCharacter (k := ℂ) x ∈ relCharSpan N := by
    rw [hy]
    exact pullback_mem_rel N ⟨y, hy0, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hmem
  rw [← VirtualCharacter.faithfulness hzx]
  exact hz

end Langlands.FiniteRep
