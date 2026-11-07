import Langlands.VirtualRepresentation.CliffordReduction
import Langlands.VirtualRepresentation.ScalarKernelBrauer
import Langlands.VirtualRepresentation.ExactInductionTransitivity

/-!
# Brauer induction for groups with a commutative open kernel of finite index

Let `π : G →* Q` be a homomorphism from a topological group to a finite group
whose kernel is open and commutative. Then the continuous exact virtual group of
`G` is spanned over `ℤ` by the classes `Ind_{π⁻¹ H}^G θ`, for subgroups `H` of
`Q` and continuous characters `θ` of `π⁻¹ H`.

The proof is by strong induction on dimension. A common eigenvector of the
kernel gives the Clifford decomposition `[A] = [Ind_S^G W] + [A / Ind_S^G W]`,
where the kernel acts on `W` by scalars. The scalar case is
`ScalarKernel.ofRepresentation_mem_span_of_scalar`, and transitivity of
induction carries its generators to generators of `G`.
-/

noncomputable section

universe uG uQ uV

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G]

/-- A submodule containing all genuine classes is everything. -/
theorem mem_of_forall_ofRepresentation_mem {K : Type*} [Field K]
    (P : FiniteRepresentation.{_, uG, uV} K G → Prop)
    (M : Submodule ℤ (ExactGrothendieckGroup P)) (h : ∀ A, ofRepresentation P A ∈ M)
    (x : ExactGrothendieckGroup P) : x ∈ M := by
  obtain ⟨v, rfl⟩ := (exactRelations P).mkQ_surjective x
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using M.zero_mem
  | add v w hv hw =>
    rw [map_add]
    exact M.add_mem hv hw
  | single c n =>
    have hc : Finsupp.single c n = n • generator c := by simp [generator]
    rw [hc, map_smul]
    refine M.smul_mem n ?_
    induction c using Quotient.inductionOn with
    | h A => exact h A

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inverse of `subgroupOfContinuousHom`. -/
def subgroupOfContinuousInv {S T : Subgroup G} (hTS : T ≤ S) : T →ₜ* T.subgroupOf S where
  toFun t := ⟨⟨t, hTS t.2⟩, t.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

variable {Q : Type uQ} [Group Q] [Finite Q]

/-- Induction from a subgroup `S` containing the kernel carries generators of
`S` (for `π` restricted to `S`) into generators of `G`. -/
theorem continuousInduce_mem_quotientInducedGenerators (π : G →* Q)
    (hπ : IsOpen (π.ker : Set G)) (S : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hNS : π.ker ≤ S) (hπS : IsOpen ((π.comp S.subtype).ker : Set S)) {y}
    (hy : y ∈ quotientInducedGenerators.{uG, uQ, uV} (π.comp S.subtype) hπS) :
    continuousInduce S hS y ∈ quotientInducedGenerators.{uG, uQ, uV} π hπ := by
  obtain ⟨H, θ, rfl⟩ := hy
  let H' : Subgroup S := H.comap (π.comp S.subtype)
  let T : Subgroup G := H'.map S.subtype
  have hTS : T ≤ S := Subgroup.map_subtype_le H'
  have hker : π.ker ≤ T := by
    intro g hg
    refine ⟨⟨g, hNS hg⟩, ?_, rfl⟩
    change π g ∈ H
    rw [(MonoidHom.mem_ker).mp hg]
    exact H.one_mem
  have : T.FiniteIndex := Subgroup.finiteIndex_of_le hker
  have hTo : IsOpen (T : Set G) := Subgroup.isOpen_mono hker hπ
  have hsub : T.subgroupOf S = H' :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective H'
  obtain ⟨θ₁, hθ₁⟩ := continuousInduce_characterClass_congr.{uG, max uG uV} hsub.symm
    (isOpen_comap_of_isOpen_ker (π.comp S.subtype) hπS H) (isOpen_subgroupOf hTo) θ
  let θ₂ : T →ₜ* ℂˣ := θ₁.comp (subgroupOfContinuousInv hTS)
  have hθ : θ₁ = θ₂.comp (subgroupOfContinuousHom hTS) := by
    ext x
    rfl
  change continuousInduce S hS (continuousInduce H' _ (characterClass θ)) ∈ _
  rw [hθ₁, hθ, continuousInduce_continuousInduce_characterClass S T hS hTo hTS θ₂]
  exact mem_quotientInducedGenerators_of_ker_le π hπ hker hTo θ₂

/-- The class of every continuous representation lies in the span, by strong
induction on dimension. -/
theorem ofRepresentation_mem_span_quotientInducedGenerators (π : G →* Q)
    (hπ : IsOpen (π.ker : Set G)) (hcomm : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a)
    (n : ℕ) (A : FiniteRepresentation.{0, uG, max uG uV} ℂ G) (hA : A.IsContinuous)
    (hn : A.rank = n) :
    ofRepresentation _ ⟨A, hA⟩ ∈
      Submodule.span ℤ (quotientInducedGenerators.{uG, uQ, uV} π hπ) := by
  induction n using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  rcases subsingleton_or_nontrivial A with hs | hnt
  · rw [ofRepresentation_eq_zero_of_rank_eq_zero _ _ Module.finrank_zero_of_subsingleton]
    exact Submodule.zero_mem _
  let N := π.ker
  let ρ := A.representation
  have hc : ∀ a b : N, Commute (ρ a) (ρ b) := by
    intro a b
    change ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul, hcomm a a.2 b b.2]
  obtain ⟨v, hv0, hv⟩ := LieKolchin.exists_common_eigenvector (fun a : N => ρ a) hc
  choose χ hχ using hv
  let S := Clifford.weightStabilizer N χ
  have hNS : N ≤ S := Clifford.le_weightStabilizer N hcomm χ
  have : S.FiniteIndex := Subgroup.finiteIndex_of_le hNS
  have hSo : IsOpen (S : Set G) := Subgroup.isOpen_mono hNS hπ
  have hvW : v ∈ Clifford.weightSpace N ρ χ := (Clifford.mem_weightSpace N ρ).mpr hχ
  let B : FiniteRepresentation.{0, uG, max uG uV} ℂ S :=
    FiniteRepresentation.of (Clifford.weightRep N ρ χ)
  have hB : B.IsContinuous := by
    let i : B.representation.IntertwiningMap
        (FiniteRepresentation.restrict S.subtype A).representation :=
      ⟨(Clifford.weightSpace N ρ χ).subtype, fun _ => rfl⟩
    exact isContinuous_of_injective_intertwiner i (Submodule.injective_subtype _)
      (isContinuous_restrict S.subtype continuous_subtype_val hA)
  have : Nontrivial B :=
    nontrivial_of_ne (⟨v, hvW⟩ : Clifford.weightSpace N ρ χ) 0
      (fun h => hv0 (congrArg Subtype.val h))
  have hBpos : 0 < B.rank := Module.finrank_pos
  -- the Clifford exact sequence
  let Ψ : (FiniteRepresentation.induce S B).representation.IntertwiningMap A.representation :=
    Clifford.cliffordMap N ρ χ
  let U : Subrepresentation A.representation :=
    { toSubmodule := LinearMap.range Ψ.toLinearMap
      apply_mem_toSubmodule := by
        rintro g _ ⟨x, rfl⟩
        exact ⟨(FiniteRepresentation.induce S B).representation g x,
          LinearMap.congr_fun (Ψ.isIntertwining' g) x⟩ }
  let C : FiniteRepresentation.{0, uG, max uG uV} ℂ G :=
    FiniteRepresentation.of (A.representation.quotient U.toSubmodule
      (fun g _ hv => U.apply_mem_toSubmodule g hv))
  have hC : C.IsContinuous := isContinuous_quotient hA U
  let q : A.representation.IntertwiningMap C.representation :=
    { toLinearMap := U.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  have hses : IsShortExact Ψ q :=
    ⟨Clifford.cliffordMap_injective N ρ χ, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).symm⟩
  have hIc : (FiniteRepresentation.induce S B).IsContinuous := isContinuous_induce S hSo hB
  have hcls : ofRepresentation _ ⟨A, hA⟩ =
      ofRepresentation _ ⟨FiniteRepresentation.induce S B, hIc⟩ + ofRepresentation _ ⟨C, hC⟩ :=
    ofRepresentation_shortExact _ (A := ⟨FiniteRepresentation.induce S B, hIc⟩)
      (B := ⟨A, hA⟩) (C := ⟨C, hC⟩) hses
  have hrk := rank_eq_add_of_shortExact hses
  have hind : 0 < (FiniteRepresentation.induce S B).rank := by
    rw [rank_induce]
    exact Nat.mul_pos (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hBpos
  have hCr : C.rank < n := by omega
  rw [hcls]
  refine Submodule.add_mem _ ?_ (ih C.rank hCr C hC rfl)
  -- the scalar case for `S`, then induction to `G`
  have hπS : IsOpen ((π.comp S.subtype).ker : Set S) := hπ.preimage continuous_subtype_val
  have hscalar : ∀ s ∈ (π.comp S.subtype).ker, ∃ c : ℂ, B.representation s = c • 1 := by
    intro s hs
    exact ⟨χ ⟨s, hs⟩, Clifford.weightRep_scalar N ρ χ s hs⟩
  have hBmem : ofRepresentation _ ⟨B, hB⟩ ∈ Submodule.span ℤ
      (quotientInducedGenerators.{uG, uQ, uV} (π.comp S.subtype) hπS) :=
    ScalarKernel.ofRepresentation_mem_span_of_scalar (π.comp S.subtype) hπS B hB hscalar
  have hIeq : ofRepresentation _ ⟨FiniteRepresentation.induce S B, hIc⟩ =
      continuousInduce S hSo (ofRepresentation _ ⟨B, hB⟩) :=
    (induce_ofRepresentation S _ _ (fun _ hA => isContinuous_induce S hSo hA) ⟨B, hB⟩).symm
  rw [hIeq]
  have hle : Submodule.span ℤ (quotientInducedGenerators.{uG, uQ, uV} (π.comp S.subtype) hπS) ≤
      (Submodule.span ℤ (quotientInducedGenerators.{uG, uQ, uV} π hπ)).comap
        (continuousInduce S hSo) := by
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.subset_span
      (continuousInduce_mem_quotientInducedGenerators π hπ S hSo hNS hπS hy)
  exact hle hBmem

/-- **Brauer induction for a group with a commutative open kernel of finite
index.** The classes `Ind_{π⁻¹ H}^G θ` span the continuous exact virtual group. -/
theorem span_quotientInducedGenerators_eq_top (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    (hcomm : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a) :
    Submodule.span ℤ (quotientInducedGenerators.{uG, uQ, uV} π hπ) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact mem_of_forall_ofRepresentation_mem _ _
    (fun A => ofRepresentation_mem_span_quotientInducedGenerators π hπ hcomm _ A.1 A.2 rfl) x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
