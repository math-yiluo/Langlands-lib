import Langlands.Representation.Plancherel.ParabolicPointUniformNumerator
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightIntegrability
import Langlands.Analysis.Local.QuotientFactorizationHaar

/-! # The opposite chart of the standard intertwining quotient and height integrability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal ENNReal CategoryTheory.MonObj

namespace Langlands.QuotientIntegration

section Integrability

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [LocallyCompactSpace Γ]
  (H K : Subgroup Γ) (m : H × K ≃ₜ Γ) (hm : ∀ p : H × K, m p = p.1.val * p.2.val)
  [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- **Integrability through the complementary chart.** Let `ν` be a regular right-invariant
measure on the actual quotient `H \ Γ` and `μK` a regular left Haar measure on the complement
`K`. A `μK`-integrable function on `K` invariant under inversion, read through the inverse chart
`H \ Γ ≃ₜ K`, is `ν`-integrable. No unimodularity of `K` is used. -/
theorem integrable_comp_factorQuotientHomeomorph_symm
    (ν : Measure (LeftQuotient H)) [ν.Regular]
    (hinv : ∀ g : Γ, MeasurePreserving (rightTranslate H g) ν ν)
    (μK : Measure K) [IsHaarMeasure μK] [μK.Regular]
    {E : Type*} [NormedAddCommGroup E] {f : K → E} (hf : Integrable f μK)
    (hfinv : ∀ k, f k⁻¹ = f k) :
    Integrable (fun q => f ((factorQuotientHomeomorph H Subtype.val m hm).symm q)) ν := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  let : LocallyCompactSpace (LeftQuotient H) := leftQuotient_locallyCompactSpace H
  let : LocallyCompactSpace K := c.isClosedEmbedding.locallyCompactSpace
  let Mν := Measure.map c.symm ν
  have : Mν.Regular := Measure.Regular.map c.symm
  have : Mν.IsMulRightInvariant :=
    isMulRightInvariant_map_factorQuotientHomeomorph_symm H K m hm ν hinv
  have hi : Mν.inv = haarScalarFactor Mν.inv μK • μK :=
    isMulLeftInvariant_eq_smul_of_regular Mν.inv μK
  have hM : Mν = haarScalarFactor Mν.inv μK • μK.inv := by
    calc
      Mν = Mν.inv.inv := (Measure.inv_inv Mν).symm
      _ = (haarScalarFactor Mν.inv μK • μK).inv := congrArg Measure.inv hi
      _ = _ := by
        rw [Measure.inv_def, Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def]
  have hfi : Integrable f μK.inv := by
    rw [Measure.inv_def]
    refine (integrable_map_equiv (MeasurableEquiv.inv K) f).2 ?_
    have : f ∘ (MeasurableEquiv.inv K) = f := funext fun k => hfinv k
    rw [this]
    exact hf
  have hfM : Integrable f Mν := by
    rw [hM]
    exact hfi.smul_measure_nnreal
  exact (integrable_map_equiv c.symm.toMeasurableEquiv f).1 hfM

end Integrability

end Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

section SubgroupOfInf

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- The subgroup `A.subgroupOf B` of `B` is identified with `A ⊓ B` as a topological group;
both carry the subspace topology of `Γ`. -/
def subgroupOfInfEquiv (A B : Subgroup Γ) : A.subgroupOf B ≃ₜ* (A ⊓ B : Subgroup Γ) where
  toFun x := ⟨((x : B) : Γ), Subgroup.mem_inf.mpr ⟨x.2, (x : B).2⟩⟩
  invFun y := ⟨⟨(y : Γ), (Subgroup.mem_inf.mp y.2).2⟩, (Subgroup.mem_inf.mp y.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem coe_subgroupOfInfEquiv (A B : Subgroup Γ) (x : A.subgroupOf B) :
    ((subgroupOfInfEquiv A B x : (A ⊓ B : Subgroup Γ)) : Γ) = ((x : B) : Γ) := rfl

omit [TopologicalSpace Γ] in
/-- An element normalizing two subgroups normalizes their intersection. -/
theorem mem_normalizer_inf {A B : Subgroup Γ} {g : Γ}
    (hA : g ∈ Subgroup.normalizer (A : Set Γ)) (hB : g ∈ Subgroup.normalizer (B : Set Γ)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hA x) (hB x)

end SubgroupOfInf

namespace IsOpenCellContraction

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {P V U U' M : Subgroup Γ} {a b : Γ}

/-- The chart `V ∩ U' ≃ₜ (U ∩ U') \ U'`, `k ↦ (U ∩ U') k`, given by the product
decomposition. -/
def quotientChart (hc : IsOpenCellContraction P V U U' M a b) :
    V.subgroupOf U' ≃ₜ Induction.LeftQuotient (U.subgroupOf U') :=
  QuotientIntegration.factorQuotientHomeomorph (U.subgroupOf U') Subtype.val
    hc.productHomeomorph (fun _ => rfl)

theorem quotientChart_apply (hc : IsOpenCellContraction P V U U' M a b) (k : V.subgroupOf U') :
    hc.quotientChart k = Quotient.mk _ (k : U') := rfl

end IsOpenCellContraction

end Langlands.HarishChandraSchwartz

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation
open Aubert.General Induction StandardIntertwining

section Host

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' U U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {p' : P' ⟶ G} {l' : M ⟶ P'} (r' : ParabolicRootPresentation p' l' a)
  (hLevi : l ≫ p = l' ≫ p')
  {n : U ⟶ P} {n' : U' ⟶ P'} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')

local instance oppositeQuotientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance oppositeQuotientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance oppositeQuotientTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable {Ppt Upt P'pt U'pt : Subgroup (rationalPoints G)}
  (hPpt : Ppt = (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
  (hU'pt : U'pt = (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
include hLevi in
/-- Every value of the split-component cocharacter of `P'` lies in the Levi points of `P`. -/
theorem splitComponentCocharacter_point_mem_parabolicLevi (t : Fˣ) :
    gmRationalPoint t ≫
        (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a ≫ l' ≫ p').hom.hom ∈
      parabolicLeviPointSubgroup p l := by
  refine SubgroupFunctor.mem_range.mpr
    ⟨gmRationalPoint t ≫ (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a).hom.hom, ?_⟩
  rw [hLevi]
  simp only [Grp.comp_hom_hom, Category.assoc]

include r r' hLevi hn hn' hPpt hUpt hU'pt in
/-- **Open-cell contraction data for two parabolics with a common Levi.** For the actual
points `P(F)`, `U(F)`, `U'(F)` of two parabolics with a common Levi `M(F)`, the opposite radical
points `Ū(F)` of `P`, and `t ∈ Fˣ` with `t ^ n → 0`, the elements `λ_{P'}(t)` and `λ_P(t)` of
the split-component cocharacters satisfy `IsOpenCellContraction`. -/
theorem parabolic_isOpenCellContraction
    (h' : IsSemidirectDecomposition P'pt (parabolicLeviPointSubgroup p l) U'pt)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) :
    HarishChandraSchwartz.IsOpenCellContraction Ppt (parabolicOppositeRadicalPoints r) Upt U'pt
      (parabolicLeviPointSubgroup p l)
      (gmRationalPoint t ≫
        (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a ≫ l' ≫ p').hom.hom)
      (gmRationalPoint t ≫
        (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p).hom.hom) := by
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  set ξ := CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a ≫ l' ≫ p' with hξdef
  have hP : Ppt = (Dynamic.parabolic χ).rationalPoints := by
    rw [hPpt, r.parabolic_eq_splitComponentCocharacter]
  have hU : Upt = (Dynamic.unipotent χ).rationalPoints := by
    rw [hUpt, r.range_comp_radical_eq hn]
  have hU' : U'pt = (Dynamic.unipotent ξ).rationalPoints := by
    rw [hU'pt, r'.range_comp_radical_eq hn']
  have hM : parabolicLeviPointSubgroup p l = (Dynamic.centralizer χ).rationalPoints := by
    change (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) = _
    rw [r.levi_eq_splitComponentCocharacter]
  have hξ : gmRationalPoint t ≫ ξ.hom.hom ∈ (Dynamic.centralizer χ).rationalPoints := by
    rw [← hM]
    exact splitComponentCocharacter_point_mem_parabolicLevi r' hLevi t
  have hZU : ∀ m ∈ (Dynamic.centralizer χ).rationalPoints,
      m ∈ (Dynamic.unipotent ξ).rationalPoints → m = 1 := by
    intro m hm hmU
    rw [← hM] at hm
    rw [← hU'] at hmU
    have h1 := h'.projection_levi ⟨m, hm⟩
    have h2 := h'.projection_unipotent ⟨m, hmU⟩
    have h3 : (⟨m, h'.levi_le hm⟩ : P'pt) = ⟨m, h'.unipotent_le hmU⟩ := rfl
    rw [h3, h2] at h1
    exact congrArg Subtype.val h1.symm
  have key := isOpenCellContraction_dynamic F χ ξ t ht hξ hZU
  rw [hP, hU, hU', hM]
  exact key

include r r' hLevi hn hn' hPpt hUpt hU'pt in
/-- **Height integrability on the standard intertwining quotient.** Let `ρ₀` be a closed
representation of `G` and `qν` a regular right-invariant measure on the actual quotient
`(U ∩ U') \ U'`. Read each quotient point through the opposite chart
`(Ū ∩ U') ≃ₜ (U ∩ U') \ U'`. Then for some `D` and every real `s > D` the function
`q ↦ ‖c⁻¹(q)‖_ρ₀ ^ (-s)` is `qν`-integrable. -/
theorem exists_integrable_quotientChart_symm_rationalMatrixNorm
    (h' : IsSemidirectDecomposition P'pt (parabolicLeviPointSubgroup p l) U'pt)
    (hU' : IsClosed (U'pt : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
    [BorelSpace (QuotientSpace (U := Upt) U'pt)]
    (qν : Measure (QuotientSpace (U := Upt) U'pt)) [qν.Regular]
    (hinv : ∀ g : U'pt,
      MeasurePreserving (QuotientIntegration.rightTranslate (Upt.subgroupOf U'pt) g) qν qν) :
    ∃ D : ℕ, ∀ s : ℝ, (D : ℝ) < s →
      Integrable (fun q => rationalMatrixNorm F ρ₀
        (((parabolic_isOpenCellContraction r r' hLevi hn hn' hPpt hUpt hU'pt h' t
          ht).quotientChart.symm q : U'pt) : rationalPoints G) ^ (-s)) qν := by
  set hc := parabolic_isOpenCellContraction r r' hLevi hn hn' hPpt hUpt hU'pt h' t ht
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : LocallyCompactSpace U'pt := hU'.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  -- The opposite factor `K = Ū ∩ U'`, inside `U'` and inside `G(F)`.
  let K := (parabolicOppositeRadicalPoints r).subgroupOf U'pt
  let H₀ : Subgroup (rationalPoints G) := parabolicOppositeRadicalPoints r ⊓ U'pt
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace H₀ := borel H₀
  have : BorelSpace H₀ := ⟨rfl⟩
  have hŪc : IsClosed ((parabolicOppositeRadicalPoints r : Subgroup (rationalPoints G)) :
      Set (rationalPoints G)) :=
    BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)
  have hH₀c : IsClosed (H₀ : Set (rationalPoints G)) := hŪc.inter hU'
  have : LocallyCompactSpace H₀ := hH₀c.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let e := HarishChandraSchwartz.subgroupOfInfEquiv (parabolicOppositeRadicalPoints r) U'pt
  have : LocallyCompactSpace K := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let μK : Measure K := Measure.haar
  let ν₀ : Measure H₀ := Measure.map e μK
  have : ν₀.Regular := Measure.Regular.map e.toHomeomorph
  -- Normalization of `H₀` by the values of `χ`.
  have hH₀U : H₀ ≤ (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints := fun x hx => hx.1
  have hH₀a : ∀ s : Fˣ, gmRationalPoint s ≫ χ.hom.hom ∈
      Subgroup.normalizer (H₀ : Set (rationalPoints G)) := by
    intro s
    have hm : gmRationalPoint s ≫ χ.hom.hom ∈ parabolicLeviPointSubgroup p l :=
      splitComponentCocharacter_point_mem_parabolicLevi r rfl s
    exact HarishChandraSchwartz.mem_normalizer_inf
      (parabolicLevi_le_normalizer_oppositeRadicalPoints r hm) (h'.levi_le_normalizer hm)
  obtain ⟨D, hD⟩ :=
    exists_integrable_rationalMatrixNorm_rpow_neg F χ ρ₀ hρ₀ H₀ hH₀c hH₀U hH₀a ν₀
  refine ⟨D, fun s hs => ?_⟩
  have hK : Integrable (fun k : K => rationalMatrixNorm F ρ₀ ((k : U'pt) : rationalPoints G) ^ (-s))
      μK := by
    have h := (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv
      (fun x : H₀ => rationalMatrixNorm F ρ₀ x ^ (-s))).1 (hD s hs)
    exact h
  have hinvK : ∀ k : K, rationalMatrixNorm F ρ₀ (((k⁻¹ : K) : U'pt) : rationalPoints G) ^ (-s) =
      rationalMatrixNorm F ρ₀ ((k : U'pt) : rationalPoints G) ^ (-s) := by
    intro k
    simp only [InvMemClass.coe_inv, rationalMatrixNorm_inv]
  exact QuotientIntegration.integrable_comp_factorQuotientHomeomorph_symm
    (Upt.subgroupOf U'pt) K hc.productHomeomorph (fun _ => rfl) qν hinv μK hK hinvK

end Host

end Langlands.Plancherel
