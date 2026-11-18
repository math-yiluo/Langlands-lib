import Langlands.Representation.Plancherel.DynamicCommonLeviComposition

/-! # Ordered charts for distance-additive dynamic radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open BruhatTits.DynamicUnipotentContainment DynamicOppositeStandardIntertwining
open StandardIntertwining

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace

local notation "Γ" => RationalPoint F G.X

/-- Split the second radical into its intersections with the first radical
and the first opposite radical, using the common centralizer. -/
def commonLeviRadicalChart (ψ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hZ : Dynamic.centralizer ψ = Dynamic.centralizer ξ) :
    (radical ψ).subgroupOf (radical ξ) × (radical ξ ⊓ oppositeRadical ψ : Subgroup Γ) ≃ₜ
      radical ξ :=
  ((Homeomorph.refl _).prodCongr
    (subgroupOfHomeomorphOfMem (oppositeRadical ψ) (radical ξ)
      (radical ξ ⊓ oppositeRadical ψ) (fun _ => Subgroup.mem_inf.trans and_comm)).symm).trans
    (MatrixRepresentation.unipotentIntersectionProduct F ψ ξ
      OppositeCharts.contractingUnit OppositeCharts.contractingUnit_tendsto
      (OppositeCharts.cocharPoint_mem_centralizer_left (by rw [hZ]) _)
      (fun _ hm hu =>
        OppositeCharts.eq_one_of_mem_centralizer_left_of_mem_radical (by rw [hZ]) hm hu))

theorem commonLeviRadicalChart_apply (ψ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hZ : Dynamic.centralizer ψ = Dynamic.centralizer ξ)
    (p : (radical ψ).subgroupOf (radical ξ) × (radical ξ ⊓ oppositeRadical ψ : Subgroup Γ)) :
    (commonLeviRadicalChart ψ ξ hZ p : Γ) = p.1.val.val * p.2.val :=
  rfl

/-- In a distance-additive triple, the part of the middle radical in the
first opposite radical also belongs to the final radical. -/
theorem firstComplement_le_target (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer ψ₀)
    (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer ψ₀)
    (hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂) :
    radical ψ₁ ⊓ oppositeRadical ψ₀ ≤ radical ψ₂ := by
  intro x hx
  let ξ := Dynamic.inverseCocharacter ψ₀
  have hξ₀ : Dynamic.centralizer ξ = Dynamic.centralizer ψ₀ :=
    Dynamic.centralizer_inverseCocharacter ψ₀
  let e := commonLeviRadicalChart ψ₂ ξ (h₂.trans hξ₀.symm)
  let p := e.symm (⟨x, hx.2⟩ : radical ξ)
  have hx_mul : x = p.1.val.val * p.2.val :=
    (congrArg (fun z : radical ξ => z.val) (e.apply_symm_apply ⟨x, hx.2⟩)).symm.trans
      (commonLeviRadicalChart_apply ψ₂ ξ _ p)
  let t : Fˣ := OppositeCharts.contractingUnit
  have ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0) :=
    OppositeCharts.contractingUnit_tendsto
  let a : Γ := MatrixRepresentation.gmRationalPoint t ≫ ψ₁.hom.hom
  let c (n : ℕ) : MulAut Γ := MulAut.conj (a ^ n)
  have hc_mem (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
      (hψ : Dynamic.centralizer ψ = Dynamic.centralizer ψ₀)
      (n : ℕ) {y : Γ} (hy : y ∈ radical ψ) : c n y ∈ radical ψ := by
    have ha : a ∈ levi ψ := by
      change MatrixRepresentation.gmRationalPoint t ≫ ψ₁.hom.hom ∈
        (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _))
      rw [hψ, ← h₁, ← MatrixRepresentation.cocharPoint_eq_gmRationalPoint_comp]
      exact cocharPoint_mem_centralizer ψ₁ t
    exact (Subgroup.mem_normalizer_iff.mp
      (Dynamic.centralizer_le_normalizer_unipotent ψ _ ((levi ψ).pow_mem ha n)) y).mp hy
  have hχ₂ : Dynamic.centralizer (Dynamic.inverseCocharacter ψ₂) =
      Dynamic.centralizer ψ₀ := centralizer_inverseCocharacter_eq ψ₀ ψ₂ h₂
  let xn (n : ℕ) : radical ξ := ⟨c n x, hc_mem ξ hξ₀ n hx.2⟩
  have hlim : Tendsto xn atTop (𝓝 1) := by
    apply tendsto_subtype_rng.mpr
    exact (MatrixRepresentation.mem_unipotent_iff_tendsto_conj F ψ₁ t ht x).mp hx.1
  have hproj (n : ℕ) : (e.symm (xn n)).2.val = c n p.2.val := by
    let pn : (radical ψ₂).subgroupOf (radical ξ) ×
        (radical ξ ⊓ oppositeRadical ψ₂ : Subgroup Γ) :=
      (⟨⟨c n p.1.val.val, hc_mem ξ hξ₀ n p.1.val.property⟩,
          Subgroup.mem_subgroupOf.mpr (hc_mem ψ₂ h₂ n (Subgroup.mem_subgroupOf.mp p.1.property))⟩,
        ⟨c n p.2.val, ⟨hc_mem ξ hξ₀ n p.2.property.1,
          hc_mem (Dynamic.inverseCocharacter ψ₂) hχ₂ n p.2.property.2⟩⟩)
    have he : e pn = xn n := by
      apply Subtype.ext
      rw [commonLeviRadicalChart_apply]
      change c n p.1.val.val * c n p.2.val = c n x
      rw [← map_mul, ← hx_mul]
    exact congrArg (fun q : (radical ψ₂).subgroupOf (radical ξ) ×
        (radical ξ ⊓ oppositeRadical ψ₂ : Subgroup Γ) => q.2.val)
      ((congrArg e.symm he).symm.trans (e.symm_apply_apply pn))
  have he_one : e (1, 1) = 1 := by
    apply Subtype.ext
    rw [commonLeviRadicalChart_apply]
    simp
  have hproj_one : (e.symm 1).2.val = 1 := by
    rw [← he_one, e.symm_apply_apply]
    rfl
  have hcont : Continuous (fun z : radical ξ => (e.symm z).2.val) :=
    continuous_subtype_val.comp e.symm.continuous.snd
  have hdlim := (hcont.tendsto 1).comp hlim
  simp only [Function.comp_def, hproj, hproj_one] at hdlim
  have hd_mem := (MatrixRepresentation.mem_unipotent_iff_tendsto_conj F ψ₁ t ht p.2.val).mpr
    hdlim
  have hd_op : p.2.val ∈ oppositeRadical ψ₁ := hd.2 p.2.property
  have hd_one := OppositeCharts.eq_one_of_mem_inverse_radical ψ₁ hd_op hd_mem
  rw [hx_mul, hd_one, mul_one]
  exact Subgroup.mem_subgroupOf.mp p.1.property

section Restriction

variable {H : Type*} [Group H] [TopologicalSpace H]
  {A B C V W : Subgroup H}

private def restrictFirstChart
    (hABC : A ⊓ C ≤ B) (hVC : V ≤ C)
    (e : A.subgroupOf B × V ≃ₜ B)
    (he : ∀ p : A.subgroupOf B × V, (e p : H) = p.1.val.val * p.2.val) :
    A.subgroupOf C × V ≃ₜ B.subgroupOf C :=
  let source : A.subgroupOf C × V ≃ₜ
      {p : A.subgroupOf B × V // p.1.val.val ∈ C} :=
    { toFun p := ⟨(⟨⟨p.1.val.val, hABC ⟨p.1.property, p.1.val.property⟩⟩, p.1.property⟩,
        p.2), p.1.val.property⟩
      invFun p := (⟨⟨p.val.1.val.val, p.property⟩, p.val.1.property⟩, p.val.2)
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let target : {g : B // g.val ∈ C} ≃ₜ B.subgroupOf C :=
    { toFun g := ⟨⟨g.val.val, g.property⟩, g.val.property⟩
      invFun g := ⟨⟨g.val.val, g.property⟩, g.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  source.trans ((e.subtype (fun p => by
    rw [he]
    exact (C.mul_mem_cancel_right (hVC p.2.property)).symm)).trans target)

private theorem restrictFirstChart_apply
    (hABC : A ⊓ C ≤ B) (hVC : V ≤ C)
    (e : A.subgroupOf B × V ≃ₜ B)
    (he : ∀ p : A.subgroupOf B × V, (e p : H) = p.1.val.val * p.2.val)
    (p : A.subgroupOf C × V) :
    (restrictFirstChart hABC hVC e he p).val.val = p.1.val.val * p.2.val :=
  he (⟨⟨p.1.val.val, hABC ⟨p.1.property, p.1.val.property⟩⟩, p.1.property⟩, p.2)

private def factorizationOfCharts (hABC : A ⊓ C ≤ B)
    (hVB : V ≤ B) (hVC : V ≤ C) (hWC : W ≤ C)
    (e₁ : A.subgroupOf B × V ≃ₜ B) (e₂ : B.subgroupOf C × W ≃ₜ C)
    (he₁ : ∀ p : A.subgroupOf B × V, (e₁ p : H) = p.1.val.val * p.2.val)
    (he₂ : ∀ p : B.subgroupOf C × W, (e₂ p : H) = p.1.val.val * p.2.val) :
    OrderedSubgroupFactorization A B C V W := by
  let e := restrictFirstChart hABC hVC e₁ he₁
  refine {
    first_le := hVB
    first_le_target := hVC
    second_le := hWC
    first := e₁
    second := e₂
    composite := (Homeomorph.prodAssoc _ _ _).symm.trans
      ((e.prodCongr (Homeomorph.refl _)).trans e₂)
    first_eq := fun p => Subtype.ext (he₁ p)
    second_eq := fun p => Subtype.ext (he₂ p)
    composite_eq := ?_ }
  intro p
  apply Subtype.ext
  change (e₂ (e (p.1, p.2.1), p.2.2) : H) = p.1.val.val * (p.2.1.val * p.2.2.val)
  rw [he₂, restrictFirstChart_apply, mul_assoc]

end Restriction

/-- The literal ordered charts for the three radicals of a distance-additive
triple with a common centralizer. -/
def distanceAdditiveRadicalFactorizationData
    (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer ψ₀)
    (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer ψ₀)
    (hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂) :
    OrderedSubgroupFactorization (radical ψ₀) (radical ψ₁) (radical ψ₂)
      (radical ψ₁ ⊓ oppositeRadical ψ₀) (radical ψ₂ ⊓ oppositeRadical ψ₁) :=
  factorizationOfCharts hd.1 inf_le_left (firstComplement_le_target ψ₀ ψ₁ ψ₂ h₁ h₂ hd)
    inf_le_left (commonLeviRadicalChart ψ₀ ψ₁ h₁.symm)
    (commonLeviRadicalChart ψ₁ ψ₂ (h₁.trans h₂.symm))
    (commonLeviRadicalChart_apply ψ₀ ψ₁ h₁.symm)
    (commonLeviRadicalChart_apply ψ₁ ψ₂ (h₁.trans h₂.symm))

end Langlands.Plancherel.DynamicCommonLeviComposition
