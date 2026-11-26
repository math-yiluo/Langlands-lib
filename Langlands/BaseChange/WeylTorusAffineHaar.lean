import Langlands.BaseChange.UnitsAffineHaar
import Langlands.BaseChange.WeylTorusNormSections

/-! # Additive Haar coordinates on a rational Weyl torus -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set _root_.Topology
open scoped NNReal

universe u v

section Algebra

variable {F : Type u} [Field F] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) F

/-- The rational centralizer subalgebra of a torus point. -/
abbrev weylTorusAlgebra (a : GeneralLinear n F) : Subalgebra F M :=
  Subalgebra.centralizer F {a.val}

theorem weylTorusAlgebra_toSubmodule (a : GeneralLinear n F) :
    (weylTorusAlgebra a).toSubmodule = weylTorusLie a := by
  ext x
  simp only [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, mem_ker_adjointDefect_iff, commute_iff_eq, eq_comm]

/-- The underlying vector space of the rational centralizer algebra. -/
def weylTorusAlgebraLieEquiv (a : GeneralLinear n F) :
    weylTorusAlgebra a ≃ₗ[F] weylTorusLie a :=
  (weylTorusAlgebra a).toSubmoduleEquiv.symm.trans
    (LinearEquiv.ofEq _ _ (weylTorusAlgebra_toSubmodule a))

@[simp]
theorem weylTorusAlgebraLieEquiv_val (a : GeneralLinear n F) (x : weylTorusAlgebra a) :
    (weylTorusAlgebraLieEquiv a x).val = x.val := rfl

variable [TopologicalSpace F]

/-- The units of the rational centralizer algebra are the rational torus. -/
def WeylTorus.algebraUnitsEquiv (T : WeylTorus F n) {a : GeneralLinear n F}
    (ha : glCentralizer a = T.val) : (weylTorusAlgebra a)ˣ ≃ₜ* T.val := by
  let A := weylTorusAlgebra a
  let f : Aˣ →* GeneralLinear n F := Units.map A.val.toMonoidHom
  have hF : IsEmbedding f := IsEmbedding.subtypeVal.units_map
  have hmem (x : Aˣ) : f x ∈ T.val := by
    rw [← ha, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    exact ((Subalgebra.mem_centralizer_iff F).mp x.val.property a.val (mem_singleton _)).symm
  let e := f.codRestrict T.val hmem
  have hemb : IsEmbedding e := IsEmbedding.subtypeVal.of_comp_iff.mp hF
  have hsurj : Function.Surjective e := by
    intro t
    have hA (s : T.val) : s.val.val ∈ A := by
      have hs : s.val ∈ glCentralizer a := ha.symm ▸ s.property
      rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hs
      refine (Subalgebra.mem_centralizer_iff F).mpr fun g hg => ?_
      rw [mem_singleton_iff.mp hg]
      exact (congrArg (fun u : GeneralLinear n F => u.val) hs).symm
    let u : Aˣ := ⟨⟨t.val.val, hA t⟩, ⟨(t.val⁻¹ : GeneralLinear n F).val, hA t⁻¹⟩,
      Subtype.ext t.val.val_inv, Subtype.ext t.val.inv_val⟩
    exact ⟨u, Subtype.ext (Units.ext rfl)⟩
  let μ := MulEquiv.ofBijective e ⟨hemb.injective, hsurj⟩
  let top := μ.toEquiv.toHomeomorphOfIsInducing hemb.isInducing
  exact { μ with continuous_toFun := top.continuous, continuous_invFun := top.symm.continuous }

@[simp]
theorem WeylTorus.algebraUnitsEquiv_val (T : WeylTorus F n) {a : GeneralLinear n F}
    (ha : glCentralizer a = T.val) (x : (weylTorusAlgebra a)ˣ) :
    (T.algebraUnitsEquiv ha x).val.val = x.val.val := rfl

end Algebra

section Measure

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} (T : WeylTorus F n) {a : GeneralLinear n F} (ha : glCentralizer a = T.val)
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (weylTorusLie a)] [BorelSpace (weylTorusLie a)]

/-- On each compact open torus subgroup, affine coordinates identify
restricted torus Haar with a positive multiple of restricted additive Haar. -/
theorem WeylTorus.exists_affineCoordinate_haar (U : OpenSubgroup T.val)
    (hU : IsCompact (U : Set T.val)) (μ : Measure T.val) [μ.IsHaarMeasure]
    (ξ : Measure (weylTorusLie a)) [ξ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧
      (μ.restrict (U : Set T.val)).map (T.affineCoordinate ha) =
        c • ξ.restrict (T.affineCoordinate ha '' (U : Set T.val)) := by
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let M := Matrix (Fin n) (Fin n) F
  let : IsTopologicalRing M := Matrix.topologicalRing
  let : SecondCountableTopology M :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  let : Module.Finite F M := inferInstanceAs (Module.Finite F (Fin n → Fin n → F))
  let A := weylTorusAlgebra a
  let : IsTopologicalRing A := Subring.instIsTopologicalRing A.toSubring
  let : Module.Finite F A := (A.toSubmoduleEquiv).finiteDimensional
  let : IsModuleTopology F A := isModuleTopologyOfFiniteDimensional
  let : LocallyCompactSpace A :=
    (Module.finBasis F A).equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology A := IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : SecondCountableTopology Aˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  let e := T.algebraUnitsEquiv ha
  let b : A ≃L[F] weylTorusLie a := (weylTorusAlgebraLieEquiv a).toContinuousLinearEquiv
  let V := U.comap e.toMonoidHom e.continuous
  have hV : IsCompact (V : Set Aˣ) := by
    change IsCompact (e.toHomeomorph ⁻¹' (U : Set T.val))
    rw [← e.toHomeomorph.image_symm]
    exact hU.image e.symm.continuous
  let μ' := μ.map e.symm
  let ξ' := ξ.map b.symm
  let : μ'.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  let : ξ'.IsAddHaarMeasure := b.symm.isAddHaarMeasure_map ξ
  have hval := finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := A)
  obtain ⟨c, hc, hh⟩ := unitsAffineHaar A hval V hV μ' ξ'
  let f : Aˣ → A := fun x => x.val - 1
  let V' := range (fun x : V => f x.val)
  have hcomp : b ∘ f = T.affineCoordinate ha ∘ e := by
    funext x
    exact Subtype.ext (by rfl)
  have hf : Measurable f := (hval.continuous.sub continuous_const).measurable
  have hT := (T.isOpenEmbedding_affineCoordinate ha).continuous.measurable
  have hh' := congrArg (Measure.map b) hh
  change ((μ'.restrict (V : Set Aˣ)).map f).map b = (c • ξ'.restrict V').map b at hh'
  have hrμ : μ'.restrict (V : Set Aˣ) = (μ.restrict (U : Set T.val)).map e.symm := by
    exact e.symm.toHomeomorph.measurableEmbedding.restrict_map μ (V : Set Aˣ)
      |>.trans (congrArg (fun s => (μ.restrict s).map e.symm) (by
        ext x
        change e (e.symm x) ∈ (U : Set T.val) ↔ x ∈ _
        rw [e.apply_symm_apply]))
  have hrξ : (ξ'.restrict V').map b = ξ.restrict (b '' V') := by
    have hbb : ξ'.map b = ξ := by
      change (ξ.map b.symm).map b = _
      rw [Measure.map_map b.continuous.measurable b.symm.continuous.measurable]
      simp only [show ⇑b ∘ ⇑b.symm = id from funext b.apply_symm_apply, Measure.map_id]
    have h := b.toHomeomorph.measurableEmbedding.restrict_map ξ' (b '' V')
    change (ξ'.map b).restrict (b '' V') = (ξ'.restrict (b ⁻¹' (b '' V'))).map b at h
    rw [hbb, preimage_image_eq _ b.injective] at h
    exact h.symm
  have hIm : b '' V' = T.affineCoordinate ha '' (U : Set T.val) := by
    ext x
    constructor
    · rintro ⟨y, ⟨y', rfl⟩, rfl⟩
      exact ⟨e y'.val, y'.property, (congrFun hcomp y'.val).symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨f (e.symm y), ⟨⟨e.symm y, ?_⟩, rfl⟩, ?_⟩
      · change e (e.symm y) ∈ (U : Set T.val)
        rwa [e.apply_symm_apply]
      · exact (congrFun hcomp _).trans (congrArg _ (e.apply_symm_apply _))
  have he : Measurable e := e.continuous.measurable
  have he' : Measurable e.symm := e.symm.continuous.measurable
  rw [Measure.map_smul _ b.continuous.measurable.aemeasurable, hrξ, hIm, hrμ,
    Measure.map_map b.continuous.measurable hf, hcomp, Measure.map_map (hT.comp he) he'] at hh'
  have heq : ((T.affineCoordinate ha ∘ e) ∘ e.symm) = T.affineCoordinate ha :=
    funext fun x => congrArg _ (e.apply_symm_apply x)
  rw [heq] at hh'
  exact ⟨c, hc, hh'⟩

end Measure
end Langlands.BaseChange
