import Langlands.Shimura.PEL.TraceSimilitudesTopology
import Langlands.Shimura.Unitary.HarrisLevels

/-! # Harris trace-form comparison on compact open level towers -/

noncomputable section

universe u v w z t

namespace Langlands.Shimura

open CategoryTheory

namespace CompactOpenLevel

variable {G : Type u} {H : Type v}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

@[ext] theorem ext {K L : CompactOpenLevel G}
    (h : K.openSubgroup = L.openSubgroup) : K = L := by
  cases K
  cases L
  cases h
  rfl

@[simp] theorem eqToHom_element {K L : CompactOpenLevel G} (h : K = L) :
    (eqToHom h : K ⟶ L).element = 1 := by
  subst L
  rfl

/-- The image level, written as an inverse image under the inverse homeomorphism. -/
def transport (e : G ≃ₜ* H) (K : CompactOpenLevel G) : CompactOpenLevel H where
  openSubgroup := K.openSubgroup.comap e.symm.toMonoidHom e.symm.continuous
  isCompact := e.symm.toHomeomorph.isCompact_preimage.mpr K.isCompact

@[simp] theorem mem_transport (e : G ≃ₜ* H) (K : CompactOpenLevel G) (h : H) :
    h ∈ (transport e K).subgroup ↔ e.symm h ∈ K.subgroup := Iff.rfl

@[simp] theorem transport_mem (e : G ≃ₜ* H) (K : CompactOpenLevel G) (g : G) :
    e g ∈ (transport e K).subgroup ↔ g ∈ K.subgroup := by
  simp only [mem_transport, e.symm_apply_apply]

/-- Transport actual arrows, including their representing group elements. -/
def transportFunctor (e : G ≃ₜ* H) : CompactOpenLevel G ⥤ CompactOpenLevel H where
  obj := transport e
  map {K L} f := ⟨e f.element, fun h hh => by
    change e.symm h ∈ K.subgroup at hh
    change e.symm ((e f.element)⁻¹ * h * e f.element) ∈ L.subgroup
    simpa only [map_mul, map_inv, e.symm_apply_apply] using
      f.respects (e.symm h) hh⟩
  map_id K := by apply Arrow.ext; exact e.map_one
  map_comp f g := by apply Arrow.ext; exact e.map_mul f.element g.element

@[simp] theorem transportFunctor_map_element (e : G ≃ₜ* H)
    {K L : CompactOpenLevel G} (f : K ⟶ L) :
    ((transportFunctor e).map f).element = e f.element := rfl

@[simp] theorem transport_symm (e : G ≃ₜ* H) (K : CompactOpenLevel G) :
    transport e.symm (transport e K) = K := by
  apply CompactOpenLevel.ext
  apply OpenSubgroup.ext
  intro g
  change e.symm (e g) ∈ K.subgroup ↔ g ∈ K.subgroup
  rw [e.symm_apply_apply]

section Hecke

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The intermediate compact open subgroup in a Hecke span is preserved. -/
theorem transport_heckeLevel (e : G ≃ₜ* H) (K L : CompactOpenLevel G) (g : G) :
    transport e (heckeLevel K L g) =
      heckeLevel (transport e K) (transport e L) (e g) := by
  apply CompactOpenLevel.ext
  apply OpenSubgroup.ext
  intro h
  change (e.symm h ∈ K.subgroup ∧ g⁻¹ * e.symm h * (g⁻¹)⁻¹ ∈ L.subgroup) ↔
    (e.symm h ∈ K.subgroup ∧
      e.symm ((e g)⁻¹ * h * ((e g)⁻¹)⁻¹) ∈ L.subgroup)
  simp only [inv_inv, map_mul, map_inv, e.symm_apply_apply]

/-- After identifying the intermediate levels, transport preserves the first leg. -/
theorem transport_heckeLeft (e : G ≃ₜ* H) (K L : CompactOpenLevel G) (g : G) :
    (transportFunctor e).map (heckeLeft K L g) =
      eqToHom (transport_heckeLevel e K L g) ≫
        heckeLeft (transport e K) (transport e L) (e g) := by
  apply Arrow.ext
  change e 1 = (eqToHom (transport_heckeLevel e K L g)).element * 1
  rw [eqToHom_element, one_mul]
  exact e.map_one

/-- After identifying the intermediate levels, transport preserves the second leg. -/
theorem transport_heckeRight (e : G ≃ₜ* H) (K L : CompactOpenLevel G) (g : G) :
    (transportFunctor e).map (heckeRight K L g) =
      eqToHom (transport_heckeLevel e K L g) ≫
        heckeRight (transport e K) (transport e L) (e g) := by
  apply Arrow.ext
  change e g = (eqToHom (transport_heckeLevel e K L g)).element * e g
  rw [eqToHom_element, one_mul]

end Hecke
end CompactOpenLevel

namespace LevelSpace

variable {Γ : Type u} {G : Type v} {H : Type w} {X : Type z}
    [Group Γ] [Group G] [Group H] [MulAction Γ X]
    [TopologicalSpace G] [TopologicalSpace H]
    (ι : Γ →* G) (e : G ≃ₜ* H) (K : Subgroup G)

/-- Changing only the finite group preserves the double-quotient relation. -/
theorem transport_respects (x y : X × G) (h : levelSetoid ι K x y) :
    levelSetoid (e.toMonoidHom.comp ι) (K.comap e.symm.toMonoidHom)
      (x.1, e x.2) (y.1, e y.2) := by
  obtain ⟨γ, k, hk, hy₁, hy₂⟩ := h
  refine ⟨γ, e k, ?_, hy₁, ?_⟩
  · change e.symm (e k) ∈ K
    simpa only [e.symm_apply_apply] using hk
  · change e y.2 = e (ι γ) * e x.2 * e k
    rw [hy₂, map_mul, map_mul]

/-- The inverse coordinate change preserves the same double-quotient relation. -/
theorem transport_symm_respects (x y : X × H)
    (h : levelSetoid (e.toMonoidHom.comp ι) (K.comap e.symm.toMonoidHom) x y) :
    levelSetoid ι K (x.1, e.symm x.2) (y.1, e.symm y.2) := by
  obtain ⟨γ, h, hh, hy₁, hy₂⟩ := h
  refine ⟨γ, e.symm h, hh, hy₁, ?_⟩
  change e.symm y.2 = ι γ * e.symm x.2 * e.symm h
  change y.2 = e (ι γ) * x.2 * h at hy₂
  rw [hy₂, map_mul, map_mul, e.symm_apply_apply]

/-- The induced equivalence uses the actual finite-coordinate homeomorphism. -/
def transportEquiv :
    LevelSpace (X := X) ι K ≃
      LevelSpace (X := X) (e.toMonoidHom.comp ι) (K.comap e.symm.toMonoidHom) where
  toFun := Quotient.map (fun x => (x.1, e x.2)) (transport_respects ι e K)
  invFun := Quotient.map (fun x => (x.1, e.symm x.2)) (transport_symm_respects ι e K)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (mk K) (by simp)
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (mk _) (by simp)

@[simp] theorem transportEquiv_mk (x : X × G) :
    transportEquiv ι e K (mk K x) =
      mk (K.comap e.symm.toMonoidHom) (x.1, e x.2) := rfl

@[simp] theorem transportEquiv_symm_mk (x : X × H) :
    (transportEquiv ι e K).symm (mk (K.comap e.symm.toMonoidHom) x) =
      mk K (x.1, e.symm x.2) := rfl

variable [TopologicalSpace X]

/-- The double-quotient equivalence is a homeomorphism for the quotient topologies. -/
def transportHomeomorph :
    LevelSpace (X := X) ι K ≃ₜ
      LevelSpace (X := X) (e.toMonoidHom.comp ι) (K.comap e.symm.toMonoidHom) where
  toEquiv := transportEquiv ι e K
  continuous_toFun := by
    exact (show Continuous (fun x : X × G => (x.1, e x.2)) from
      continuous_fst.prodMk (e.continuous.comp continuous_snd)).quotient_map'
        (transport_respects ι e K)
  continuous_invFun := by
    exact (show Continuous (fun x : X × H => (x.1, e.symm x.2)) from
      continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)).quotient_map'
        (transport_symm_respects ι e K)

/-- All transporter maps commute with changing finite-group coordinates. -/
theorem transport_translate {K L : Subgroup G} (g : G)
    (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) (q : LevelSpace (X := X) ι K) :
    transportHomeomorph ι e L (translate g hg q) =
      translate (e g) (by
        intro h hh
        change e.symm h ∈ K at hh
        change e.symm ((e g)⁻¹ * h * e g) ∈ L
        simpa only [map_mul, map_inv, e.symm_apply_apply] using hg (e.symm h) hh)
        (transportHomeomorph ι e K q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    change mk _ (x.1, e (x.2 * g)) = mk _ (x.1, e x.2 * e g)
    rw [map_mul]

end LevelSpace

namespace LevelSpace

variable {Γ : Type u} {G H : Type v} {X : Type z}
    [Group Γ] [Group G] [Group H] [MulAction Γ X]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace X]
    [ContinuousMul G] [ContinuousMul H]
    (ι : Γ →* G) (e : G ≃ₜ* H)

/-- A natural isomorphism of actual topological level towers. -/
def transportTowerIso :
    tower (X := X) (ι := ι) ≅
      CompactOpenLevel.transportFunctor e ⋙
        tower (X := X) (ι := e.toMonoidHom.comp ι) :=
  NatIso.ofComponents (fun K =>
    { hom := TopCat.ofHom ⟨transportHomeomorph ι e K.subgroup,
        (transportHomeomorph ι e K.subgroup).continuous⟩
      inv := TopCat.ofHom ⟨(transportHomeomorph ι e K.subgroup).symm,
        (transportHomeomorph ι e K.subgroup).symm.continuous⟩
      hom_inv_id := by ext q; exact (transportHomeomorph ι e K.subgroup).symm_apply_apply q
      inv_hom_id := by ext q; exact (transportHomeomorph ι e K.subgroup).apply_symm_apply q })
    (fun f => by
      ext q
      exact transport_translate ι e f.element f.respects q)

end LevelSpace

namespace CentralSimpleUnitaryData

open NumberField Module _root_.Algebra
open scoped TensorProduct

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (β : Aˣ)
    (hβ : D.involution (β : A) = -(β : A))

/-- Retaining the opposite of the regular-operator group preserves the original
unitary group law, right-translation order, and scalar multiplier. -/
def harrisPELFiniteAdelicEquiv :
    D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints ≃ₜ*
      (D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteAdeles ℚ))ᵐᵒᵖ where
  toMulEquiv := (MulEquiv.opOp _).trans
    (D.harrisFiniteAdelicTraceSimilitudesContinuousEquiv β hβ).toMulEquiv.op
  continuous_toFun := MulOpposite.continuous_op.comp
    ((D.harrisFiniteAdelicTraceSimilitudesContinuousEquiv β hβ).continuous.comp
      MulOpposite.continuous_op)
  continuous_invFun := MulOpposite.continuous_unop.comp
    ((D.harrisFiniteAdelicTraceSimilitudesContinuousEquiv β hβ).symm.continuous.comp
      MulOpposite.continuous_unop)

@[simp] theorem harrisPELFiniteAdelicEquiv_apply
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints)
    (x : Langlands.Global.FiniteAdeles ℚ ⊗[ℚ] A) :
    ((D.harrisPELFiniteAdelicEquiv β hβ g).unop).val.1 x =
      x * (g.val.1 : Langlands.Global.FiniteAdeles ℚ ⊗[ℚ] A) := rfl

@[simp] theorem harrisPELFiniteAdelicEquiv_multiplier
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints) :
    (D.harrisPELFiniteAdelicEquiv β hβ g).unop.val.2 = g.val.2 := rfl

/-- The rational diagonal of the regular-operator presentation is the original
bilinear diagonal, under the proved rational comparison. -/
theorem harrisPELFiniteAdelicEquiv_diagonal
    (g : D.toSecondKindInvolution.rationalInvolution.similitudes) :
    D.harrisPELFiniteAdelicEquiv β hβ
        (D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal g) =
      MulOpposite.op (D.harrisBilinearDiagonal β hβ
        (Langlands.Global.FiniteAdeles ℚ)
        (D.harrisRationalTraceSimilitudesEquiv β hβ (MulOpposite.op g))) := by
  apply MulOpposite.unop_injective
  exact (D.harrisBilinearDiagonal_natural _ _ _ _).symm

/-- The actual compact-open level functor for the regular trace-form presentation. -/
def harrisPELLevelFunctor :
    CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints ⥤
      CompactOpenLevel
        (D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteAdeles ℚ))ᵐᵒᵖ :=
  CompactOpenLevel.transportFunctor (D.harrisPELFiniteAdelicEquiv β hβ)

@[simp] theorem harrisPELLevelFunctor_obj_mem
    (U : CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints)
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints) :
    D.harrisPELFiniteAdelicEquiv β hβ g ∈
        ((D.harrisPELLevelFunctor β hβ).obj U).subgroup ↔ g ∈ U.subgroup :=
  CompactOpenLevel.transport_mem _ _ _

@[simp] theorem harrisPELLevelFunctor_map_element
    {U V : CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints}
    (f : U ⟶ V) :
    ((D.harrisPELLevelFunctor β hβ).map f).element =
      D.harrisPELFiniteAdelicEquiv β hβ f.element := rfl

variable [IsScalarTower ℚ K A]
    (h : HasHarrisSignature D.toSecondKindInvolution n)
    (Φ : (E →+* ℝ) → (K →+* ℂ)) (hΦ : IsCMSection E K Φ)

/-- The trace-form tower uses the existing CM-compatible domain and the actual
bilinear rational diagonal; no output space is supplied. -/
def harrisPELLevelTower :
    CompactOpenLevel
        (D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteAdeles ℚ))ᵐᵒᵖ ⥤
      TopCat.{max u w} :=
  LevelSpace.tower (X := (HarrisSignatureCharts.ofSignature h hΦ).Domain)
    (ι := (D.harrisPELFiniteAdelicEquiv β hβ).toMonoidHom.comp
      D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal)

/-- Harris's unitary tower and its regular trace-form presentation agree
naturally at all compact open levels and all transporter arrows. -/
def harrisPELLevelTowerIso :
    unitaryLevelTower D h Φ hΦ ≅
      D.harrisPELLevelFunctor β hβ ⋙ D.harrisPELLevelTower β hβ h Φ hΦ := by
  letI : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  letI : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  exact LevelSpace.transportTowerIso
    (X := (HarrisSignatureCharts.ofSignature h hΦ).Domain)
    D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal
    (D.harrisPELFiniteAdelicEquiv β hβ)

@[simp] theorem harrisPELLevelTowerIso_hom_app_mk
    (U : CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints)
    (x : (HarrisSignatureCharts.ofSignature h hΦ).Domain ×
      D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints) :
    ((D.harrisPELLevelTowerIso β hβ h Φ hΦ).hom.app U) (LevelSpace.mk U.subgroup x) =
      LevelSpace.mk ((D.harrisPELLevelFunctor β hβ).obj U).subgroup
        (x.1, D.harrisPELFiniteAdelicEquiv β hβ x.2) := rfl

section HarrisCMType

variable {F : Type t} [Field F] [NumberField F] [IsCMField F]
    [IsQuadraticExtension ℚ F] (ιF : F →+* K) (τ₀ : F →+* ℂ)

/-- The regular trace-form tower for Harris's induced imaginary-quadratic CM type. -/
def harrisCMPELLevelTower :
    CompactOpenLevel
        (D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteAdeles ℚ))ᵐᵒᵖ ⥤
      TopCat.{max u w} :=
  D.harrisPELLevelTower β hβ h (harrisCMSection E ιF τ₀)
    (isCMSection_harrisCMSection E ιF τ₀)

/-- The comparison specialized to the CM type in Harris 1999, Section 4. -/
def harrisCMPELLevelTowerIso :
    harrisUnitaryLevelTower D h ιF τ₀ ≅
      D.harrisPELLevelFunctor β hβ ⋙ D.harrisCMPELLevelTower β hβ h ιF τ₀ :=
  D.harrisPELLevelTowerIso β hβ h (harrisCMSection E ιF τ₀)
    (isCMSection_harrisCMSection E ιF τ₀)

end HarrisCMType
end CentralSimpleUnitaryData
end Langlands.Shimura
