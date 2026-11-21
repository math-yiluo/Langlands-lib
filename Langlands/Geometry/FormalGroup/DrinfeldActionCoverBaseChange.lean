import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderCoefficientUnit
import Langlands.Geometry.FormalGroup.GlobalAtlasRationalMorphism

/-! # Coefficient extension of source maps on the actual reduced cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory TensorProduct

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {S T : Type v} [CommRing S] [Algebra O S] [CommRing T] [Algebra O T]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O S σ} {N : ModuleLaw O S τ}
variable (E : ModuleLaw.OrderAction D M) (E' : ModuleLaw.OrderAction D N)
variable (t : Set S) (ht : Ideal.span t = ⊤) (θ : S →ₐ[O] T)

set_option maxHeartbeats 400000 in
private theorem globalCoverBaseAlongIso_hom_natural (q : ModuleLaw.Hom M N) :
    (ofGlobalHom (q.map θ) (θ '' t) ((ofGlobalCover M t ht).baseOpens_covers (coefficientTest θ))).comp
        (globalCoverBaseAlongIso E t ht θ).hom.val =
      (globalCoverBaseAlongIso E' t ht θ).hom.val.comp ((ofGlobalHom q t ht).baseChangeAlong θ) := by
  apply Hom.ext
  intro C b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (globalChartHom (q.map θ) b.val C hb).toHom.toCoordinateMap.comp
      (((globalCoverBaseAlongIso E t ht θ).hom.val.hom C b hb).toHom.toCoordinateMap) =
    (((globalCoverBaseAlongIso E' t ht θ).hom.val.hom C b hb).toHom.toCoordinateMap).comp
      ((((ofGlobalHom q t ht).baseChangeAlong θ).hom C b hb).toHom.toCoordinateMap)
  rw [globalCoverBaseAlongIso_hom_coordinates, globalCoverBaseAlongIso_hom_coordinates,
    CoordinateMap.comp_id, CoordinateMap.id_comp]
  refine (globalChartHom_coordinates _ _ _ _).trans
    ((Hom.baseChangeAlong_coordinates (ofGlobalHom q t ht) θ C b hb).trans ?_).symm
  rw [show ((ofGlobalHom q t ht).hom (restrictCoefficientAlgebra θ C)
    ((ofGlobalCover N t ht).baseSource (coefficientTest θ) b)
    ((ofGlobalCover N t ht).baseSource_unit (coefficientTest θ) C b hb)).toHom.toCoordinateMap =
      (q.toHom.toCoordinateMap.map (algebraMap S (restrictCoefficientAlgebra θ C))) from
    globalChartHom_coordinates _ _ _ _]
  change q.toHom.toCoordinateMap.map (algebraMap S (restrictCoefficientAlgebra θ C)) =
    (q.toHom.toCoordinateMap.map θ.toRingHom).map (algebraMap T C)
  rw [CoordinateMap.map_ringHom_comp]
  rfl

set_option maxHeartbeats 400000 in
/-- The actual comparisons to the extended global cover commute with restricting
whole rational maps and extending their coefficients. -/
theorem globalCoverBaseAlongIso_rational_natural (q : ModuleLaw.RationalHom F M N) :
    RationalHom.comp
        (ofGlobalRationalHom (θ '' t) ((ofGlobalCover M t ht).baseOpens_covers (coefficientTest θ))
          (ModuleLaw.RationalHom.map θ q))
        (RationalHom.ofHom (globalCoverBaseAlongIso E t ht θ).hom.val) =
      RationalHom.comp (RationalHom.ofHom (globalCoverBaseAlongIso E' t ht θ).hom.val)
        (RationalHom.baseChangeAlong θ (ofGlobalRationalHom t ht q)) := by
  induction q using TensorProduct.inductionOn with
  | add q₁ q₂ h₁ h₂ =>
    simp only [_root_.map_add, RationalHom.add_comp, RationalHom.comp_add, h₁, h₂]
  | tmul a q =>
    have e : (a ⊗ₜ[O] q : ModuleLaw.RationalHom F M N) =
        a • ModuleLaw.RationalHom.ofHom q := by
      rw [ModuleLaw.RationalHom.ofHom_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    simp only [_root_.map_smul, ModuleLaw.RationalHom.map_ofHom, ofGlobalRationalHom_ofHom,
      RationalHom.baseChangeAlong_ofHom, RationalHom.smul_comp, RationalHom.comp_smul,
      ← RationalHom.ofHom_comp]
    exact congrArg (fun g => a • RationalHom.ofHom (F := F) g)
      (globalCoverBaseAlongIso_hom_natural E E' t ht θ q)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw
open BasicAtlas.RationalHom (comp comp_assoc ofHom)

attribute [local instance] coefficientAlgebra coefficientScalarTower

section Cover

variable {O S D F : Type*} [CommRing O] [CommRing S] [Algebra O S]
  [Ring D] [Algebra O D] [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O S σ} {N : ModuleLaw O S τ}

private theorem globalCoverOrderIsoOfCoverEq_rational_natural
    (E : ModuleLaw.OrderAction D M) (E' : ModuleLaw.OrderAction D N)
    (t u : Set S) (ht : Ideal.span t = ⊤) (hu : Ideal.span u = ⊤) (e : t = u)
    (q : ModuleLaw.RationalHom F M N) :
    comp (BasicAtlas.ofGlobalRationalHom u hu q)
        (ofHom (BasicAtlas.globalCoverOrderIsoOfCoverEq E t u ht hu e).hom.val) =
      comp (ofHom (BasicAtlas.globalCoverOrderIsoOfCoverEq E' t u ht hu e).hom.val)
        (BasicAtlas.ofGlobalRationalHom t ht q) := by
  subst u
  exact (BasicAtlas.RationalHom.comp_id _).trans (BasicAtlas.RationalHom.id_comp _).symm

end Cover

section Squares

variable {O S F : Type*} [CommRing O] [CommRing S] [Algebra O S]
  [Field F] [Algebra O F]
variable {σ : Type} [Finite σ]
variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : BasicAtlas O S σ}
variable {e₀ : X₀.opens = Y₀.opens} {e₁ : X₁.opens = Y₁.opens} {e₂ : X₂.opens = Y₂.opens}
variable {a₀ : X₀.opens = X₁.opens} {a₁ : X₁.opens = X₂.opens}
variable {b₀ : Y₀.opens = Y₁.opens} {b₁ : Y₁.opens = Y₂.opens}

private theorem pasteRationalSquares
    (q₀ : BasicAtlas.RationalHom F X₀ Y₀ e₀)
    (q₁ : BasicAtlas.RationalHom F X₁ Y₁ e₁)
    (q₂ : BasicAtlas.RationalHom F X₂ Y₂ e₂)
    (x₀ : BasicAtlas.RationalHom F X₀ X₁ a₀)
    (x₁ : BasicAtlas.RationalHom F X₁ X₂ a₁)
    (y₀ : BasicAtlas.RationalHom F Y₀ Y₁ b₀)
    (y₁ : BasicAtlas.RationalHom F Y₁ Y₂ b₁)
    (h₀ : comp q₁ x₀ = comp y₀ q₀) (h₁ : comp q₂ x₁ = comp y₁ q₁) :
    comp q₂ (comp x₁ x₀) = comp (comp y₁ y₀) q₀ := by
  rw [← comp_assoc q₂, h₁, comp_assoc y₁, h₀, ← comp_assoc y₁]

end Squares

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}

variable (Φ : SpecialModule K D ι κ) (Y : SpecialAtlas K D ι A.obj) (f : A ⟶ B)
variable (a b : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)

/-- Restrict a global rational Hom between two extensions of the fixed frame
to the common reduced target cover. -/
def restrictFrameHom
    (q : ModuleLaw.RationalHom K (Φ.formalModule.map a) (Φ.formalModule.map b)) :
    BasicAtlas.RationalHom K (quotientFrame Φ a Y).atlas (quotientFrame Φ b Y).atlas rfl :=
  BasicAtlas.ofGlobalRationalHom Y.reduction.atlas.opens Y.reduction.atlas.covers q

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4096 in
/-- The whole global coefficient square restricts through the actual quotient-frame comparisons. -/
theorem quotientFrameBaseChangeIso_rational_natural
    (q : ModuleLaw.RationalHom K (Φ.formalModule.map a) (Φ.formalModule.map b))
    (q' : ModuleLaw.RationalHom K
      (Φ.formalModule.map ((Nilp.reducedScalarMap 𝒪[K] f).comp a))
      (Φ.formalModule.map ((Nilp.reducedScalarMap 𝒪[K] f).comp b)))
    (hq : ModuleLaw.RationalHom.comp q'
        (ModuleLaw.RationalHom.ofHom (ModuleLaw.mapCompIso Φ.formalModule a
          (Nilp.reducedScalarMap 𝒪[K] f)).hom) =
      ModuleLaw.RationalHom.comp
        (ModuleLaw.RationalHom.ofHom (ModuleLaw.mapCompIso Φ.formalModule b
          (Nilp.reducedScalarMap 𝒪[K] f)).hom)
        (ModuleLaw.RationalHom.map (Nilp.reducedScalarMap 𝒪[K] f) q)) :
    comp (F := K) (restrictFrameHom Φ (Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f))
        ((Nilp.reducedScalarMap 𝒪[K] f).comp a) ((Nilp.reducedScalarMap 𝒪[K] f).comp b) q')
        (ofHom (F := K) (quotientFrameBaseChangeIso Φ a Y f).hom.val) =
      comp (F := K) (ofHom (F := K) (quotientFrameBaseChangeIso Φ b Y f).hom.val)
        (BasicAtlas.RationalHom.baseChangeAlong (F := K)
          (X := (quotientFrame Φ a Y).atlas) (Y := (quotientFrame Φ b Y).atlas)
          (h := rfl) (Nilp.reducedScalarMap 𝒪[K] f)
          (restrictFrameHom Φ Y a b q)) := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let V := Y.reduction.atlas
  let U := ((Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B)).atlas
  let t := φ '' V.opens
  have ht : Ideal.span t = ⊤ := V.baseOpens_covers (BasicAtlas.coefficientTest φ)
  have he : t = U.opens := (Y.atlas.reductionBaseChangeOpens_eq f).symm
  let ResidueMap := κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
  let c₁ (ψ : ResidueMap) := ofHom (F := K)
    (BasicAtlas.globalCoverBaseAlongIso (Φ.order.map ψ) V.opens V.covers φ).hom.val
  let c₂ (ψ : ResidueMap) := ofHom (F := K)
    (BasicAtlas.ofGlobalHom (ModuleLaw.mapCompIso Φ.formalModule ψ φ).hom t ht)
  let c₃ (ψ : ResidueMap) := ofHom (F := K)
    (BasicAtlas.globalCoverOrderIsoOfCoverEq (Φ.order.map (φ.comp ψ)) t U.opens ht U.covers he).hom.val
  have hc (ψ : ResidueMap) :
      ofHom (F := K) (quotientFrameBaseChangeIso Φ ψ Y f).hom.val =
        comp (c₃ ψ) (comp (c₂ ψ) (c₁ ψ)) := by
    rw [← comp_assoc, ← BasicAtlas.RationalHom.ofHom_comp, ← BasicAtlas.RationalHom.ofHom_comp]
    rfl
  let q₀ := BasicAtlas.RationalHom.baseChangeAlong φ
    (BasicAtlas.ofGlobalRationalHom V.opens V.covers q)
  let q₁ := BasicAtlas.ofGlobalRationalHom t ht (ModuleLaw.RationalHom.map φ q)
  let q₂ := BasicAtlas.ofGlobalRationalHom t ht q'
  let q₃ := BasicAtlas.ofGlobalRationalHom U.opens U.covers q'
  have h₁ : comp q₁ (c₁ a) = comp (c₁ b) q₀ :=
    BasicAtlas.globalCoverBaseAlongIso_rational_natural (Φ.order.map a) (Φ.order.map b)
      V.opens V.covers φ q
  have h₂ : comp q₂ (c₂ a) = comp (c₂ b) q₁ := by
    have h := congrArg (BasicAtlas.ofGlobalRationalHom t ht) hq
    simp only [BasicAtlas.ofGlobalRationalHom_comp, BasicAtlas.ofGlobalRationalHom_ofHom] at h
    exact h
  have h₃ : comp q₃ (c₃ a) = comp (c₃ b) q₂ :=
    globalCoverOrderIsoOfCoverEq_rational_natural (Φ.order.map (φ.comp a))
      (Φ.order.map (φ.comp b)) t U.opens ht U.covers he q'
  have h₁₂ := pasteRationalSquares q₀ q₁ q₂ (c₁ a) (c₂ a) (c₁ b) (c₂ b) h₁ h₂
  have h₁₂₃ := pasteRationalSquares q₀ q₂ q₃ (comp (c₂ a) (c₁ a)) (c₃ a)
    (comp (c₂ b) (c₁ b)) (c₃ b) h₁₂ h₃
  change comp q₃ (ofHom (quotientFrameBaseChangeIso Φ a Y f).hom.val) =
    comp (ofHom (quotientFrameBaseChangeIso Φ b Y f).hom.val) q₀
  exact (congrArg (comp q₃) (hc a)).trans
    (h₁₂₃.trans (congrArg (fun r => comp r q₀) (hc b).symm))

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
