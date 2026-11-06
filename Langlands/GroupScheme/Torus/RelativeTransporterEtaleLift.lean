import Langlands.GroupScheme.Torus.RelativeTransporterSmooth
import Langlands.GroupScheme.Torus.TransporterFunctoriality
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction
import Langlands.AbelianScheme.KernelBaseChange

/-! # Pointed etale lifting of specified diagonalizable transporters -/

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.PointwiseSchemeAction

variable {S S' : Scheme.{u}} {H G : GroupScheme S}

/-- The pullback point equivalence transfers the original all-refinement
transporter equation to the actual pulled-back group maps. -/
theorem IsTransporter.baseChange_of_equiv (p : S' ⟶ S) (i₁ i₂ : H ⟶ G) {T : Over S'}
    (g : T ⟶ ((GroupScheme.baseChange p).obj G).X)
    (hg : IsTransporter i₁ i₂ (baseChangePointsEquiv p G T g)) :
    IsTransporter ((GroupScheme.baseChange p).map i₁) ((GroupScheme.baseChange p).map i₂) g := by
  intro V b h
  apply (baseChangePointsEquiv p G V).injective
  rw [map_mul, map_mul, baseChangePointsEquiv_comp p i₁ V h,
    baseChangePointsEquiv_comp p i₂ V h, baseChangePointsEquiv_naturality]
  exact hg ((Over.map p).obj V) ((Over.map p).map b) (baseChangePointsEquiv p H V h)

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)}
  (i₁ i₂ : (Diagonalizable.groupScheme R M).toGrp ⟶ G)

/-- Actual pointed etale data lifting a prescribed residue-valued transporter. -/
structure PointedEtaleTransporterData (s : Spec R)
    (g₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ Spec R
  residuePoint : Spec ((Spec R).residueField s) ⟶ neighbourhood
  etale : Etale projection
  residue_over : residuePoint ≫ projection = (Spec R).fromSpecResidueField s
  pointMap : Over.mk projection ⟶ G.X
  isTransporter : IsTransporter i₁ i₂ pointMap
  recovers : Over.homMk residuePoint residue_over ≫ pointMap = g₀

/-- Construct a pointed etale lift of a specified actual transporter point. -/
def pointedEtaleTransporter [IsAffine G.X.left] (hG : Smooth G.X.hom) (s : Spec R)
    (g₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X)
    (hg₀ : IsTransporter i₁ i₂ g₀) : PointedEtaleTransporterData i₁ i₂ s g₀ :=
  Classical.choice <| by
    let φ : R ⟶ (Spec R).residueField s := Spec.preimage ((Spec R).fromSpecResidueField s)
    let : Algebra R ((Spec R).residueField s) := φ.hom.toAlgebra
    let C : CommAlgCat.{u} R := CommAlgCat.of R ((Spec R).residueField s)
    let c : (algSpec R).obj (op C) ⟶ Over.mk ((Spec R).fromSpecResidueField s) :=
      Over.homMk (𝟙 _) (by
        change (𝟙 _) ≫ (Spec R).fromSpecResidueField s = Spec.map φ
        rw [Category.id_comp]
        exact (Spec.map_preimage _).symm)
    obtain ⟨y, hy⟩ := (exists_relativeTransporter_factor_iff i₁ i₂ (c ≫ g₀)).mpr (hg₀.restrict c)
    have hybase : y.left ≫ (relativeTransporterScheme i₁ i₂).hom =
        (Spec R).fromSpecResidueField s := by
      rw [Over.w y]
      change Spec.map φ = _
      exact Spec.map_preimage _
    have hyrec : y.left ≫ (relativeTransporterHom i₁ i₂).left = g₀.left := by
      have h := congrArg Over.Hom.left hy
      change y.left ≫ (relativeTransporterHom i₁ i₂).left = (𝟙 _) ≫ g₀.left at h
      simpa only [Category.id_comp] using h
    let := smooth_relativeTransporterScheme i₁ i₂ hG
    let d := Langlands.AlgebraicGeometry.pointedEtaleSection
      (relativeTransporterScheme i₁ i₂).hom s y.left hybase
    let a : Over.mk d.projection ⟶ relativeTransporterScheme i₁ i₂ :=
      Over.homMk d.sectionMap d.section_over
    let g : Over.mk d.projection ⟶ G.X := a ≫ relativeTransporterHom i₁ i₂
    refine ⟨⟨d.neighbourhood, d.projection, d.point, d.etale, d.point_over, g,
      (relativeTransporterHom_isTransporter i₁ i₂).restrict a, ?_⟩⟩
    apply Over.OverMorphism.ext
    change d.point ≫ (d.sectionMap ≫ (relativeTransporterHom i₁ i₂).left) = g₀.left
    rw [← Category.assoc, d.recovers]
    exact hyrec

namespace PointedEtaleTransporterData

variable {i₁ i₂} {s : Spec R}
  {g₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X}
  (d : PointedEtaleTransporterData i₁ i₂ s g₀)

/-- The identity scheme map compares the mapped terminal test with the given projection. -/
def identityComparison :
    (Over.map d.projection).obj (Over.mk (𝟙 d.neighbourhood)) ⟶ Over.mk d.projection :=
  Over.homMk (𝟙 _) (by simp)

/-- The actual section of the pulled-back group corresponding to the lifted transporter. -/
def baseChangedSection : Over.mk (𝟙 d.neighbourhood) ⟶ ((GroupScheme.baseChange d.projection).obj G).X :=
  (baseChangePointsEquiv d.projection G _).symm (d.identityComparison ≫ d.pointMap)

/-- The exact pullback adjunction equation for the actual lifted section. -/
theorem baseChangePointsEquiv_baseChangedSection :
    baseChangePointsEquiv d.projection G _ d.baseChangedSection =
      d.identityComparison ≫ d.pointMap :=
  MulEquiv.apply_symm_apply _ _

/-- The lifted section satisfies the transporter equation for the actual
base-changed homomorphisms on all refinements of every test scheme. -/
theorem baseChangedSection_isTransporter :
    IsTransporter ((GroupScheme.baseChange d.projection).map i₁) ((GroupScheme.baseChange d.projection).map i₂)
      d.baseChangedSection := by
  apply IsTransporter.baseChange_of_equiv
  rw [d.baseChangePointsEquiv_baseChangedSection]
  exact d.isTransporter.restrict d.identityComparison

/-- Specialization recovers the original residue-valued point as a scheme morphism. -/
theorem baseChangedSection_recovers :
    d.residuePoint ≫ d.baseChangedSection.left ≫ Limits.pullback.fst G.X.hom d.projection =
      g₀.left := by
  have hc : d.baseChangedSection.left ≫ Limits.pullback.fst G.X.hom d.projection =
      d.pointMap.left := by
    have h := congrArg Over.Hom.left d.baseChangePointsEquiv_baseChangedSection
    simpa only [baseChangePointsEquiv_left, Over.comp_left, identityComparison,
      Over.homMk_left, Category.id_comp] using h
  rw [hc]
  exact congrArg Over.Hom.left d.recovers

end PointedEtaleTransporterData

end Langlands.GroupScheme.PointwiseSchemeAction
