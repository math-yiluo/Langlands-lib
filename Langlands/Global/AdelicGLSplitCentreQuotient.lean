import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof
import Langlands.Global.DiscreteLeftCosetMeasureTransport
import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters
import Langlands.GroupScheme.Rational.KernelCentralizerLie

/-! # The positive scalar realization of the general-linear adelic quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global

open Langlands.GroupScheme

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

namespace AdelicGL

/-- The image of the positive real scalars, embedded diagonally at infinity and with finite
component one. -/
def splitCentre : Subgroup (AdelicGL F n) :=
  (PositiveRealTorus.scalarSubgroup F).map (scalar F n).toMonoidHom

/-- The positive scalar subgroup together with the principal matrix points. -/
def splitCentreRationalSubgroup : Subgroup (AdelicGL F n) :=
  splitCentre F n ⊔ (rational F n).range

/-- The actual matrix left quotient by positive real scalars and principal points. -/
abbrev SplitCentreQuotient := LeftCosetSpace (splitCentreRationalSubgroup F n)

end AdelicGL

namespace GeneralLinearGroupPoints

local notation "RF" => CommRingCat.of F
local notation "GmF" => Gm (Spec RF)
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "A" => CommAlgCat.of F (Adeles F)
local notation "i" => GroupScheme.GeneralLinear.scalarTorus (Fin n) RF
local notation "Γ" => RestrictionSplitCentre.canonicalRationalSubgroup F GLG
local notation "Δ" => AdelicGL.splitCentreRationalSubgroup F n
local notation "hG" => isConnectedReductive_generalLinear F (Fin n)

local instance : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) RF

local instance : LocallyOfFiniteType (GLG).X.hom :=
  have := IsConnectedReductive.smooth hG
  inferInstance

private theorem characterValue_id_gm (x : AdelicGroupPoints F (GmF).toGrp) :
    Lie.characterValue (𝟙 GmF) x = Gm.affineUnitsEquiv RF A x := by
  change Gm.affineUnitsEquiv RF A (x ≫ (CommGroupScheme.groupHom (𝟙 GmF)).hom.hom) = _
  change Gm.affineUnitsEquiv RF A (x ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- The rank-one positive subgroup is detected by the identity character of `Gₘ`. -/
private theorem mem_intrinsicSubgroup_gm (x : AdelicGroupPoints F (GmF).toGrp) :
    x ∈ PositiveRealTorus.intrinsicSubgroup F GmF ↔
      Gm.affineUnitsEquiv RF A x ∈ PositiveRealTorus.scalarSubgroup F := by
  rw [PositiveRealTorus.mem_intrinsicSubgroup_iff]
  constructor
  · intro h
    change ∃ a : ℝ≥0ˣ, PositiveRealIdeles.full F a = Gm.affineUnitsEquiv RF A x
    simpa only [characterValue_id_gm] using h (𝟙 GmF)
  · rintro ⟨a, ha⟩ χ
    rw [eq_gmEndEquiv_zsmul F χ, Lie.characterValue_zsmul, characterValue_id_gm, ← ha]
    exact ⟨a ^ gmEndEquiv F χ, map_zpow (PositiveRealIdeles.full F) _ _⟩

/-- Evaluating the actual scalar torus on adelic points gives the existing matrix scalar map. -/
private theorem adelicHomeomorph_scalarTorus (x : AdelicGroupPoints F (GmF).toGrp) :
    adelicHomeomorph F n (PositiveRealTorus.pointMap F (GmF).toGrp GLG (Adeles F) i x) =
      AdelicGL.scalar F n (Gm.affineUnitsEquiv RF A x) := by
  let Z := (algSpec RF).obj (Opposite.op A)
  let r := (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := RF) A).symm
  change GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) RF A (x ≫ (i).hom.hom) =
    Matrix.GeneralLinearGroup.scalar (Fin n) (Gm.affineUnitsEquiv RF A x)
  have h := GroupScheme.GeneralLinear.pointsEquiv_scalarTorus (n := Fin n) (R := RF) Z x
  rw [GroupScheme.GeneralLinear.pointsEquiv_eq_affinePointsEquiv,
    GroupScheme.GeneralLinear.gm_pointsEquiv_eq_affinePointsEquiv] at h
  have hscalar := Matrix.GeneralLinearGroup.map_scalar (n := Fin n)
    (GroupScheme.Corepresented.affineSectionsIso (R := RF) A).inv.hom.toRingHom
    (Gm.affineUnitsEquiv RF A x)
  apply Units.ext
  ext a b
  apply r.injective
  exact congrArg (fun m : Matrix.GeneralLinearGroup (Fin n) ((algΓ RF).obj Z).unop =>
    m.val a b) (h.trans hscalar.symm)

/-- In positive rank the canonical split centre is precisely the positive scalar matrices
of Getz–Hahn (2.20), under the actual adelic point homeomorphism. -/
theorem mem_splitCentre_iff (hn : 0 < n) (x : AdelicGroupPoints F GLG) :
    adelicHomeomorph F n x ∈ AdelicGL.splitCentre F n ↔
      x ∈ RestrictionSplitCentre.canonicalSubgroup F GLG := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup
    (GroupScheme.GeneralLinear.scalarTorus_isSplitComponent (n := Fin n) F)]
  constructor
  · rintro ⟨a, ha, hax⟩
    let y := (Gm.affineUnitsEquiv RF A).symm a
    have hy : Gm.affineUnitsEquiv RF A y = a := (Gm.affineUnitsEquiv RF A).apply_symm_apply a
    refine ⟨y, (mem_intrinsicSubgroup_gm F y).mpr (by rw [hy]; exact ha), ?_⟩
    apply (adelicHomeomorph F n).injective
    rw [adelicHomeomorph_scalarTorus, hy]
    exact hax
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Gm.affineUnitsEquiv RF A y, (mem_intrinsicSubgroup_gm F y).mp hy,
      (adelicHomeomorph_scalarTorus F n y).symm⟩

/-- The inherited topological groups on the canonical centre and the matrix scalar image agree. -/
def splitCentreHomeomorph (hn : 0 < n) :
    RestrictionSplitCentre.canonicalSubgroup F GLG ≃ₜ* AdelicGL.splitCentre F n :=
  Langlands.QuotientIntegration.subgroupContinuousMulEquiv (adelicHomeomorph F n) _ _
    (mem_splitCentre_iff F n hn)

private theorem map_rationalSubgroup :
    (AdelicGroupPoints.rationalSubgroup F GLG).map (adelicHomeomorph F n).toMonoidHom =
      (AdelicGL.rational F n).range := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨rationalEquiv F n q, (adelicHomeomorph_rational F n q).symm⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := (rationalEquiv F n).surjective q
    exact ⟨_, ⟨g, rfl⟩, adelicHomeomorph_rational F n g⟩

theorem map_canonicalRationalSubgroup (hn : 0 < n) :
    (Γ).map (adelicHomeomorph F n).toMonoidHom = Δ := by
  change (_ ⊔ AdelicGroupPoints.rationalSubgroup F GLG).map
    (adelicHomeomorph F n).toMonoidHom = _
  rw [Subgroup.map_sup, map_rationalSubgroup]
  congr 1
  ext x
  obtain ⟨y, rfl⟩ := (adelicHomeomorph F n).surjective x
  exact (Subgroup.mem_map_iff_mem (f := (adelicHomeomorph F n).toMonoidHom)
    (adelicHomeomorph F n).injective).trans
    (mem_splitCentre_iff F n hn y).symm

private theorem mem_splitCentreRationalSubgroup_iff (hn : 0 < n)
    (x : AdelicGroupPoints F GLG) : adelicHomeomorph F n x ∈ Δ ↔ x ∈ Γ := by
  rw [← map_canonicalRationalSubgroup F n hn]
  exact Subgroup.mem_map_iff_mem (f := (adelicHomeomorph F n).toMonoidHom)
    (adelicHomeomorph F n).injective

theorem isClosed_splitCentreRationalSubgroup (hn : 0 < n) :
    IsClosed (Δ : Set (AdelicGL F n)) := by
  rw [← map_canonicalRationalSubgroup F n hn, Subgroup.coe_map]
  exact (adelicHomeomorph F n).toHomeomorph.isClosedMap _
    (RestrictionSplitCentre.isClosed_canonicalRationalSubgroup F GLG
      centralSplitTorusCharacter hG)

/-- The ambient point homeomorphism restricts to the subgroups used in the quotient. -/
def splitCentreRationalSubgroupHomeomorph (hn : 0 < n) :
    Γ ≃ₜ* Δ :=
  Langlands.QuotientIntegration.subgroupContinuousMulEquiv (adelicHomeomorph F n) Γ Δ
    (mem_splitCentreRationalSubgroup_iff F n hn)

@[simp]
theorem splitCentreRationalSubgroupHomeomorph_val (hn : 0 < n) (x : Γ) :
    (splitCentreRationalSubgroupHomeomorph F n hn x).val = adelicHomeomorph F n x.val :=
  rfl

/-- The map on representatives identifies the canonical `[GL_n]` with the matrix left quotient. -/
def splitCentreQuotientHomeomorph (hn : 0 < n) :
    RestrictionSplitCentre.CanonicalQuotient F GLG ≃ₜ AdelicGL.SplitCentreQuotient F n :=
  Homeomorph.Quotient.congr (adelicHomeomorph F n).toHomeomorph (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ Γ ↔ adelicHomeomorph F n y * (adelicHomeomorph F n x)⁻¹ ∈ Δ
    rw [← map_inv, ← map_mul]
    exact (mem_splitCentreRationalSubgroup_iff F n hn _).symm)

@[simp]
theorem splitCentreQuotientHomeomorph_mk (hn : 0 < n) (x : AdelicGroupPoints F GLG) :
    splitCentreQuotientHomeomorph F n hn (LeftCosetSpace.mk Γ x) =
      LeftCosetSpace.mk Δ (adelicHomeomorph F n x) := rfl

/-- The positive right translation agrees on the two left quotients. -/
theorem splitCentreQuotientHomeomorph_rightTranslate (hn : 0 < n)
    (g : AdelicGroupPoints F GLG) (q : RestrictionSplitCentre.CanonicalQuotient F GLG) :
    splitCentreQuotientHomeomorph F n hn (LeftCosetSpace.rightTranslate Γ g q) =
      LeftCosetSpace.rightTranslate Δ (adelicHomeomorph F n g)
        (splitCentreQuotientHomeomorph F n hn q) := by
  induction q using Quotient.inductionOn with
  | _ x => exact congrArg (LeftCosetSpace.mk Δ) (map_mul (adelicHomeomorph F n) x g)

section Measure

variable [MeasurableSpace (AdelicGL F n)]

/-- The matrix quotient measure with the inherited canonical `[GL_n]` normalization. -/
def splitCentreQuotientMeasure (hn : 0 < n) :
    Measure (AdelicGL.SplitCentreQuotient F n) :=
  Measure.map (splitCentreQuotientHomeomorph F n hn)
    (RestrictionSplitCentre.canonicalMeasure F GLG)

/-- The quotient map preserves the exact chosen normalization. -/
theorem measurePreserving_splitCentreQuotientHomeomorph [BorelSpace (AdelicGL F n)] (hn : 0 < n) :
    MeasurePreserving (splitCentreQuotientHomeomorph F n hn)
      (RestrictionSplitCentre.canonicalMeasure F GLG) (splitCentreQuotientMeasure F n hn) := by
  refine ⟨?_, rfl⟩
  exact (LeftCosetSpace.measurableEquivOfMulEquiv (adelicHomeomorph F n) Γ Δ
    (mem_splitCentreRationalSubgroup_iff F n hn)).measurable

/-- With the canonical ambient and subgroup Haar measures transported to matrices, the
matrix quotient measure satisfies the same Weil formula. -/
theorem splitCentreQuotientMeasure_isCompatible [BorelSpace (AdelicGL F n)] (hn : 0 < n) :
    haveI := Langlands.QuotientIntegration.isMulRightInvariant_map
      (splitCentreRationalSubgroupHomeomorph F n hn)
      (RestrictionSplitCentre.canonicalSubgroupHaarMeasure F GLG centralSplitTorusCharacter hG)
    Langlands.QuotientIntegration.IsCompatible Δ
      (Measure.map (adelicHomeomorph F n) (Measure.haar : Measure (AdelicGroupPoints F GLG)))
      (Measure.map (splitCentreRationalSubgroupHomeomorph F n hn)
        (RestrictionSplitCentre.canonicalSubgroupHaarMeasure F GLG centralSplitTorusCharacter hG))
      (splitCentreQuotientMeasure F n hn) := by
  let : PolishSpace (AdelicGL F n) := (adelicHomeomorph F n).symm.toHomeomorph.isClosedEmbedding.polishSpace
  let := isClosed_splitCentreRationalSubgroup F n hn
  let := LeftCosetSpace.quotient_borelSpace Δ
  let := RestrictionSplitCentre.canonicalQuotient_borelSpace F GLG centralSplitTorusCharacter hG
  exact Langlands.QuotientIntegration.isCompatible_map_equiv (adelicHomeomorph F n) Γ Δ
    (splitCentreRationalSubgroupHomeomorph F n hn) (splitCentreRationalSubgroupHomeomorph_val F n hn)
    (splitCentreQuotientHomeomorph F n hn) (splitCentreQuotientHomeomorph_mk F n hn)
    _ _ _ (RestrictionSplitCentre.canonicalMeasure_isCompatible F GLG centralSplitTorusCharacter hG)

/-- The matrix quotient has finite volume in this normalization. -/
theorem isFiniteMeasure_splitCentreQuotientMeasure (hn : 0 < n) :
    IsFiniteMeasure (splitCentreQuotientMeasure F n hn) := by
  let : IsFiniteMeasure (RestrictionSplitCentre.canonicalMeasure F GLG) :=
    RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume F GLG hG _ _
      (RestrictionSplitCentre.isSplitComponent_canonicalRestrictionComponent F GLG)
  exact (RestrictionSplitCentre.canonicalMeasure F GLG).isFiniteMeasure_map _

end Measure

end GeneralLinearGroupPoints

end Langlands.Global
