import Langlands.Representation.Plancherel.DynamicRepresentedGalleryOperators
import Langlands.Representation.Families.AdmissibleInducedIrreducibilityOpen

/-! # A principal irreducibility locus at a represented gallery vertex -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G)
  (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))

set_option hygiene false in
local notation "H" => parameterScheme χ
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "Poly" => MvPolynomial (Fin (rationalImageRank H)) ℂ
set_option hygiene false in
local notation "principal" => rationalUnramifiedPrincipalOpen H (parameterScheme_isConnectedReductive χ hG)
set_option hygiene false in
local notation "twisted" => fun z : X => σ.twist z.val.toMonoidHom
  (unramifiedCharacter_isOpen_ker (normCharacters χ) z)

/-- A nonzero principal open on which the represented source remains irreducible. -/
def HasPrincipalRepresentedIrreducibilityLocus
    {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} (D : ParabolicData χ ψ T a) : Prop :=
  ∃ p : Poly, p ≠ 0 ∧ ∀ z ∈ principal p, (representedInduction hG D (twisted z)).IsIrreducible

set_option maxHeartbeats 1800000 in
/-- An irreducible twist of an induced irreducible admissible coefficient supplies
an irreducible principal open in the original parameter space. -/
theorem hasPrincipalRepresentedIrreducibilityLocus_of_one
    {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} (D : ParabolicData χ ψ T a)
    (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible) (z₀ : X)
    (h₀ : (representedInduction hG D (twisted z₀)).IsIrreducible) :
    HasPrincipalRepresentedIrreducibilityLocus hG σ D := by
  obtain ⟨p, hz₀, hp⟩ := Renard.AlgebraicFamily.admissibleInducedIrreducibilityOpen.{u, uV}
    F G hG D.P H D.U D.p D.l D.n D.r.isCompatible.parabolic D.r.isCompatible.levi
    D.radical (multiplication_isIso hG D) σ hσ hA z₀ h₀
  have hzero : p ≠ 0 := by
    intro h
    have hz := (mem_rationalUnramifiedPrincipalOpen H (parameterScheme_isConnectedReductive χ hG) p z₀).mp hz₀
    rw [h, map_zero] at hz
    exact hz rfl
  exact ⟨p, hzero, hp⟩

variable (ha : IsSplitComponent a)
set_option hygiene false in
local notation "d" => galleryVertexData (χ := χ) hG ha

set_option maxHeartbeats 1800000 in
/-- Both orders are regular on a principal subregion of the source irreducibility locus. -/
theorem exists_galleryRegularIrreduciblePrincipalOpen
    (x y : GalleryVertex χ) (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible)
    (hIrr : HasPrincipalRepresentedIrreducibilityLocus hG σ (d x)) :
    ∃ p : Poly, p ≠ 0 ∧ ∀ z ∈ principal p,
      (representedInduction hG (d x) (twisted z)).IsIrreducible ∧
      representedIsPQRegular hG (d x) (d y) (twisted z) ∧
      representedIsPQRegular hG (d y) (d x) (twisted z) := by
  classical
  obtain ⟨pI, hI, hIOn⟩ := hIrr
  let vertices : Finset (GalleryVertex χ) := {x, y}
  have hx : x ∈ vertices := Finset.mem_insert_self _ _
  have hy : y ∈ vertices := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨pR, hR, hROn⟩ := exists_generic_galleryRegular (χ := χ) hG ha vertices σ hσ hA
  refine ⟨pI * pR, mul_ne_zero hI hR, ?_⟩
  intro z hz
  have he := (mem_rationalUnramifiedPrincipalOpen H (parameterScheme_isConnectedReductive χ hG)
    (pI * pR) z).mp hz
  rw [map_mul] at he
  have hzI := (mem_rationalUnramifiedPrincipalOpen H (parameterScheme_isConnectedReductive χ hG)
    pI z).mpr (left_ne_zero_of_mul he)
  have hzR := (mem_rationalUnramifiedPrincipalOpen H (parameterScheme_isConnectedReductive χ hG)
    pR z).mpr (right_ne_zero_of_mul he)
  exact ⟨hIOn z hzI, hROn z hzR x hx y hy, hROn z hzR y hy x hx⟩

end Langlands.Plancherel.DynamicCommonLeviPresentations
