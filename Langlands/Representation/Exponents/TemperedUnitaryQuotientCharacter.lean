import Langlands.Representation.Exponents.TemperedUnitaryQuotientStructure
import Langlands.Representation.Exponents.CentralCharacterIdentityJacquet
import Langlands.Representation.Exponents.CentralEigencharacterExtensionProof
import Langlands.Representation.Exponents.FullCenterFromSplitComponent
import Langlands.Representation.Plancherel.SplitTorusNormFormula

/-! # Split-component unitarity of the selected unitary Jacquet quotient -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance quotientCharacterAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

variable [IsAffineHom M.X.hom]

local instance quotientCharacterLeviTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

namespace UnitaryJacquetIrreducibleQuotientData

/-- A scalar character of the selected quotient restricts to a character
with zero normalized real part on the actual Levi split component. -/
theorem splitComponentCentralCharacter_realPart_eq_zero
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π)
    (ω : Subgroup.center (rationalPoints M) →* ℂˣ)
    (hω : D.quotient.HasCentralCharacter ω) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
      (splitComponentCentralCharacter a ha ω) = 0 := by
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  let := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let J := (jacquetFunctor p l r hp hr hl hmul).obj π
  let e := leviPointsEquiv p l hp hl
  let Q := SmoothRep.pullback e.symm D.quotient
  let sourceMap := splitComponentPointsMap (l ≫ p) a
  have hsourceMap : ∀ t, sourceMap t ∈ Subgroup.center (pointImage (l ≫ p)) :=
    splitComponentPointsMap_mem_center (l ≫ p) ha
  let ψ := splitComponentCentralCharacter a ha ω
  let hcompl := htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha
  let F := unitaryJacquetQuotientImageMap p l r hp hl hr hmul ha π hcompl D
  have hscalar (t : rationalPoints A.toGrp) (y : Q) :
      Q.representation (sourceMap t) y = (ψ t : ℂ) • y := by
    have he : e.symm (sourceMap t) = rationalPoints.map a t := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      rfl
    change D.quotient.representation (e.symm (sourceMap t)) y = (ψ t : ℂ) • y
    rw [he]
    exact hω ⟨rationalPoints.map a t,
      ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ y
  by_contra hψ
  change Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 ψ ≠ 0 at hψ
  have hkill (χ : rationalPoints A.toGrp →* ℂˣ)
      (_hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
      (h0 : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0) :
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule ≤
        F.toLinearMap.ker := by
    intro x hx
    change F x = 0
    by_contra hFx
    have hm := map_mem_generalizedWeightSpace sourceMap χ hsourceMap F hx
    obtain ⟨n, hn⟩ :=
      (mem_generalizedWeightSpace_of_isSmooth sourceMap χ hsourceMap Q.isSmooth (F x)).mp hm
    have hχψ : χ = ψ := by
      ext t
      exact (eq_of_eigen_of_mem_genEigenspace (Q.representation (sourceMap t)) hFx
        (hscalar t (F x)) (hn t)).symm
    apply hψ
    simpa only [hχψ] using h0
  have hle :
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ≤ F.toLinearMap.ker := by
    rw [unitaryJacquetPart_toSubmodule]
    exact iSup_le fun χ => iSup_le fun hχ => iSup_le fun h0 => hkill χ hχ h0
  have hqzero (x : leviUnitaryJacquetModule p l r hp hl hr hmul ha π) :
      SmoothRep.hom D.quotientMap x = 0 := by
    have hz := hle x.property
    have he := congrArg (fun f => SmoothRep.hom f x)
      (unitaryJacquetModuleι_quotientFullMap p l r hp hl hr hmul ha π hcompl D)
    exact he.symm.trans hz
  have : D.quotient.representation.IsIrreducible := D.irreducible
  have : Nontrivial D.quotient :=
    IsSimpleModule.nontrivial ℂ[rationalPoints M] D.quotient.representation.asModule
  obtain ⟨y, hy⟩ := exists_ne (0 : D.quotient)
  obtain ⟨x, rfl⟩ := D.surjective y
  exact hy (hqzero x)

/-- The scalar character has unit modulus at every actual split-component
point. Smoothness supplies the open kernel needed by the norm formula. -/
theorem splitComponentCentralCharacter_norm_eq_one
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π)
    (ω : Subgroup.center (rationalPoints M) →* ℂˣ)
    (hω : D.quotient.HasCentralCharacter ω)
    (t : rationalPoints A.toGrp) :
    ‖(splitComponentCentralCharacter a ha ω t : ℂ)‖ = 1 := by
  have := ha.isAffine
  have := ha.isCentralSplitTorus.1.1.smooth
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let := RationalPointFamily.splitComponentPointTopology ha
  let : IsTopologicalGroup (rationalPoints A.toGrp) :=
    rationalPoint_isTopologicalGroup k A.toGrp
  have : D.quotient.representation.IsIrreducible := D.irreducible
  have : Nontrivial D.quotient :=
    IsSimpleModule.nontrivial ℂ[rationalPoints M] D.quotient.representation.asModule
  have hopen : IsOpen
      ((splitComponentCentralCharacter a ha ω).ker : Set (rationalPoints A.toGrp)) :=
    isOpen_ker_of_scalar_action D.quotient.representation D.quotient.isSmooth
      (rationalPoints.map a)
      (continuous_rationalPointMap k a.hom.hom)
      (splitComponentCentralCharacter a ha ω)
      (fun x y => hω ⟨rationalPoints.map a x,
        ha.isCentralSplitTorus.isCentral.map_mem_center x⟩ y)
  exact (Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff
    ha.isCentralSplitTorus.1.1 (splitComponentCentralCharacter a ha ω) hopen).mp
      (D.splitComponentCentralCharacter_realPart_eq_zero
        p l r hp hl hr hmul ha htemp ω hω) t

omit [IsAffineHom M.X.hom] in
/-- A unitary central-character datum for the actual quotient, using the
explicit structural compactness of the full scheme center modulo the split
component. No temperedness of the quotient is required. -/
def unitaryCentralCharacter
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π)
    (hcompact : CenterSplitComponentCompactness M hl.isConnectedReductive A a ha) :
    letI := leviPointTopology l hl
    UnitaryCentralCharacter D.quotient.representation := by
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : D.quotient.representation.IsIrreducible := D.irreducible
  have : Nontrivial D.quotient :=
    IsSimpleModule.nontrivial ℂ[rationalPoints M] D.quotient.representation.asModule
  let ω := D.centralCharacter p l r hp hl hr hmul ha htemp
  have hω : D.quotient.HasCentralCharacter ω :=
    (D.centralCharacter_spec p l r hp hl hr hmul ha htemp).2
  exact unitaryCentralCharacterOfSplitComponent hl.isConnectedReductive
    D.quotient ω A a ha hcompact hω
    (D.splitComponentCentralCharacter_norm_eq_one p l r hp hl hr hmul ha htemp ω hω)

end UnitaryJacquetIrreducibleQuotientData

end Langlands.Aubert.General.RepresentedParabolic
