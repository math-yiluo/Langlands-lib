import Langlands.BruhatTits.SpecialCompact.JointBasisReductionStatement
import Langlands.GroupScheme.Rational.CentralizerRootSupport

/-!
# Proof of the reduction of the joint special-compact existence target

Rebase a valid assignment at the given torus, take a special vertex of its apartment, and
read off the compact, Levi, basis, Iwasawa and Renard Cartan conclusions from the
conditional statements. The Levi Iwasawa products come from the Levi compact statement and
the Iwasawa statement for the Levi data, transported along the torus equality.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan

namespace Langlands.BruhatTits.SpecialCompact

section Transport

variable {F : Type u} [Field F]

/-- A generic cocharacter of the ambient torus stays generic for the same torus in an actual
standard Levi: every relative root of the Levi is an ambient relative root. -/
theorem isGenericCocharacter_leviTorusHom {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν) (J : Set (characterLattice S))
    [IsAffineHom (Standard.leviScheme i ν J).X.hom] :
    IsGenericCocharacter (Standard.leviTorusHom i ν J) ν := fun α hα =>
  hν α (relativeRoots_subset_of_factor (Standard.isRepresentedBy_leviHom i ν J) _
    (Standard.leviTorusHom_comp i ν J) hα)

/-- Iwasawa products for every generic cocharacter of a torus `i'` give them for a torus `i`
equal to `i'` up to the equality of their sources. -/
theorem parabolicPointProductFamily_of_heq {M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom M.X.hom] {S S' : CommGroupScheme (Spec (CommRingCat.of F))} (hS : S' = S)
    {i' : S'.toGrp ⟶ M} {i : S.toGrp ⟶ M} (hi : HEq i' i) (K : Subgroup (rationalPoints M))
    (h : ∀ ν' : cocharacterLattice S', IsGenericCocharacter i' ν' →
      Iwasawa.ParabolicPointProductFamily i' ν' K)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν) :
    Iwasawa.ParabolicPointProductFamily i ν K := by
  subst hS
  obtain rfl := eq_of_heq hi
  exact h ν hν

end Transport

/-- The joint conclusion at the given torus from the conclusions at every special vertex of
building data whose torus is the given one. -/
theorem joint_of_valuationBuildingData {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (V : ValuationBuildingData G)
    (hx : ∃ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x)
    (hB : ∀ ν : cocharacterLattice V.S, IsGenericCocharacter V.i ν →
      ∀ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x →
        SpecialCompactProperties F V.i ν (V.apartment.specialCompactSubgroup x) ∧
          SpecialLeviInheritance F V.isMaximalSplitTorus ν V.apartment x ∧
          SimultaneousStandardBasisAt V.i ν (V.apartment.specialCompactSubgroup x))
    (hI : ∀ ν : cocharacterLattice V.S, IsGenericCocharacter V.i ν →
      ∀ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x →
        Iwasawa.ParabolicPointProductFamily V.i ν (V.apartment.specialCompactSubgroup x))
    (hC : ∀ ν : cocharacterLattice V.S, IsGenericCocharacter V.i ν →
      ∀ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x →
        Plancherel.RenardCartan.SpecialCompactRenardComparison V.apartment x ν
            V.centralizer.j V.centralizer.s V.centralizer.bijective ∧
          Plancherel.RenardCartan.SpecialCompactStandardLeviCompatibility V.apartment x ν
            V.centralizer.s V.centralizer.bijective V.centralizer.j)
    (hL : ∀ ν : cocharacterLattice V.S, IsGenericCocharacter V.i ν →
      ∀ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x →
        ∀ J : Set (characterLattice V.S), J ⊆ simpleRelativeRoots V.i ν →
          haveI : IsAffineHom (Standard.leviScheme V.i ν J).X.hom :=
            (Standard.isClosedSubgroup_leviHom V.i ν J).isAffineHom
          Iwasawa.ParabolicPointProductFamily (Standard.leviTorusHom V.i ν J) ν
            (V.apartment.specialCompactLeviSubgroup ν J x))
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hS : V.S = S) (hVi : HEq V.i i)
    (ν : cocharacterLattice S) :
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
        (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G)
        (s : S.toGrp ⟶ Z),
        IsClosedSubgroup j ∧
          (torusCentralizer i).IsRepresentedBy j ∧
          s ≫ j = i ∧
          ∃ h : Function.Bijective (restrictionEvaluation s),
            D.IsSpecialApartmentVertex x ∧
              SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
              SpecialLeviInheritance F hi ν D x ∧
              Iwasawa.ParabolicPointProductFamily i ν (D.specialCompactSubgroup x) ∧
              Langlands.Plancherel.RenardCartan.SpecialCompactRenardComparison
                D x ν j s h ∧
              (∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
                haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
                  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
                Iwasawa.ParabolicPointProductFamily
                  (Standard.leviTorusHom i ν J) ν
                  (D.specialCompactLeviSubgroup ν J x)) ∧
              Langlands.Plancherel.RenardCartan.SpecialCompactStandardLeviCompatibility
                D x ν s h j ∧
              SimultaneousStandardBasisAt i ν (D.specialCompactSubgroup x) := by
  intro hν
  obtain ⟨_, SV, iV, hiV, AV, CV, _⟩ := V
  subst hS
  obtain rfl := eq_of_heq hVi
  obtain ⟨x, hx⟩ := hx
  obtain ⟨hP, hInh, hBas⟩ := hB ν hν x hx
  obtain ⟨hRC, hLC⟩ := hC ν hν x hx
  exact ⟨AV, x, CV.Z, CV.j, CV.s, CV.isClosedSubgroup, CV.isRepresentedBy, CV.comp_eq,
    CV.bijective, hx, hP, hInh, hI ν hν x hx, hRC, hL ν hν x hx, hLC, hBas⟩

/-- The joint special-compact existence target follows from a valid assignment and the
conditional statements of `JointBasisReductionStatement`. -/
theorem jointBasisReduction : JointBasisReductionStatement.{u} := by
  rintro ⟨𝔅₀, h𝔅₀⟩ hT hSV hBasis hIw hCartan hLM F _ _ _ _ G hG S i hi ν
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨𝔅, h𝔅, hS, hVi⟩ := hT 𝔅₀ h𝔅₀ F G hG S i hi
  have hA : 𝔅.IsAvailableFor F G hG := h𝔅.isAvailableFor
  refine joint_of_valuationBuildingData (𝔅.datum F G hG).base.toValuationBuildingData
    (hSV F G hG 𝔅 hA) (hBasis F G hG 𝔅 h𝔅)
    (fun ν hν x hx => ((hIw F G hG 𝔅 hA ν hν).1 x hx).2.2.1)
    (hCartan F G hG 𝔅 hA) ?_ hi hS hVi ν
  intro ν hν x hx J hJ
  have : IsAffineHom (Standard.leviScheme (𝔅.datum F G hG).base.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom _ ν J).isAffineHom
  obtain ⟨hM, 𝔅M, hAM, hSM, hiM, xM, hxM, hK⟩ := hLM F G hG 𝔅 h𝔅 ν hν x hx J hJ
  rw [← hK]
  exact parabolicPointProductFamily_of_heq hSM hiM _
    (fun ν' hν' => ((hIw F _ hM 𝔅M hAM ν' hν').1 xM hxM).2.2.1) ν
    (isGenericCocharacter_leviTorusHom hν J)

end Langlands.BruhatTits.SpecialCompact
