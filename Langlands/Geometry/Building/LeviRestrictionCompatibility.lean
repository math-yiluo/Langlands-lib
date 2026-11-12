import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.BruhatTits.SpecialCompact.LeviValuationRestriction
import Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction
import Langlands.Geometry.Building.CrossTorusApartmentComparison
import Langlands.GroupScheme.Derived.SemisimpleReflectionReduction
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Compatibility of a prescribed Levi restriction class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

section RestrictionClass

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} {iM : S.toGrp ⟶ M}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    {ω : Fˣ → ℝ} {D : KPApartmentData i ω} {DM : KPApartmentData iM ω}
    {j : M ⟶ G}

/-- One restriction pair determines the whole Levi equipollence class. -/
theorem exists_leviRestriction_of_pair
    (h : ∃ (x : D.Apartment) (xM : DM.Apartment), IsLeviRestriction j x xM)
    (yM : DM.Apartment) : ∃ y : D.Apartment, IsLeviRestriction j y yM := by
  obtain ⟨x, xM, hres⟩ := h
  obtain ⟨v, hv⟩ := DM.equipollent_of_mem xM.mem yM.mem
  refine ⟨⟨v +ᵥ x.val, D.vadd_mem x.mem v⟩, ?_⟩
  intro a ha m
  change yM.val a m = (v +ᵥ x.val) a (rationalPoints.map j m)
  rw [hv]
  simp only [RootFunctionFamily.vadd_apply, hres a ha m]

end RestrictionClass

section PrescribedClass

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ω : Fˣ → ℝ} (D : KPApartmentData i ω) (DM : KPApartmentData iM ω)

/-- One restriction pair identifies any prescribed class with the constructed restriction. -/
theorem eq_leviRestrictedApartmentData_of_pair
    (h : ∃ (x : D.Apartment) (xM : DM.Apartment), IsLeviRestriction j x xM) :
    DM = leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D := by
  obtain ⟨x, xM, hres⟩ := h
  have hx : xM.val = leviRestrictedRootFunctionFamily iM j x.val := by
    apply RootFunctionFamily.ext
    intro a m
    by_cases ha : a ∈ relativeRoots iM
    · rw [leviRestrictedRootFunctionFamily_apply iM j x.val a ha]
      exact hres a ha m
    · rw [leviRestrictedRootFunctionFamily_apply_not_mem iM j x.val a ha]
      exact xM.isValuation.eq_top_of_not_mem_roots a ha m
  apply KPApartmentData.eq_of_common_mem xM.mem
  exact ⟨x.val, x.mem, hx.symm⟩

end PrescribedClass

section SemisimpleLevi

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)

include hS hcomp hj

/-- A semisimple same-torus Levi has no nonzero defining central cocharacter. -/
theorem cocharacter_eq_zero_of_isSemisimple_levi
    (hiM : IsClosedSubgroup iM) (hM : IsSemisimple M) : ζ = 0 := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  exact hM.cocharacter_eq_zero_of_annihilates_relativeRoots hS hiM ζ
    (fun a ha => (hroots ▸ ha).2)

/-- A semisimple same-torus Levi inclusion is the homomorphism of an isomorphism. -/
theorem exists_leviIso_of_isSemisimple
    (hiM : IsClosedSubgroup iM) (hM : IsSemisimple M) :
    ∃ e : M ≅ G, e.hom = j := by
  have hzero := cocharacter_eq_zero_of_isSemisimple_levi hS i iM j hcomp ζ hj hiM hM
  have htop : (⊤ : SubgroupFunctor G).IsRepresentedBy j := by
    simpa only [hzero, groupHom_zero_comp_eq_trivialCocharacter,
      Dynamic.centralizer_trivialCocharacter] using hj
  exact ⟨htop.topIso, htop.topIso_hom⟩

/-- In particular the literal semisimple Levi inclusion is an isomorphism. -/
theorem isIso_leviHom_of_isSemisimple
    (hiM : IsClosedSubgroup iM) (hM : IsSemisimple M) : IsIso j := by
  obtain ⟨e, he⟩ := exists_leviIso_of_isSemisimple hS i iM j hcomp ζ hj hiM hM
  rw [← he]
  infer_instance

end SemisimpleLevi


section Omega

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    {D : KPApartmentData i (localFieldOrder F)}
    {DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)}
    {C : CentralizerDatum i} (CM : CentralizerDatum (Standard.leviTorusHom i ν J))

/-- The whole restricted class satisfies V6 for any actual Levi centralizer datum. -/
theorem isOmegaCompatible_standardLevi_of_pair
    (h : ∃ (x : D.Apartment) (xM : DM.Apartment),
      IsLeviRestriction (Standard.leviHom i ν J) x xM)
    (hD : D.IsOmegaCompatible C) : DM.IsOmegaCompatible CM := by
  exact (Langlands.Plancherel.RenardCartan.isOmegaCompatible_standardLevi_of_restriction
    i C ν J D DM hD (exists_leviRestriction_of_pair h)).of_centralizerDatum CM

end Omega

end Langlands.Geometry.Building
