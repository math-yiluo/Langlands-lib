import Langlands.Geometry.Building.LeviApartmentRestrictionStatement
import Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction
import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof

/-! # Proof of restriction of an apartment to a standard Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

section Fibres

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    {i : S.toGrp ⟶ G} {iM : S.toGrp ⟶ M}
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    {ω : Fˣ → ℝ} {D : KPApartmentData i ω} {DM : KPApartmentData iM ω}
    {j : M ⟶ G} {x x' : D.Apartment} {xM xM' : DM.Apartment}

/-- Any two restriction pairs carry a translation of ambient valuations to the
same translation of the restricted valuations. -/
theorem leviRestriction_val_eq_vadd
    (h : IsLeviRestriction j x xM) (h' : IsLeviRestriction j x' xM')
    {v : V S} (hv : x'.val = v +ᵥ x.val) :
    xM'.val = v +ᵥ xM.val := by
  apply RootFunctionFamily.ext
  intro a m
  by_cases ha : a ∈ relativeRoots iM
  · calc
      xM'.val a m = x'.val a (rationalPoints.map j m) := h' a ha m
      _ = (v +ᵥ x.val) a (rationalPoints.map j m) := by rw [hv]
      _ = (v +ᵥ xM.val) a m := by
        simp only [RootFunctionFamily.vadd_apply, h a ha m]
  · rw [xM'.isValuation.eq_top_of_not_mem_roots a ha m,
      RootFunctionFamily.vadd_apply,
      xM.isValuation.eq_top_of_not_mem_roots a ha m, WithTop.top_add]

/-- The fibres of restriction are the translations annihilated by every Levi root. -/
theorem leviRestriction_eq_iff_exists_vadd
    (h : IsLeviRestriction j x xM) (h' : IsLeviRestriction j x' xM') :
    xM = xM' ↔ ∃ v : V S, x'.val = v +ᵥ x.val ∧
      ∀ a ∈ relativeRoots iM, eval S a v = 0 := by
  constructor
  · intro heq
    obtain ⟨v, hv⟩ := D.equipollent_of_mem x.mem x'.mem
    refine ⟨v, hv, mem_rootAnnihilator.1
      (xM.isValuation.vadd_eq_self_iff.1 ?_)⟩
    rw [← leviRestriction_val_eq_vadd h h' hv, ← heq]
  · rintro ⟨v, hv, hzero⟩
    apply KPApartmentData.Apartment.ext
    exact ((leviRestriction_val_eq_vadd h h' hv).trans
      (xM.isValuation.vadd_eq_self_iff.2 (mem_rootAnnihilator.2 hzero))).symm

end Fibres

/-- KP Lemma 6.7.1 (1)–(4) for the actual standard Levi at the same maximal split torus. -/
theorem leviApartmentRestriction : LeviApartmentRestrictionStatement.{u} := by
  intro F _ _ _ _ G hG S i hi ν hν J hJ D
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  have hiM := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have : Mono (Standard.leviTorusHom i ν J).hom.hom.left := hiM.isSplitSubtorus.mono
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Smooth (Standard.leviScheme i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G hG S i hi ν hν J hJ).1.smooth
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨ζ, hζ⟩ :=
    StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer hG hS i ν J
  have hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.leviHom i ν J) := hζ ▸ Standard.isRepresentedBy_leviHom i ν J
  let DM := leviRestrictedApartmentData hS i (Standard.leviTorusHom i ν J)
    (Standard.leviHom i ν J) (Standard.leviTorusHom_comp i ν J) ζ hj
    (Standard.isClosedSubgroup_leviHom i ν J) hG hi D
  let p : D.Apartment → DM.Apartment :=
    leviApartmentProjection hS i (Standard.leviTorusHom i ν J)
      (Standard.leviHom i ν J) (Standard.leviTorusHom_comp i ν J) ζ hj
      (Standard.isClosedSubgroup_leviHom i ν J) hG hi D
  have hp : ∀ x, IsLeviRestriction (Standard.leviHom i ν J) x (p x) :=
    isLeviRestriction_leviApartmentProjection hS i (Standard.leviTorusHom i ν J)
      (Standard.leviHom i ν J) (Standard.leviTorusHom_comp i ν J) ζ hj
      (Standard.isClosedSubgroup_leviHom i ν J) hG hi D
  have hsurj : Function.Surjective p :=
    leviApartmentProjection_surjective hS i (Standard.leviTorusHom i ν J)
      (Standard.leviHom i ν J) (Standard.leviTorusHom_comp i ν J) ζ hj
      (Standard.isClosedSubgroup_leviHom i ν J) hG hi D
  refine ⟨DM, fun x => ⟨p x, hp x⟩, ?_, ?_⟩
  · intro xM
    obtain ⟨x, rfl⟩ := hsurj xM
    exact ⟨x, hp x⟩
  · intro x x' xM xM' h h'
    exact leviRestriction_eq_iff_exists_vadd h h'

end Langlands.Geometry.Building
