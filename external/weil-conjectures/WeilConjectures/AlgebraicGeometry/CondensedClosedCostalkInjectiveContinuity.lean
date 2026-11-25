/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity

/-! # Closed costalks of bounded injective filtered cocones -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance closedCostalkInjectiveContinuityHasZeroMorphisms
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

/-- The K-injective comparison for a right derived functor is natural.
Source: the right-derived unit and quotient comparison isomorphisms in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.
(auxiliary; not a blueprint node)

Proof: expand the comparison into its three isomorphisms. Naturality of the
quotient comparison treats the outer factors. Naturality of the derived unit,
cancelled against its invertible component at the source, treats the middle. -/
theorem rightDerivedObjQIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (H : A ⥤ B) [H.Additive] {K L : CochainComplex A ℤ}
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    H.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (H.rightDerivedFunctorObjQIso L).hom =
      (H.rightDerivedFunctorObjQIso K).hom ≫
        DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map f) := by
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv]
  erw [← Category.assoc, ← H.rightDerivedFunctor.map_comp,
    (DerivedCategory.quotientCompQhIso A).inv.naturality f,
    H.rightDerivedFunctor.map_comp, Category.assoc]
  have hu := H.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient A (.up ℤ)).map f)
  have hu' : H.rightDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f)) ≫
        inv (H.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient A (.up ℤ)).obj L)) =
      inv (H.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K)) ≫
      DerivedCategory.Qh.map ((H.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient A (.up ℤ)).map f)) := by
    apply (cancel_epi (H.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K))).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    erw [← hu, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rfl
  erw [reassoc_of% hu']
  erw [(DerivedCategory.quotientCompQhIso B).hom.naturality]
  simp only [Category.assoc]
  rfl

/-- Transfer derived continuity to a bounded injective cocone in abstract abelian categories,
so the cocone calculation does not repeatedly unfold concrete sheaf and module structures. -/
private theorem injectiveContinuity_of_derived
    {A B : Type*} [Category.{v} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    {I : Type*} [Category I] [IsFiltered I]
    [HasColimitsOfShape I A] [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (H : A ⥤ B) [H.Additive] (J : I ⥤ CochainComplex A ℤ) (c : Cocone J) (a : ℤ)
    (hJ : ∀ s, (J.obj s).IsStrictlyGE a)
    (hJi : ∀ s r, Injective ((J.obj s).X r))
    (hc : c.pt.IsStrictlyGE a) (hci : ∀ r, Injective (c.pt.X r))
    (hq : QuasiIso (colimit.desc J c))
    (hcont : ∀ q : ℤ, IsIso (condensedContinuityComparison J a
      (DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q))) :
    QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)) := by
  classical
  have hJk (s : I) : (J.obj s).IsKInjective := by
    have := hJ s
    have := hJi s
    exact CochainComplex.isKInjective_of_injective (J.obj s) a
  have hck : c.pt.IsKInjective := by
    have := hc
    have := hci
    exact CochainComplex.isKInjective_of_injective c.pt a
  let d := condensedContinuityCocone J a
  have hd : IsColimit d := canonicalContinuityIsColimit J a hJ
  let g := hd.desc c
  have hg : colimit.desc J d ≫ g = colimit.desc J c := by
    apply colimit.hom_ext
    intro s
    simp only [colimit.ι_desc_assoc, colimit.ι_desc]
    exact hd.fac c s
  have hqd : IsIso (colimit.desc J d) := by
    change IsIso ((IsColimit.coconePointUniqueUpToIso (colimit.isColimit J) hd).hom)
    infer_instance
  have hqg : QuasiIso g := by
    rw [← quasiIso_iff_comp_left (colimit.desc J d) g, hg]
    exact hq
  let P := J ⋙ H.mapHomologicalComplex (.up ℤ)
  let e : J ⋙ DerivedCategory.Q ⋙ H.rightDerivedFunctor ≅ P ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun s ↦ H.rightDerivedFunctorObjQIso (J.obj s))
      (fun f ↦ rightDerivedObjQIso_naturality H (J.map f))
  let ε := H.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map g)) ≪≫
    H.rightDerivedFunctorObjQIso c.pt
  apply condensedContinuityComparison_representatives J a H.rightDerivedFunctor
    hcont P ((H.mapHomologicalComplex (.up ℤ)).obj c.pt) e ε
    ((H.mapHomologicalComplex (.up ℤ)).mapCocone c).ι
  intro s
  dsimp only [e, NatIso.ofComponents_hom_app, ε, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom]
  rw [← H.rightDerivedFunctor.map_comp_assoc, ← DerivedCategory.Q.map_comp,
    hd.fac c s]
  exact (rightDerivedObjQIso_naturality H (K := J.obj s) (L := c.pt) (c.ι.app s)).symm

set_option synthInstance.maxHeartbeats 100000 in
-- Internal module colimit inference needs a larger typeclass search budget.
set_option synthInstance.maxSize 4096 in
/-- A closed exceptional inverse image preserves a filtered quasi-colimit cocone
of injective complexes with a common lower bound.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), closed costalk step, using (3.4)
and Lemma 5.3(1).
(auxiliary; not a blueprint node)

Proof: bounded-below injective complexes are K-injective. The right-derived unit
therefore gives natural isomorphisms RH(QJ_s) ≅ Q(HJ_s), and the same comparison
at c.pt. The good-truncated cocone of J is colimiting because its truncation
projections are invertible under the strict lower bound. Its universal map g to
c.pt is a quasi-isomorphism: precomposition with the isomorphism from colim J
identifies it with the assumed quasi-isomorphism. Apply derived closed-costalk
continuity in every degree. Identify the vertex by RH(Qg) and the K-injective
comparison at c.pt. Naturality gives exactly the cocone-leg equation required by
the representative comparison theorem, which proves that the canonical colimit
map of termwise H images is a quasi-isomorphism. This includes empty closed or
open parts and zero complexes. -/
theorem condensed_closed_costalk_injective_continuity
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    [H.Additive] (adj : CondensedRing.lowerStar Λ i ⊣ H)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (J : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (c : Cocone J) (a : ℤ)
    (hJ : ∀ s, (J.obj s).IsStrictlyGE a)
    (hJi : ∀ s r, Injective ((J.obj s).X r))
    (hc : c.pt.IsStrictlyGE a) (hci : ∀ r, Injective (c.pt.X r))
    (hq : QuasiIso (colimit.desc J c)) :
    QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)) := by
  -- Cache the module colimits before specializing the abstract continuity argument.
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let B := Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfShape I A := inferInstance
  have : HasColimitsOfShape I B := inferInstance
  have : HasExactColimitsOfShape I B := inferInstance
  exact injectiveContinuity_of_derived H J c a hJ hJi hc hci hq
    (fun q ↦ condensed_closed_costalk_derived_continuity T Λ i H adj J a hJ q)

end AlgebraicGeometry.ProEtale
