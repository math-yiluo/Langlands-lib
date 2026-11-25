/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.FixedPullbackDegreeZeroDescent

/-! # Degree reduction for etale limit cohomology

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero limit cohomology classes descend to a stage.

Source: Stacks Project, Etale Cohomology, Tag 09YQ, the degree-zero part of
Cohomology on Sites Tag 09YP, and Sites Tag 09YN.
(blueprint: lem-weil-pbc-etale-limit-cohomology-degree-zero-descent).

Proof: Projections of the scheme limit are affine, so the limit is qcqs.
Sections of the filtered sheaf colimit on this fixed qcqs scheme form the
filtered colimit of stage sections. Apply the existing filtered-cohomology
colimit theorem in degree zero and transport its image cocone through the natural
isomorphism with global sections. H.equiv₀ and its naturality represent the given class by
some z in H^0(G_i). Transport z through eG_i and apply fixed-pullback degree-zero
descent to obtain a class x of the pullback of F_i at a later stage j.
Map x by φ_(i,j) to H^0(F_j), then by eH_j inverse to H_j. Naturality of
cohomologyMap, the descent equation, hG and the cocone equation for L identify
its image in H^0(L.pt) with the original class. Finally hB and injectivity of
eB give the requested equation in B.pt. The coefficient coherence and H-arrow
hypotheses are retained unchanged; the supplied functors already encode their
coherence, so the representative argument uses hG and hB directly.
-/
theorem etale_limit_cohomology_degree_zero_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) 0))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) 0) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt 0))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0)) :
    ∀ y : B.pt, ∃ (i : I) (x : H.obj i), (B.ι.app i).hom x = y := by
  classical
  have _ := hidentity
  have _ := hcomposition
  have _ := hH
  have hAffine (i : Iᵒᵖ) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let i₀ : I := Classical.arbitrary I
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  let Γ := Sheaf.Γ c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (0 : ℤ)
  let e :
      DerivedCategory.singleFunctor (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
        0 ⋙ cohomology AddCommGrpCat.{u + 1} c.pt (0 : ℤ) ≅ Γ :=
    Functor.isoWhiskerLeft
        (DerivedCategory.Plus.singleFunctor
          (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
        (Functor.isoWhiskerRight Γ.rightDerivedFunctorPlusCompatibility.symm H₀) ≪≫
      Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
      Γ.rightDerivedZeroIsoSelf
  have hΓ : IsColimit (Γ.mapCocone L) := IsColimit.mapCoconeEquiv e
    (Scheme.etaleCohomology_isColimit_of_isFiltered c.pt hL 0).some
  let E := (sheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (⊤_ c.pt.Etale))
  have hE : IsColimit (E.mapCocone L) :=
    IsColimit.mapCoconeEquiv
      (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) hΓ
  intro y
  let s := Sheaf.H.equiv₀ L.pt terminalIsTerminal (eB.hom y)
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨i, t, ht⟩ := Concrete.isColimit_exists_rep (G ⋙ E) hE s
  let z := (Sheaf.H.equiv₀ (G.obj i) terminalIsTerminal).symm t
  have hz : Sheaf.H.map (L.ι.app i) 0 z = eB.hom y := by
    apply (Sheaf.H.equiv₀ L.pt terminalIsTerminal).injective
    erw [← Sheaf.H.equiv₀_naturality terminalIsTerminal (L.ι.app i) z]
    dsimp only [z]
    rw [AddEquiv.apply_symm_apply]
    change ((L.ι.app i).hom.app (op (⊤_ c.pt.Etale))) t = s at ht
    exact ht
  let z' := Sheaf.H.map (eG i).hom 0 z
  obtain ⟨j, f, x, hx⟩ := fixed_pullback_degree_zero_descent D c hc i (F i) z'
  refine ⟨j, (eH j).inv (Sheaf.H.map (φ f) 0 x), ?_⟩
  apply (ConcreteCategory.bijective_of_isIso eB.hom).1
  have hBj := ConcreteCategory.congr_hom (hB j) ((eH j).inv (Sheaf.H.map (φ f) 0 x))
  have heH := ConcreteCategory.congr_hom (eH j).inv_hom_id (Sheaf.H.map (φ f) 0 x)
  simp only [ConcreteCategory.comp_apply] at hBj heH
  change eB.hom (B.ι.app j ((eH j).inv (Sheaf.H.map (φ f) 0 x))) = eB.hom y
  erw [hBj, heH]
  change Sheaf.H.map ((eG j).inv ≫ L.ι.app j) 0
    (cohomologyMap (c.π.app (op j)) (F j) 0 (Sheaf.H.map (φ f) 0 x)) = eB.hom y
  rw [cohomologyMap_map, hx]
  erw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  have hleg :
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫
        (eG j).inv ≫ L.ι.app j = (eG i).inv ≫ L.ι.app i := by
    have hw := L.w f
    rw [hG i j f] at hw
    have hwi := congrArg (fun a ↦ (eG i).inv ≫ a) hw
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hwi
  rw [hleg]
  dsimp only [z']
  erw [← Sheaf.H.map_comp_apply]
  simpa only [Functor.const_obj_obj, Iso.hom_inv_id_assoc] using hz


end AlgebraicGeometry.Etale
