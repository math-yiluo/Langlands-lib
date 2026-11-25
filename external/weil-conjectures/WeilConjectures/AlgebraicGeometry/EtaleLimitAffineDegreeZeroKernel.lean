/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleFixedAffineDegreeZeroKernel
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.Limits

/-! # The degree-zero affine continuity kernel

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
(blueprint: lem-weil-pbc-etale-limit-affine-degree-zero-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem hZeroColimit {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {G : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {L : Cocone G} (hL : IsColimit L) :
    Nonempty (IsColimit ((Sheaf.functorH X.smallEtaleTopology 0).mapCocone L)) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (0 : ℤ)
  let e :
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        0 ⋙ cohomology AddCommGrpCat.{u + 1} X (0 : ℤ) ≅ Γ :=
    Functor.isoWhiskerLeft
        (DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
        (Functor.isoWhiskerRight Γ.rightDerivedFunctorPlusCompatibility.symm H₀) ≪≫
      Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
      Γ.rightDerivedZeroIsoSelf
  have hΓ := IsColimit.mapCoconeEquiv e
    (Scheme.etaleCohomology_isColimit_of_isFiltered X hL 0).some
  have hE := IsColimit.mapCoconeEquiv
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) hΓ
  exact ⟨IsColimit.mapCoconeEquiv
    (Sheaf.functorHZeroIso X.smallEtaleTopology terminalIsTerminal).symm hE⟩

private theorem pullback_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (d : X ⟶ Z) (hd : d = a ≫ b)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b d hd).hom.app F) n
      (cohomologyMap d F n x) =
        cohomologyMap a ((upperStar AddCommGrpCat.{u + 1} b).obj F) n
          (cohomologyMap b F n x) := by
  subst d
  exact ((cohomologyPullbackFunctorial a b F n).2.1 x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Detection of zero for degree-zero affine-stage cohomology.

Source: Stacks Project, Tag 09YP, degree-zero case, using Sites Tag 09YN;
affine étale reduction in Tags 09YQ, 0EYL and 04HR.
(blueprint: lem-weil-pbc-etale-limit-affine-degree-zero-kernel).

Proof: Restrict to the cofinal upper tail of i. Present the affine étale sites
by the strictified colimit of 0EYL. Restriction from the small étale site is
an equivalence by 04HR. Both direct images evaluate on the same cartesian
base changes of affine objects. The resulting right-adjoint comparison induces
an inverse-image comparison compatible with adjunction units. Uniqueness of
this comparison gives its identity and composition coherence. Transport F, φ,
G and the colimit cocone L through these equivalences; equivalences preserve
colimits. The identity object of the affine scheme at i and its base changes
are terminal. The section comparison of 09YN at this object identifies the
limit sections with the filtered colimit of the stage sections. Degree-zero
Ext is sections via H.equiv₀; the cohomology pullback formula is the adjunction
unit, so the specified maps are exactly these section comparison maps.
A representative whose limit section is zero equals the zero representative
in this filtered colimit. Finite-stage detection of equality therefore gives
a later stage at which its transition is zero. The tail inclusion supplies the
arrow i → j in the original index category.

Edge cases: zero coefficients and the empty affine scheme have zero sections;
for a singleton index both comparisons are equivalences. No higher-degree
continuity or negative cohomology is used.
-/
theorem etale_limit_affine_degree_zero_kernel
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
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
    (i : I) (x : Sheaf.H (F i) 0)
    (hx : Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0
      (cohomologyMap (c.π.app (op i)) (F i) 0 x) = 0) :
    ∃ (j : I) (f : i ⟶ j),
      Sheaf.H.map (φ f) 0 (cohomologyMap (D.map f.op) (F i) 0 x) = 0 := by
  classical
  have _ := hidentity
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  obtain ⟨hC⟩ := hZeroColimit hL
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  let s : Sheaf.H (G.obj i) 0 :=
    Sheaf.H.map (eG i).inv 0 (cohomologyMap (c.π.app (op i)) (F i) 0 x)
  have hs : Sheaf.H.map (L.ι.app i) 0 s = 0 := by
    dsimp only [s]
    erw [← Sheaf.H.map_comp_apply]
    exact hx
  have hs' : Sheaf.H.map (L.ι.app i) 0 s = Sheaf.H.map (L.ι.app i) 0 0 := by
    simpa only [map_zero] using hs
  obtain ⟨j, f, g, hf⟩ := Concrete.isColimit_exists_of_rep_eq
    (G ⋙ Sheaf.functorH c.pt.smallEtaleTopology 0) hC s (0 : Sheaf.H (G.obj i) 0) hs'
  have hj : Sheaf.H.map (G.map f) 0 s = 0 := by
    change Sheaf.H.map (G.map f) 0 s = Sheaf.H.map (G.map g) 0 0 at hf
    erw [map_zero] at hf
    exact hf
  have hy : cohomologyMap (c.π.app (op j)) (F j) 0
      (Sheaf.H.map (φ f) 0 (cohomologyMap (D.map f.op) (F i) 0 x)) = 0 := by
    have he : (eG i).inv ≫ G.map f ≫ (eG j).hom =
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) := by
      rw [hG i j f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
    have ht : Sheaf.H.map (eG j).hom 0 (Sheaf.H.map (G.map f) 0 s) = 0 := by
      rw [hj, map_zero]
    have hp := pullback_comp (c.π.app (op j)) (D.map f.op) (c.π.app (op i))
      (c.w f.op).symm (F i) 0 x
    have hn := cohomologyMap_map (c.π.app (op j)) 0 (φ f)
      (cohomologyMap (D.map f.op) (F i) 0 x)
    dsimp only [s] at ht
    erw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, he,
      Sheaf.H.map_comp_apply] at ht
    erw [hp, ← hn] at ht
    exact ht
  obtain ⟨k, g, hg⟩ := fixed_affine_degree_zero_kernel D c hc j (F j)
    (Sheaf.H.map (φ f) 0 (cohomologyMap (D.map f.op) (F i) 0 x)) hy
  refine ⟨k, f ≫ g, ?_⟩
  rw [hcomposition, Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  rw [pullback_comp (D.map g.op) (D.map f.op) (D.map (f ≫ g).op)
    (D.map_comp g.op f.op) (F i) 0 x]
  erw [← cohomologyMap_map (D.map g.op) 0 (φ f), hg, map_zero]

end AlgebraicGeometry.Etale
