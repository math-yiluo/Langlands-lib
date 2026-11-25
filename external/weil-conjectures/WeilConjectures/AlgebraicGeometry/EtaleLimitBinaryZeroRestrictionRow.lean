/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.StageCohomologyComparison
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.EtaleLimitSingleOpenComparison
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Filtered.Final

/-! # Native restricted cohomology rows

Source: Stacks Project, Tags 09YQ and 0A50.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem biprod_prod_fst (A B : AddCommGrpCat.{u + 1}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.fst A B) = biprod.fst := by
  rw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc]

private theorem biprod_prod_snd (A B : AddCommGrpCat.{u + 1}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
      AddCommGrpCat.ofHom (AddMonoidHom.snd A B) = biprod.snd := by
  rw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc]

set_option linter.unusedVariables false in
-- The dependent scheme and sheaf identifications exhaust the default elaboration budget.
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero restriction row on a cofinal tail.

Source: Stacks Project, Tag 09YQ, coherent-system construction, and Tag 0A50,
initial injectivity and naturality of restriction.
(blueprint: lem-weil-pbc-etale-limit-binary-zero-restriction-row).

Proof: Take J to be the directed tail above i₀ and t its final inclusion. Transfer
U and V to opens of D(i₀) along e and pull these opens back at every stage of J.
Their union is the whole stage: e lands in U ∪ V. At the limit their inverse images
are precisely WU and WV. Restrict the coefficient system using upperStarComp;
the supplied identity and composition equations give the restricted coherence.
Inverse image is a left adjoint, so the restrictions of L are sheaf colimits.
The restricted scheme cones are limits by isLimitOpensCone. Their transitions
and projections are affine. Compactness pulls back along affine maps, and open
subschemes of quasi-separated stages are quasi-separated. Thus each restricted
system meets the system certificate constructor, with initial stage isomorphic
to U.toScheme or V.toScheme. Apply the canonical cohomology diagram construction
in degree zero to each restricted system. Define K₄ as their product diagram and
r as the pair of actual restrictions, conjugated by eH. Pullback and coefficient
naturality prove r natural. Initial Mayer--Vietoris injectivity proves every r.app j
injective. Finite-product preservation for filtered colimits identifies its colimit
with the product of the two restricted colimits. Assemble their system certificates
using prod, then transport by that identification using iso and comp, obtaining v₄.
The canonical cocone equations and hB prove the stated equality on every stage leg.
This constructs only the restriction row; no left zero terms or colimit square is
asserted. Empty and coincident opens still cover, so injectivity remains valid. -/
theorem etale_limit_binary_zero_restriction_row
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
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
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0))
    (i₀ : I) (e : D.obj (op i₀) ≅ (U ⊔ V).toScheme) :
    let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
    let B₄ := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) 0 ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) 0)
    let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt 0).prod (cohomologyMap WV.ι L.pt 0)).comp eB.hom.hom)
    ∃ (J : Type u) (order : Preorder J),
      letI := order
      ∃ (directed : IsDirected J (· ≤ ·)) (nonempty : Nonempty J),
      letI := directed
      letI := nonempty
      ∃ (t : J ⥤ I) (ht : t.Final),
      ∃ (K₄ : J ⥤ AddCommGrpCat.{u + 1}) (r : t ⋙ H ⟶ K₄)
        (v₄ : colimit K₄ ⟶ B₄),
        (∀ j, Function.Injective (r.app j)) ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₄ ∧
        (∀ j, r.app j ≫ colimit.ι K₄ j ≫ v₄ = B.ι.app (t.obj j) ≫ r') := by
  classical
  dsimp only
  let J := Set.Ici i₀
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := directed_of (· ≤ ·) a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let : IsFiltered J := isFiltered_of_directed_le_nonempty J
  let t : J ⥤ I := (show Monotone (fun j : J ↦ j.val) from fun _ _ h ↦ h).functor
  have ht : t.Final := by
    apply Functor.final_of_exists_of_isFiltered
    · intro i
      obtain ⟨k, hi, h₀⟩ := directed_of (· ≤ ·) i i₀
      exact ⟨⟨k, h₀⟩, ⟨homOfLE hi⟩⟩
    · intro i j f g
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  let allowed : Scheme.{u} → Prop :=
    fun S ↦ S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme
  obtain ⟨KU, eKU, rU, vU, hrU, hvU, hsqU⟩ :=
    etale_limit_single_open_comparison X (U ⊔ V) U hU le_sup_left D c hc F φ
      hidentity hcomposition G eG hG L hL H eH hH B eB hB i₀ e allowed (Or.inl rfl)
  obtain ⟨KV, eKV, rV, vV, hrV, hvV, hsqV⟩ :=
    etale_limit_single_open_comparison X (U ⊔ V) V hV le_sup_right D c hc F φ
      hidentity hcomposition G eG hG L hL H eH hH B eB hB i₀ e allowed
        (Or.inr (Or.inl rfl))
  let K := KU ⊞ KV
  let r : t ⋙ H ⟶ K := biprod.lift rU rV
  let cl : (J ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1} := colim
  let : PreservesBinaryBiproduct KU KV cl :=
    preservesBinaryBiproduct_of_preservesBiproduct cl KU KV
  let ep : colimit K ≅ AddCommGrpCat.of
      (↑(colimit KU) × ↑(colimit KV)) :=
    (cl.mapBiprod KU KV) ≪≫ AddCommGrpCat.biprodIsoProd (colimit KU) (colimit KV)
  let v := ep.hom ≫ AddCommGrpCat.ofHom (vU.hom.prodMap vV.hom)
  refine ⟨J, inferInstance, inferInstance, inferInstance, t, ht, K, r, v, ?_, ?_, ?_⟩
  · intro j x y hxy
    have hUeq : rU.app j x = rU.app j y := by
      have h := congrArg ((biprod.fst : K ⟶ KU).app j) hxy
      change ((r ≫ biprod.fst).app j) x = ((r ≫ biprod.fst).app j) y at h
      simpa only [r, biprod.lift_fst] using h
    have hVeq : rV.app j x = rV.app j y := by
      have h := congrArg ((biprod.snd : K ⟶ KV).app j) hxy
      change ((r ≫ biprod.snd).app j) x = ((r ≫ biprod.snd).app j) y at h
      simpa only [r, biprod.lift_snd] using h
    let g := D.map (homOfLE j.property).op ≫ e.hom ≫ (U ⊔ V).ι
    have hcover : (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) = ⊤ := by
      rw [← Scheme.Hom.preimage_sup]
      simp only [g, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
        Scheme.Hom.preimage_top]
    obtain ⟨δX, δY, hinj, _⟩ :=
      etale_mayerVietoris_connecting_pullback (𝟙 _) (g ⁻¹ᵁ U) (g ⁻¹ᵁ V)
        hcover (F j.val)
    apply (eH j.val).addCommGroupIsoToAddEquiv.injective
    apply hinj
    apply Prod.ext
    · have h := congrArg (fun z ↦ (eKU j).hom z) hUeq
      change (rU.app j ≫ (eKU j).hom) x = (rU.app j ≫ (eKU j).hom) y at h
      rw [hrU] at h
      exact h
    · have h := congrArg (fun z ↦ (eKV j).hom z) hVeq
      change (rV.app j ≫ (eKV j).hom) x = (rV.app j ≫ (eKV j).hom) y at h
      rw [hrV] at h
      exact h
  · exact StageCohomologyComparison.comp (StageCohomologyComparison.iso ep)
      (StageCohomologyComparison.prod hvU hvV)
  · intro j
    have hpU : ep.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        colimMap (biprod.fst : K ⟶ KU) := by
      simp only [ep, Iso.trans_hom, Category.assoc, biprod_prod_fst]
      rw [Functor.mapBiprod_hom]
      exact biprod.lift_fst _ _
    have hpV : ep.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        colimMap (biprod.snd : K ⟶ KV) := by
      simp only [ep, Iso.trans_hom, Category.assoc, biprod_prod_snd]
      rw [Functor.mapBiprod_hom]
      exact biprod.lift_snd _ _
    have hvfst : v ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        colimMap (biprod.fst : K ⟶ KU) ≫ vU := by
      have h : AddCommGrpCat.ofHom (vU.hom.prodMap vV.hom) ≫
          AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
          AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) ≫ vU := rfl
      exact (Category.assoc ep.hom _ _).trans
        ((congrArg (fun f ↦ ep.hom ≫ f) h).trans
          ((Category.assoc ep.hom _ vU).symm.trans
            (congrArg (fun f ↦ f ≫ vU) hpU)))
    have hvsnd : v ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        colimMap (biprod.snd : K ⟶ KV) ≫ vV := by
      have h : AddCommGrpCat.ofHom (vU.hom.prodMap vV.hom) ≫
          AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
          AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) ≫ vV := rfl
      exact (Category.assoc ep.hom _ _).trans
        ((congrArg (fun f ↦ ep.hom ≫ f) h).trans
          ((Category.assoc ep.hom _ vV).symm.trans
            (congrArg (fun f ↦ f ≫ vV) hpV)))
    have hu : r.app j ≫ colimit.ι K j ≫ v ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        rU.app j ≫ colimit.ι KU j ≫ vU := by
      rw [hvfst, ← Category.assoc (colimit.ι K j), colimMap_eq, colimit.ι_map]
      simp only [← Category.assoc]
      rw [← NatTrans.comp_app]
      simp only [r, biprod.lift_fst]
    have hv : r.app j ≫ colimit.ι K j ≫ v ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        rV.app j ≫ colimit.ι KV j ≫ vV := by
      rw [hvsnd, ← Category.assoc (colimit.ι K j), colimMap_eq, colimit.ι_map]
      simp only [← Category.assoc]
      rw [← NatTrans.comp_app]
      simp only [r, biprod.lift_snd]
    rw [hsqU] at hu
    rw [hsqV] at hv
    ext1
    apply AddMonoidHom.ext
    intro x
    exact Prod.ext (congrArg (fun f ↦ f x) hu) (congrArg (fun f ↦ f x) hv)


end AlgebraicGeometry.Etale
