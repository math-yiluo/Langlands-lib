/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.AlgebraicGeometry.StageCohomologyComparison
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenComparisonCertificateDegree
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps
import Mathlib.CategoryTheory.Filtered.Final

/-! # Native restricted cohomology rows

Source: Stacks Project, Tags 09YQ and 0A50.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem product_cocone_certificate
    {J : Type u} [SmallCategory J]
    (allowed : Scheme.{u} → Prop) (KU KV : J ⥤ AddCommGrpCat.{u + 1})
    {A B : AddCommGrpCat.{u + 1}}
    (ιU : KU ⟶ (Functor.const J).obj A) (ιV : KV ⟶ (Functor.const J).obj B)
    (ι : KU ⊞ KV ⟶ (Functor.const J).obj (AddCommGrpCat.of (A × B)))
    (hf : ∀ j, ι.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (biprod.fst : KU ⊞ KV ⟶ KU).app j ≫ ιU.app j)
    (hg : ∀ j, ι.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (biprod.snd : KU ⊞ KV ⟶ KV).app j ≫ ιV.app j)
    (hU : StageCohomologyComparison allowed (colimit.desc KU (Cocone.mk A ιU)))
    (hV : StageCohomologyComparison allowed (colimit.desc KV (Cocone.mk B ιV))) :
    StageCohomologyComparison allowed (colimit.desc (KU ⊞ KV) (Cocone.mk _ ι)) := by
  let cl : (J ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1} := colim
  let : PreservesBinaryBiproduct KU KV cl :=
    preservesBinaryBiproduct_of_preservesBiproduct cl KU KV
  let ep : colimit (KU ⊞ KV) ≅ AddCommGrpCat.of
      (↑(colimit KU) × ↑(colimit KV)) :=
    (cl.mapBiprod KU KV) ≪≫ AddCommGrpCat.biprodIsoProd (colimit KU) (colimit KV)
  let v := ep.hom ≫ AddCommGrpCat.ofHom
    ((colimit.desc KU (Cocone.mk A ιU)).hom.prodMap (colimit.desc KV (Cocone.mk B ιV)).hom)
  have hpU : ep.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      colimMap (biprod.fst : KU ⊞ KV ⟶ KU) := by
    simp only [ep, Iso.trans_hom, Category.assoc]
    rw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc]
    rw [Functor.mapBiprod_hom]
    exact biprod.lift_fst _ _
  have hpV : ep.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      colimMap (biprod.snd : KU ⊞ KV ⟶ KV) := by
    simp only [ep, Iso.trans_hom, Category.assoc]
    rw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc]
    rw [Functor.mapBiprod_hom]
    exact biprod.lift_snd _ _
  have hvfst : v ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      colimMap (biprod.fst : KU ⊞ KV ⟶ KU) ≫ colimit.desc KU (Cocone.mk A ιU) := by
    have h : AddCommGrpCat.ofHom
        ((colimit.desc KU (Cocone.mk A ιU)).hom.prodMap (colimit.desc KV (Cocone.mk B ιV)).hom) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) ≫ colimit.desc KU (Cocone.mk A ιU) := rfl
    dsimp only [v]
    rw [Category.assoc, h, ← Category.assoc, hpU]
  have hvsnd : v ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      colimMap (biprod.snd : KU ⊞ KV ⟶ KV) ≫ colimit.desc KV (Cocone.mk B ιV) := by
    have h : AddCommGrpCat.ofHom
        ((colimit.desc KU (Cocone.mk A ιU)).hom.prodMap (colimit.desc KV (Cocone.mk B ιV)).hom) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) ≫ colimit.desc KV (Cocone.mk B ιV) := rfl
    dsimp only [v]
    rw [Category.assoc, h, ← Category.assoc, hpV]
  have heq : v = colimit.desc (KU ⊞ KV) (Cocone.mk _ ι) := by
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_desc]
    ext1
    apply AddMonoidHom.ext
    intro x
    apply Prod.ext
    · have h := congrArg (fun m ↦ colimit.ι (KU ⊞ KV) j ≫ m) hvfst
      simp only [ι_colimMap_assoc, colimit.ι_desc] at h
      have h' := hf j
      exact (congrArg (fun m ↦ m x) h).trans (congrArg (fun m ↦ m x) h').symm
    · have h := congrArg (fun m ↦ colimit.ι (KU ⊞ KV) j ≫ m) hvsnd
      simp only [ι_colimMap_assoc, colimit.ι_desc] at h
      have h' := hg j
      exact (congrArg (fun m ↦ m x) h).trans (congrArg (fun m ↦ m x) h').symm
  rw [← heq]
  exact StageCohomologyComparison.comp (StageCohomologyComparison.iso ep)
    (StageCohomologyComparison.prod hU hV)

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
/-- The positive-degree Mayer--Vietoris segment before descent of its squares.

Source: Stacks Project, Tag 09YQ, coherent-system construction, and Tag 0A50,
long exact sequence and coefficient naturality; pullback naturality of its construction.
(blueprint: lem-weil-pbc-etale-limit-binary-successor-cocone-segment).

Proof: Pass to the directed tail J above i₀ with final inclusion t. Transfer U,V
along e to the union stage and pull them back to each later stage and the limit.
These opens cover each stage. Restrict all coefficients and transition maps;
upperStarComp and the original coherence laws give coherent restricted systems.
The restricted cones are limits by isLimitOpensCone, with affine transitions.
Affine inverse images preserve compactness. Quasi-separatedness passes to open
subschemes, and the intersection is compact because D(i₀) is quasi-separated.
Inverse image preserves the sheaf colimit by its left adjoint property. Construct
canonical cohomology diagrams of the two opens and their intersection in degrees
q and q+1. Their specified initial stages are isomorphic to U, V and U ∩ V.
Take K₁ to be the degree-q product, K₂ the degree-q intersection, K₄ the degree-(q+1)
product, and the middle diagram to be t ⋙ H. Apply the functorial Mayer--Vietoris
sequence before evaluating on coefficients, so that its difference and boundary
maps are chosen simultaneously. Coefficient naturality and pullback naturality
make a,b,r natural. Exactness of the sequence gives both stage pairs and the bottom
pair. Its canonical comparison cocones give C₁,C₂ and v₄. The system certificate
constructor certifies the single factors; prod and iso/comp transport certify their
products and the specified cocones. Naturality of the sequence proves the three
stage-leg squares. For the middle square use hB to identify its actual leg with
pullback followed by the coefficient colimit leg. No equality on an entire colimit
is asserted here: those equalities require colimit.hom_ext and finality separately.
Zero factors for empty opens and diagonal/difference maps for coincident opens
satisfy the same naturality and exactness statements. -/
theorem etale_limit_binary_successor_cocone_segment
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
    (L : Cocone G) (hL : IsColimit L) (q : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (q + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (q + 1)) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (q + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (q + 1)))
    (i₀ : I) (e : D.obj (op i₀) ≅ (U ⊔ V).toScheme) :
    let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
    let B₄ := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) (q + 1) ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) (q + 1))
    let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt (q + 1)).prod
        (cohomologyMap WV.ι L.pt (q + 1))).comp eB.hom.hom)
    ∃ (J : Type u) (order : Preorder J),
      letI := order
      ∃ (directed : IsDirected J (· ≤ ·)) (nonempty : Nonempty J),
      letI := directed
      letI := nonempty
      ∃ (t : J ⥤ I) (ht : t.Final),
      ∃ (K₁ K₂ K₄ : J ⥤ AddCommGrpCat.{u + 1})
        (a : K₁ ⟶ K₂) (b : K₂ ⟶ t ⋙ H) (r : t ⋙ H ⟶ K₄)
        (C₁ : Cocone K₁) (C₂ : Cocone K₂)
        (a' : C₁.pt ⟶ C₂.pt) (b' : C₂.pt ⟶ B.pt)
        (v₄ : colimit K₄ ⟶ B₄),
        (∀ j, Function.Exact (a.app j) (b.app j)) ∧
        (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) (colimit.desc K₁ C₁) ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) (colimit.desc K₂ C₂) ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₄ ∧
        (∀ j, a.app j ≫ C₂.ι.app j = C₁.ι.app j ≫ a') ∧
        (∀ j, b.app j ≫ B.ι.app (t.obj j) = C₂.ι.app j ≫ b') ∧
        (∀ j, r.app j ≫ colimit.ι K₄ j ≫ v₄ = B.ι.app (t.obj j) ≫ r') := by
  classical
  simp only
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
  choose KU eKU hKU ιU hιU using fun n ↦
    etale_limit_open_cohomology_cocone_degree D c F φ hidentity hcomposition
      G eG hG L i₀ (e.hom ≫ (U ⊔ V).ι) U n
  choose KV eKV hKV ιV hιV using fun n ↦
    etale_limit_open_cohomology_cocone_degree D c F φ hidentity hcomposition
      G eG hG L i₀ (e.hom ≫ (U ⊔ V).ι) V n
  choose KI eKI hKI ιI hιI using fun n ↦
    etale_limit_open_cohomology_cocone_degree D c F φ hidentity hcomposition
      G eG hG L i₀ (e.hom ≫ (U ⊔ V).ι) (U ⊓ V) n
  have hcover : (e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ (U ⊔ V) = ⊤ := by
    simp only [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  obtain ⟨a, b, r, a', b', ι₁, ι₄, hab, hbr, hab', ha, hb, hr,
      hfst₁, hsnd₁, hfst₄, hsnd₄⟩ :=
    etale_limit_open_mayerVietoris_maps X U V D c F φ hidentity hcomposition
      G eG hG L q H eH hH B eB hB i₀ (e.hom ≫ (U ⊔ V).ι) hcover
      KU eKU hKU ιU hιU KV eKV hKV ιV hιV KI eKI hKI ιI hιI
  let CI (n : ℕ) : Cocone (KI n) := Cocone.mk _ (ιI n)
  have hvU (n : ℕ) :=
    etale_limit_open_comparison_certificate_degree X (U ⊔ V) U hU le_sup_left D c hc
      F φ hidentity hcomposition G eG hG L hL i₀ e n allowed (Or.inl rfl)
      (KU n) (eKU n) (hKU n) (ιU n) (hιU n)
  have hvV (n : ℕ) :=
    etale_limit_open_comparison_certificate_degree X (U ⊔ V) V hV le_sup_right D c hc
      F φ hidentity hcomposition G eG hG L hL i₀ e n allowed (Or.inr (Or.inl rfl))
      (KV n) (eKV n) (hKV n) (ιV n) (hιV n)
  have hcompactI : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    have : QuasiSeparatedSpace (U ⊔ V).toScheme :=
      e.inv.homeomorph.isOpenEmbedding.quasiSeparatedSpace
    have hqs : IsQuasiSeparated ((U ⊔ V : X.Opens) : Set X) :=
      by
        have h := (isQuasiSeparated_univ (α := (U ⊔ V).toScheme)).image_of_isEmbedding
          (U ⊔ V).ι.isOpenEmbedding.isEmbedding
        simpa only [Set.image_univ, Scheme.Opens.range_ι] using h
    exact hqs U V le_sup_left U.isOpen hU le_sup_right V.isOpen hV
  have hvI :=
    etale_limit_open_comparison_certificate_degree X (U ⊔ V) (U ⊓ V) hcompactI
      (inf_le_left.trans le_sup_left) D c hc F φ hidentity hcomposition G eG hG L hL
      i₀ e q allowed (Or.inr (Or.inr rfl)) (KI q) (eKI q) (hKI q) (ιI q) (hιI q)
  have hv₁ : StageCohomologyComparison allowed
      (colimit.desc (KU q ⊞ KV q) (Cocone.mk _ ι₁)) := by
    with_reducible
      exact (product_cocone_certificate allowed (KU q) (KV q)
        (ιU q) (ιV q) ι₁ hfst₁ hsnd₁ (hvU q) (hvV q))
  have hv₄ : StageCohomologyComparison allowed
      (colimit.desc (KU (q + 1) ⊞ KV (q + 1)) (Cocone.mk _ ι₄)) := by
    with_reducible
      exact (product_cocone_certificate allowed (KU (q + 1)) (KV (q + 1))
        (ιU (q + 1)) (ιV (q + 1)) ι₄ hfst₄ hsnd₄ (hvU (q + 1)) (hvV (q + 1)))
  refine ⟨J, inferInstance, inferInstance, inferInstance, t, ht,
    KU q ⊞ KV q, KI q, KU (q + 1) ⊞ KV (q + 1), a, b, r,
    Cocone.mk _ ι₁, CI q, a', b', colimit.desc _ (Cocone.mk _ ι₄),
    hab, hbr, hab', hv₁, hvI, hv₄, ha, hb, ?_⟩
  intro j
  simp only [colimit.ι_desc]
  -- The supplied tail functor evaluates to the underlying index.
  convert hr j using 1 <;> rfl

end AlgebraicGeometry.Etale
