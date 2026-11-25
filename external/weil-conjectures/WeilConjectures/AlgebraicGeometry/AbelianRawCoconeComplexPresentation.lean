/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso
import WeilConjectures.AlgebraicGeometry.RestrictedAffineComplexSystemNatural

/-! # Complex presentation of the varying-coefficient raw diagram

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-raw-cocone-complex-presentation).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem comparison_square
    {A A' R R' K K' T T' : AddCommGrpCat.{v + 1}}
    (e : A ≅ K) (e' : A' ≅ K') (r : A ≅ R) (r' : A' ≅ R')
    (s : R ≅ T) (s' : R' ≅ T') (m : K ⟶ K') (n : T ⟶ T')
    (q : R ⟶ R') (g : A → A')
    (hm : ∀ t, m (e.hom t) = e'.hom (g t))
    (hr : ∀ t, q (r.hom t) = r'.hom (g t))
    (hs : ∀ t, n (s.hom t) = s'.hom (q t)) :
    m ≫ (e'.symm ≪≫ r' ≪≫ s').hom = (e.symm ≪≫ r ≪≫ s).hom ≫ n := by
  ext x
  change (e'.symm ≪≫ r' ≪≫ s').hom (m x) = n ((e.symm ≪≫ r ≪≫ s).hom x)
  simp only [Iso.trans_hom, Iso.symm_hom, AddCommGrpCat.comp_apply]
  have hm' := hm (e.inv x)
  simp only [Iso.inv_hom_id_apply] at hm'
  rw [hm', Iso.hom_inv_id_apply, hs, hr]

set_option backward.isDefEq.respectTransparency true in
private theorem presentation_of_iso
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    {K T : Jᵒᵖ ⥤ AddCommGrpCat.{v + 1}} {B : Cocone K} {B' : Cocone T}
    (s : EtaleComplexCohomologyPresentation T B') (a : K ≅ T) (b : B.pt ≅ B'.pt)
    (hb : ∀ i, B.ι.app i ≫ b.hom = a.hom.app i ≫ B'.ι.app i) :
    EtaleComplexCohomologyPresentation K B := by
  rcases s with ⟨D, c, hc, compact, quasiSeparated, affine, F, φ, hid, hcomp,
    n, hbelow, G, eG, hG, p, P, hP, eT, hT, L, hL, eB, hB, _⟩
  refine ⟨D, c, hc, compact, quasiSeparated, affine, F, φ, hid, hcomp,
    n, hbelow, G, eG, hG, p, P, hP, (fun i ↦ a.app (op i) ≪≫ eT i), ?_,
    L, hL, b ≪≫ eB, ?_, trivial⟩
  · intro i j f
    calc
      K.map f.op = (a.app (op i)).hom ≫ T.map f.op ≫ (a.app (op j)).inv := by
        have hn : K.map f.op ≫ (a.app (op j)).hom =
            (a.app (op i)).hom ≫ T.map f.op := a.hom.naturality f.op
        rw [← Category.assoc, ← hn]
        simp only [Iso.app_hom, Iso.app_inv, Category.assoc,
          Iso.hom_inv_id_app, Category.comp_id]
      _ = _ := by rw [hT]; simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  · intro i
    simp only [Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, hb, Category.assoc, hB]
    simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
/-- The prescribed raw diagram and its cocone admit a geometric complex presentation.
This asserts only the input data for continuity, with no colimit assertion on B.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit, reduction to affine U),
Tag 03Q8 (restricted cohomology), and Tag 0EZM (lemma-colimit-variant-complexes,
canonical pullback/coefficient maps).
(blueprint: lem-sbc-abelian-raw-cocone-complex-presentation).

Proof: Form X_i times_S U and X times_S U, with induced maps given by the pullback
universal property. That property also proves the cone is limiting. Base change
preserves affine transitions and qcqs structure morphisms. Because U is affine,
each stage is a compact quasi-separated scheme. Pull back F_i along the projections
to X_i and use upperStarComp to pull back phi. Its unit and associativity coherence
transport hphiid and hphicomp to the restricted system. Form the degree-zero single
complexes: they vanish below zero and their maps are obtained using the single-functor
comparison. On the limit restrict H and identify each object using eH and the
inverse-image composition comparison. The formula hH gives its canonical transitions.
The restriction functor is a left adjoint, so it preserves the coefficient colimit;
the single-complex functor preserves this colimit termwise. This gives G, eG, hG,
L and IsColimit L in EtaleComplexCohomologyPresentation.
Use the free abelian represented sheaf/sections adjunction at U. Its inverse image
represents sections on X_i times_S U. Etale restriction preserves injectives because
its left adjoint is exact. Thus on a bounded-below injective resolution this adjunction
identifies the raw derived-Hom group with restricted cohomology, additively. The fully
faithful inclusion of D+ in D compares this with cohomology of the single complex.
Apply these isomorphisms to e.inv and eB.inv to identify K and B.pt with those groups.
Choose P to be exactly the derived adjunction-unit pullback displayed in the definition.
Naturality of derived adjunction, inverse-image composition, and the single and shift
comparisons identifies the raw five-factor formula with P followed by the coefficient
map. Applied to each stage arrow and hmap this proves hH of the presentation; applied
to each cone projection and hleg it proves hB. Both are equalities of homomorphisms,
by extensionality. Reindex through the double-opposite equivalence to meet the index
convention in the presentation. No continuity theorem is used. For degree zero these
are the section adjunctions; for empty U all the groups are zero, and the same
comparisons still apply. -/
theorem abelianRawCocone_complex_presentation {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left]
    (K : I ⥤ AddCommGrpCat.{v + 1}) (B : Cocone K)
    (e : ∀ i : I,
      (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U) ≅
        K.obj i)
    (eB : (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).obj (op U) ≅ B.pt)
    (hmap : ∀ {i j : I} (f : i ⟶ j) (t :
        (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U)),
      K.map f ((e i).hom t) = (e j).hom
        (abelianHigherDirectImageRawPullback (D.map f.op).left (D.obj (op i)).hom
          (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) U t))
    (hleg : ∀ (i : I) (t :
        (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U)),
      B.ι.app i ((e i).hom t) = eB.hom
        (abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) U t)) :
    EtaleComplexCohomologyPresentation
      ((opOpEquivalence I).functor ⋙ K)
      (B.whisker (opOpEquivalence I).functor) := by
  obtain ⟨r, hr⟩ := exists_raw_restricted_cohomology_natural_iso S p U
  obtain ⟨T, B', hpres, s, sB, hsB, hsT⟩ :=
    exists_restricted_affine_complex_system_natural D c hc F φ hφid hφcomp H eH hH p U
  let α : (opOpEquivalence I).functor ⋙ K ≅ T :=
    NatIso.ofComponents
      (fun i ↦ (e i.unop.unop).symm ≪≫
        r (D.obj (op i.unop.unop)).hom (F i.unop.unop) ≪≫ s i) (by
      intro i j f
      change K.map f.unop.unop ≫ _ = _ ≫ T.map f
      apply comparison_square (q := rawAffineRestrictedCohomologyMap
        (D.map f.unop.unop.op).left (D.obj (op i.unop.unop)).hom
        (D.obj (op j.unop.unop)).hom (Over.w (D.map f.unop.unop.op)) p
        (F i.unop.unop) (F j.unop.unop) (φ f.unop.unop) U)
        (g := abelianHigherDirectImageRawPullback (D.map f.unop.unop.op).left
          (D.obj (op i.unop.unop)).hom (D.obj (op j.unop.unop)).hom
          (Over.w (D.map f.unop.unop.op)) p (F i.unop.unop) (F j.unop.unop)
          (φ f.unop.unop) U)
      · exact hmap f.unop.unop
      · exact hr _ _ _ _ _ _ _
      · intro t
        have ht := hsT f.unop.unop t
        change T.map f _ = _ at ht
        exact ht)
  let b : B.pt ≅ B'.pt := eB.symm ≪≫ r c.pt.hom (colimit H) ≪≫ sB
  refine presentation_of_iso hpres α b ?_
  intro i
  change B.ι.app i.unop.unop ≫ (eB.symm ≪≫ r c.pt.hom (colimit H) ≪≫ sB).hom =
    ((e i.unop.unop).symm ≪≫
      r (D.obj (op i.unop.unop)).hom (F i.unop.unop) ≪≫ s i).hom ≫ B'.ι.app i
  apply comparison_square (q := rawAffineRestrictedCohomologyMap
    (c.π.app (op i.unop.unop)).left (D.obj (op i.unop.unop)).hom c.pt.hom
    (Over.w (c.π.app (op i.unop.unop))) p (F i.unop.unop) (colimit H)
    ((eH i.unop.unop).inv ≫ colimit.ι H i.unop.unop) U)
    (g := abelianHigherDirectImageRawPullback (c.π.app (op i.unop.unop)).left
      (D.obj (op i.unop.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop.unop))) p
      (F i.unop.unop) (colimit H) ((eH i.unop.unop).inv ≫ colimit.ι H i.unop.unop) U)
  · exact hleg i.unop.unop
  · exact hr _ _ _ _ _ _ _
  · exact hsB i

end AlgebraicGeometry.Etale
