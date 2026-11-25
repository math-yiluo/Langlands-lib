/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.CoefficientHomUnit

/-! # Augmentation evaluation in coefficient Hom complexes

Source: Stacks Project, Algebraization, Tag 099I, final displayed composite.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local irreducible] homComplexFunctor

private theorem augmentationFactorization
    {D : Type*} [Category D] (H : Dᵒᵖ ⥤ D ⥤ D)
    {A B K L N Q : D} (σ : A ⟶ B) (ε : K ⟶ A) (δ : L ⟶ B)
    (u : K ⟶ L) (hu : u ≫ δ = ε ≫ σ)
    (a : N ⟶ (H.obj (op B)).obj N) (g : N ⟶ Q)
    (eN : (H.obj (op A)).obj N ≅ N) (eQ : (H.obj (op A)).obj Q ≅ Q)
    (ha : a ≫ (H.map σ.op).app N = eN.inv)
    (he : (H.obj (op A)).map g ≫ eQ.hom = eN.hom ≫ g) :
    a ≫ (H.map δ.op).app N ≫ (H.obj (op L)).map g ≫ (H.map u.op).app Q =
      g ≫ eQ.inv ≫ (H.map ε.op).app Q := by
  have hu' : (H.map δ.op).app N ≫ (H.map u.op).app N =
      (H.map σ.op).app N ≫ (H.map ε.op).app N := by
    rw [← NatTrans.comp_app, ← H.map_comp, ← op_comp, hu,
      op_comp, H.map_comp, NatTrans.comp_app]
  have hn := (H.map u.op).naturality g
  have hε := (H.map ε.op).naturality g
  have hei : eN.inv ≫ (H.obj (op A)).map g = g ≫ eQ.inv := by
    apply (cancel_mono eQ.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using congrArg (fun k ↦ eN.inv ≫ k) he
  rw [hn]
  rw [← Category.assoc ((H.map δ.op).app N), hu']
  simp only [Category.assoc]
  rw [← hε, ← Category.assoc a, ha, ← Category.assoc, hei, Category.assoc]

private theorem coefficientAugmentation
    {D E : Type*} [Category D] [Category E] (r : D ⥤ E)
    (A : E) (B : D) (σ : A ⟶ r.obj B)
    (H : Eᵒᵖ ⥤ E ⥤ E) (F : Dᵒᵖ ⥤ E ⥤ D)
    (c : Functor.uncurry.obj F ⋙ r ≅ r.op.prod (𝟭 E) ⋙ Functor.uncurry.obj H)
    (α : 𝟭 D ⟶ r ⋙ F.obj (op B)) (e : H.obj (op A) ≅ 𝟭 E)
    (hα : ∀ M, r.map (α.app M) ≫ c.hom.app (op B, r.obj M) ≫
      (H.map σ.op).app (r.obj M) = (e.app (r.obj M)).inv)
    (K : E) (ε : K ⟶ A) (L : D) (δ : L ⟶ B)
    (T : E ⥤ E) (η : 𝟭 E ⟶ T) (u : K ⟶ r.obj L)
    (hu : u ≫ r.map δ = ε ≫ σ) :
    ∃ G : E ⥤ D, ∃ cL : G ⋙ r ≅ H.obj (op (r.obj L)),
      ∃ β : 𝟭 D ⟶ r ⋙ T ⋙ G, ∀ M,
        r.map (β.app M) ≫ cL.hom.app (T.obj (r.obj M)) ≫
          (H.map u.op).app (T.obj (r.obj M)) =
        η.app (r.obj M) ≫ (e.app (T.obj (r.obj M))).inv ≫
          (H.map ε.op).app (T.obj (r.obj M)) := by
  let G := F.obj (op L)
  let cL : G ⋙ r ≅ H.obj (op (r.obj L)) :=
    NatIso.ofComponents (fun N ↦ c.app (op L, N)) (by
      intro N N' f
      have h := c.hom.naturality
        (show (op L, N) ⟶ (op L, N') from (𝟙 _, f))
      change r.map ((F.map (𝟙 (op L))).app N ≫ (F.obj (op L)).map f) ≫
          c.hom.app (op L, N') = c.hom.app (op L, N) ≫
            (H.map (r.map (𝟙 L)).op).app N ≫ (H.obj (op (r.obj L))).map f at h
      rw [F.map_id, NatTrans.id_app, Category.id_comp, r.map_id, op_id,
        H.map_id, NatTrans.id_app] at h
      change r.map ((F.obj (op L)).map f) ≫ c.hom.app (op L, N') =
        c.hom.app (op L, N) ≫ (𝟙 _ ≫ (H.obj (op (r.obj L))).map f) at h
      rw [Category.id_comp] at h
      exact h)
  let β : 𝟭 D ⟶ r ⋙ T ⋙ G :=
    { app M := α.app M ≫ (F.obj (op B)).map (η.app (r.obj M)) ≫
        (F.map δ.op).app (T.obj (r.obj M))
      naturality := by
        intro M N f
        have ha : f ≫ α.app N = α.app M ≫ (F.obj (op B)).map (r.map f) :=
          α.naturality f
        dsimp only [Functor.id_map, Functor.comp_map]
        rw [← Category.assoc, ha]
        simp only [Category.assoc]
        rw [← Category.assoc ((F.obj (op B)).map _), ← Functor.map_comp]
        have hη : r.map f ≫ η.app (r.obj N) = η.app (r.obj M) ≫ T.map (r.map f) :=
          η.naturality (r.map f)
        rw [hη, Functor.map_comp]
        simp only [Category.assoc]
        rw [(F.map δ.op).naturality] }
  refine ⟨G, cL, β, ?_⟩
  intro M
  let N := r.obj M
  let Q := T.obj N
  have hc : r.map ((F.obj (op B)).map (η.app N) ≫ (F.map δ.op).app Q) ≫
      c.hom.app (op L, Q) = c.hom.app (op B, N) ≫
        (H.map (r.map δ).op).app N ≫ (H.obj (op (r.obj L))).map (η.app N) := by
    rw [(F.map δ.op).naturality]
    exact c.hom.naturality (show (op B, N) ⟶ (op L, Q) from (δ.op, η.app N))
  have ha : (r.map (α.app M) ≫ c.hom.app (op B, N)) ≫
      (H.map σ.op).app N = (e.app N).inv := (Category.assoc _ _ _).trans (hα M)
  have hh := augmentationFactorization H σ ε (r.map δ) u hu
    (r.map (α.app M) ≫ c.hom.app (op B, N)) (η.app N)
    (e.app N) (e.app Q) ha (e.hom.naturality (η.app N))
  change r.map (α.app M ≫ _) ≫ c.hom.app (op L, Q) ≫ (H.map u.op).app Q = _
  rw [r.map_comp, Category.assoc, ← Category.assoc _ (c.hom.app (op L, Q)), hc]
  simpa only [N, Q, Functor.id_obj, Category.assoc] using hh

-- The sectionwise formula compares the two scalar actions and the product projections.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Augmentation evaluation lifts to a natural B-linear map of coefficient Hom complexes.
Source: Stacks Project, Algebraization, Tag 099I, final displayed composite.
(auxiliary; not a blueprint node).

Proof: construct the coefficient internal Hom H with its precomposition B-action and
its explicit augmentation-evaluation maps. Apply the product Hom-complex construction
to H, and normalize its restriction comparison by its product projections. For m in
M^n, define the projection at source degree p to be zero if p is not zero. At p=0,
use the B-linear evaluation map associated to delta^0, followed by eta^n. The product
universal property supplies the degree-n map. The Hom differential on a projection is
d_I h - (-1)^n h d_L. The p=0 equation is eta's chain-map equation; the p=-1 term
vanishes by delta d_L=0; all other projections are zero. Thus these degree maps form
a chain map. Eta's naturality gives naturality in M. Restrict and precompose with u.
The augmentation equation identifies the resulting cochain with
x -> epsilon(x) eta(m), which is evaluation-at-one inverse followed by precomposition
with epsilon. Equality of all product projections proves the stated chain identity.
No quasi-isomorphism or K-injectivity hypothesis is needed.
-/
theorem exists_coefficientHom_augmentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (L : ringedSiteComplex B) (δ : L ⟶ ringedSiteRingComplex B)
    (T : ringedSiteComplex R ⥤ ringedSiteComplex R)
    (η : 𝟭 (ringedSiteComplex R) ⟶ T) :
    let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let rc := r.mapHomologicalComplex (.up ℤ)
    let σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B) :=
      (HomologicalComplex.single _ (.up ℤ) 0).map
          (SheafOfModules.LocalizationCech.unitMap φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    ∀ (u : K ⟶ rc.obj L), u ≫ rc.map δ = ε ≫ σ →
      ∃ G : ringedSiteComplex R ⥤ ringedSiteComplex B,
        ∃ c : G ⋙ rc ≅ (homComplexFunctor (R := R)).obj (op (rc.obj L)),
          ∃ β : 𝟭 (ringedSiteComplex B) ⟶ rc ⋙ T ⋙ G,
            ∀ M : ringedSiteComplex B,
              rc.map (β.app M) ≫ c.hom.app (T.obj (rc.obj M)) ≫
                  ((homComplexFunctor (R := R)).map u.op).app (T.obj (rc.obj M)) =
                (by
                  change rc.obj M ⟶
                    ((homComplexFunctor (R := R)).obj (op K)).obj (T.obj (rc.obj M))
                  exact η.app (rc.obj M) ≫
                    (ringedHomUnitEvaluationIso R (T.obj (rc.obj M))).inv ≫
                    ((homComplexFunctor (R := R)).map ε.op).app (T.obj (rc.obj M))) := by
  classical
  dsimp only
  intro u hu
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let rc := r.mapHomologicalComplex (.up ℤ)
  obtain ⟨F, c, α, hα⟩ := exists_coefficientHom_unit φ
  let e : (homComplexFunctor (R := R)).obj (op (ringedSiteRingComplex R)) ≅
      𝟭 (ringedSiteComplex R) :=
    NatIso.ofComponents (ringedHomUnitEvaluationIso R) (by
      intro M N f
      apply HomologicalComplex.hom_ext
      intro n
      exact homComplex_unit_evaluation_naturality J R f n)
  exact coefficientAugmentation rc (ringedSiteRingComplex R) (ringedSiteRingComplex B)
    _ (homComplexFunctor (R := R)) F c α e hα K ε L δ T η u hu

end CategoryTheory
