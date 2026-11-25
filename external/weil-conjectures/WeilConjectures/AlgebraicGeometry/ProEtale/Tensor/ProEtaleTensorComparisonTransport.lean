/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorTotalTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Transport of representative-normalized tensor comparisons

## References

* Stacks Project, Cohomology on Sites, Tag 07A4
* Stacks Project, Cohomology on Sites, Tag 07A4, passage from flat K-flat representatives to derived
  tensor by localization
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits

private theorem normalizedTensorPath
    {C : Type*} [Category C] {A B D E F G H I J K L : C}
    {u : A ⟶ B} {v : B ⟶ D} {w : D ⟶ E} {z : E ⟶ F}
    {p : F ⟶ G} {q : G ⟶ H} {u' : A ⟶ I} {v' : I ⟶ D}
    {p' : E ⟶ J} {z' : J ⟶ G} {r : I ⟶ K} {t : K ⟶ H}
    {u₀ : A ⟶ L} {r₀ : L ⟶ K} (i : H ≅ J)
    (h₁ : u ≫ v = u' ≫ v') (h₂ : z ≫ p = p' ≫ z') (h₃ : z' ≫ q = i.inv)
    (h₄ : v' ≫ w ≫ p' = r ≫ t ≫ i.hom) (h₅ : u' ≫ r = u₀ ≫ r₀) :
    u ≫ v ≫ w ≫ z ≫ p ≫ q = u₀ ≫ r₀ ≫ t := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄]
  simp only [Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% h₅]

private theorem comparedTensorPath
    {A B C : Type*} [Category A] [Category B] [Category C]
    (K : A ⥤ B) (U : C × C ⥤ B)
    {M N O : A} {P P' P'' P''' Q Q' Q'' Q''' : C} {Z Z' : B}
    {a : M ⟶ N} {b : N ⟶ O} {c : M ⟶ O}
    {alpha : K.obj O ⟶ U.obj (P, Q)}
    {lP : P ⟶ P'} {lQ : Q ⟶ Q'} {nP : P' ⟶ P''} {nQ : Q' ⟶ Q''}
    {kP : P ⟶ P'''} {kQ : Q ⟶ Q'''} {ecP : P''' ⟶ P''} {ecQ : Q''' ⟶ Q''}
    {repF : U.obj (P'', Q'') ⟶ Z} {repK : U.obj (P''', Q''') ⟶ Z'}
    {total : Z' ⟶ Z} {result : K.obj M ⟶ Z'}
    (har : a ≫ b = c) (hp : lP ≫ nP = kP ≫ ecP) (hq : lQ ≫ nQ = kQ ≫ ecQ)
    (hbx : U.map (Prod.mkHom ecP ecQ) ≫ repF = repK ≫ total)
    (hg : K.map c ≫ alpha ≫ U.map (Prod.mkHom kP kQ) ≫ repK = result) :
    K.map a ≫ K.map b ≫ alpha ≫ U.map (Prod.mkHom lP lQ) ≫
        U.map (Prod.mkHom nP nQ) ≫ repF = result ≫ total := by
  rw [← K.map_comp_assoc, har, ← U.map_comp_assoc]
  change _ ≫ _ ≫ U.map (Prod.mkHom (lP ≫ nP) (lQ ≫ nQ)) ≫ _ = _
  rw [hp, hq]
  change _ ≫ _ ≫ U.map (Prod.mkHom kP kQ ≫ Prod.mkHom ecP ecQ) ≫ _ = _
  rw [U.map_comp]
  simp only [Category.assoc]
  rw [hbx, reassoc_of% hg]

namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
attribute [local implicit_reducible] resolving proEtaleFlatRepresentatives
  proEtaleRingDerivedPullbackFactors proEtaleCanonicalTensorComparison
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf SheafOfModules.monoidalCategory
  proEtaleOrdinaryTensorPullback

/-- Normalized total comparisons determine the derived tensor transport square. -/
theorem proEtaleTensorComparisonTransport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (L : Mod R ⥤ Mod S) [L.Additive]
    (e : L ≅ proEtaleRingModulePullback f R S c) (d : ExactModel L)
    (l : d.functor ≅ proEtaleRingDerivedPullback f R S c)
    (hf : ∀ C : CochainComplex (Mod R) ℤ,
      l.hom.app (DerivedCategory.Q.obj C) ≫
        (proEtaleRingDerivedPullbackFactors f R S c).hom.app C =
      d.factors.hom.app C ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app C))
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (ay : TensorModel R) (bx : TensorModel S)
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (tc : TensorComparison L d ay bx mu)
    (he : ∀ M N : Mod R,
      e.hom.app (((tensor R).obj M).obj N) ≫
        (proEtaleOrdinaryTensorPullback f R S c M N).hom =
      (mu M N).hom ≫ ((tensor S).map (e.hom.app M)).app (L.obj N) ≫
        ((tensor S).obj ((proEtaleRingModulePullback f R S c).obj M)).map (e.hom.app N))
    (ea : a.tensor ≅ ay.functor) (eb : b.tensor ≅ bx.functor)
    (ha : Functor.isoWhiskerLeft
      (((resolving R).ι ⋙ DerivedCategory.Q).prod
        ((resolving R).ι ⋙ DerivedCategory.Q)) ea = a.representative.symm ≪≫ ay.representative)
    (hb : Functor.isoWhiskerLeft
      (((resolving S).ι ⋙ DerivedCategory.Q).prod
        ((resolving S).ι ⋙ DerivedCategory.Q)) eb = b.representative.symm ≪≫ bx.representative) :
    ∀ M N : Der R,
      l.hom.app (a.tensor.obj (M, N)) ≫
          (proEtaleCanonicalTensorComparison f R S c a b).hom.app (M, N) ≫
          eb.hom.app ((proEtaleRingDerivedPullback f R S c).obj M,
            (proEtaleRingDerivedPullback f R S c).obj N) =
        d.functor.map (ea.hom.app (M, N)) ≫ tc.comparison.hom.app (M, N) ≫
          bx.functor.map (Prod.mkHom (l.hom.app M) (l.hom.app N)) := by
  let F := proEtaleRingDerivedPullback f R S c
  let K := d.functor
  let FC := (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)
  let KC := L.mapHomologicalComplex (.up ℤ)
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  let alpha := proEtaleCanonicalTensorComparison f R S c a b
  let left : a.tensor ⋙ K ⟶ (F.prod F) ⋙ bx.functor :=
    Functor.whiskerLeft a.tensor l.hom ≫ Functor.whiskerRight alpha.hom (𝟭 _) ≫
      Functor.whiskerLeft (F.prod F) eb.hom
  let right : a.tensor ⋙ K ⟶ (F.prod F) ⋙ bx.functor :=
    Functor.whiskerRight ea.hom K ≫ tc.comparison.hom ≫
      Functor.whiskerRight (NatTrans.prod l.hom l.hom) bx.functor
  dsimp only
  suffices h : left = right by
    intro M N
    exact NatTrans.congr_app h (M, N)
  obtain ⟨_, ⟨ff⟩, _⟩ := proEtaleTensorPullbackDescentData f R S c
  apply ff.map_injective
  ext Z
  rcases Z with ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩
  have hpa := (Classical.choose_spec (proEtaleCanonicalTensorPullback f R S c a b).2.exists)
  obtain ⟨hpF, hqF, hn⟩ := hpa P Q hp hq
  have hpK := tc.preserves P hp
  have hqK := tc.preserves Q hq
  have har : a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      ea.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        ay.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) := by
    have h := NatTrans.congr_app (congrArg Iso.hom ha) (⟨P, hp⟩, ⟨Q, hq⟩)
    change ea.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
        ay.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) at h
    rw [h, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hbr : eb.hom.app (DerivedCategory.Q.obj (FC.obj P),
        DerivedCategory.Q.obj (FC.obj Q)) ≫
      bx.representative.inv.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) =
        b.representative.inv.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) := by
    have h := NatTrans.congr_app (congrArg Iso.hom hb)
      (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩)
    change eb.hom.app (DerivedCategory.Q.obj (FC.obj P),
        DerivedCategory.Q.obj (FC.obj Q)) =
      b.representative.inv.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) ≫
        bx.representative.hom.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) at h
    rw [h, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have htotal := proEtaleTensorTotalTransport f R S c L e ay bx d mu tc he P Q
  let qn := DerivedCategory.Q.mapIso (proEtaleTensorPullbackTotalIso f R S c P Q)
  let qg := totalMap ay bx L mu tc.comm P Q
  have hqg : IsIso qg := by
    let ti := (total S).mapIso (Iso.prod (ec.app P) (ec.app Q)) ≪≫
      proEtaleTensorPullbackTotalIso f R S c P Q
    have h : qg ≫ (ec.app ((total R).obj (P, Q))).hom = ti.hom := htotal.symm
    exact IsIso.of_isIso_fac_right h
  let qgi := DerivedCategory.Q.mapIso (asIso qg)
  have hroute : DerivedCategory.Q.map (ec.hom.app ((total R).obj (P, Q))) ≫ qn.inv =
      qgi.inv ≫ DerivedCategory.Q.map
        ((total S).map (Prod.mkHom (ec.hom.app P) (ec.hom.app Q))) := by
    apply (cancel_epi qgi.hom).1
    apply (cancel_mono qn.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
    change DerivedCategory.Q.map qg ≫
      DerivedCategory.Q.map (ec.hom.app ((total R).obj (P, Q))) =
      DerivedCategory.Q.map ((total S).map
        (Prod.mkHom (ec.hom.app P) (ec.hom.app Q))) ≫
      DerivedCategory.Q.map (proEtaleTensorPullbackTotal f R S c P Q)
    simpa only [Functor.map_comp] using (congrArg DerivedCategory.Q.map htotal).symm
  have hbx : bx.functor.map (Prod.mkHom (DerivedCategory.Q.map (ec.hom.app P))
        (DerivedCategory.Q.map (ec.hom.app Q))) ≫
      bx.representative.inv.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) =
    bx.representative.inv.app (⟨KC.obj P, hpK⟩, ⟨KC.obj Q, hqK⟩) ≫
      DerivedCategory.Q.map
        ((total S).map (Prod.mkHom (ec.hom.app P) (ec.hom.app Q))) := by
    let ep : (⟨KC.obj P, hpK⟩ : (resolving S).FullSubcategory) ⟶ ⟨FC.obj P, hpF⟩ :=
      ObjectProperty.homMk (ec.hom.app P)
    let eq : (⟨KC.obj Q, hqK⟩ : (resolving S).FullSubcategory) ⟶ ⟨FC.obj Q, hqF⟩ :=
      ObjectProperty.homMk (ec.hom.app Q)
    exact bx.representative.inv.naturality (Prod.mkHom ep eq)
  have hg : K.map (ay.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      tc.comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      bx.functor.map (Prod.mkHom (d.factors.hom.app P)
        (d.factors.hom.app Q)) ≫
      bx.representative.inv.app (⟨KC.obj P, hpK⟩, ⟨KC.obj Q, hqK⟩) =
        d.factors.hom.app ((total R).obj (P, Q)) ≫ qgi.inv := by
    apply (cancel_mono qgi.hom).1
    have h := tc.representative P Q hp hq
    have hqgi : DerivedCategory.Q.map qg = qgi.hom := rfl
    change K.map (ay.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      tc.comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      bx.functor.map (Prod.mkHom (d.factors.hom.app P)
        (d.factors.hom.app Q)) ≫
      bx.representative.inv.app (⟨KC.obj P, hpK⟩, ⟨KC.obj Q, hqK⟩) ≫
        DerivedCategory.Q.map qg = _ at h
    rw [hqgi] at h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  have hlNat : K.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      l.hom.app (a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
      l.hom.app (DerivedCategory.Q.obj ((total R).obj (P, Q))) ≫
        F.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) :=
    l.hom.naturality (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))
  have hebNat : eb.hom.app (F.obj (DerivedCategory.Q.obj P),
        F.obj (DerivedCategory.Q.obj Q)) ≫
      bx.functor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) =
      b.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) ≫
      eb.hom.app (DerivedCategory.Q.obj (FC.obj P), DerivedCategory.Q.obj (FC.obj Q)) :=
    (eb.hom.naturality (Prod.mkHom
      ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
      ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q))).symm
  have hn' : F.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) =
      (proEtaleRingDerivedPullbackFactors f R S c).hom.app ((total R).obj (P, Q)) ≫
        qn.inv ≫ b.representative.hom.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) := hn
  have hl : K.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      left.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      bx.functor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) ≫
      bx.representative.inv.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) =
    d.factors.hom.app ((total R).obj (P, Q)) ≫
      DerivedCategory.Q.map (ec.hom.app ((total R).obj (P, Q))) ≫ qn.inv := by
    dsimp only [left, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.id_map]
    simp only [Category.assoc, Functor.prod_obj]
    exact normalizedTensorPath
      (b.representative.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩))
      hlNat hebNat hbr hn' (hf ((total R).obj (P, Q)))
  have hr : K.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      right.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      bx.functor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) ≫
      bx.representative.inv.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩) =
    d.factors.hom.app ((total R).obj (P, Q)) ≫ qgi.inv ≫
      DerivedCategory.Q.map
        ((total S).map (Prod.mkHom (ec.hom.app P) (ec.hom.app Q))) := by
    dsimp only [right, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.prod]
    simpa only [Category.assoc] using
      comparedTensorPath K bx.functor har (hf P) (hf Q) hbx hg
  rw [hroute] at hl
  let post := bx.functor.mapIso (Iso.prod
    ((proEtaleRingDerivedPullbackFactors f R S c).app P)
    ((proEtaleRingDerivedPullbackFactors f R S c).app Q)) ≪≫
    (bx.representative.app (⟨FC.obj P, hpF⟩, ⟨FC.obj Q, hqF⟩)).symm
  apply (cancel_epi (K.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)))).1
  apply (cancel_mono post.hom).1
  change (K.map _ ≫ left.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
    post.hom = (K.map _ ≫ right.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      post.hom
  dsimp only [post, Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.app_hom,
    Iso.app_inv, Iso.symm_hom]
  simpa only [Category.assoc] using hl.trans hr.symm

end AlgebraicGeometry.Scheme
