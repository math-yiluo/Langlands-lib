import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Canonical comparison of pullbacks along equal composites -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule.RigidifiedModule

section Comparison

variable {U X Y : Scheme.{u}}

/-- The canonical comparison `a^* p^* M ≅ b^* p^* M` attached to an equation
`a ≫ p = b ≫ p`: composition comparison for `a`, then pullback along equal maps, then the
inverse composition comparison for `b`. -/
def equalCompositeIso (p : X ⟶ Y) (a b : U ⟶ X) (h : a ≫ p = b ≫ p) (M : Y.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackComp a p).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp b p).app M).symm

/-- The canonical comparison as a natural isomorphism of functors `Y.Modules ⥤ U.Modules`. -/
def equalCompositeNatIso (p : X ⟶ Y) (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback a ≅
      Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback b :=
  Scheme.Modules.pullbackComp a p ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp b p).symm

variable (p : X ⟶ Y) (a b c : U ⟶ X) (M : Y.Modules)

lemma equalCompositeIso_hom (h : a ≫ p = b ≫ p) :
    (equalCompositeIso p a b h M).hom =
      (Scheme.Modules.pullbackComp a p).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).hom.app M ≫
          (Scheme.Modules.pullbackComp b p).inv.app M :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma equalCompositeIso_inv (h : a ≫ p = b ≫ p) :
    (equalCompositeIso p a b h M).inv =
      (Scheme.Modules.pullbackComp b p).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).inv.app M ≫
          (Scheme.Modules.pullbackComp a p).inv.app M := by
  simp [equalCompositeIso]

/-- The forward comparison is the published generalized comparison `compHom` followed by
the inverse composition comparison for `b`. -/
lemma equalCompositeIso_hom_eq_compHom (h : a ≫ p = b ≫ p) :
    (equalCompositeIso p a b h M).hom =
      compHom a p (b ≫ p) h M ≫ (Scheme.Modules.pullbackComp b p).inv.app M := by
  simp [equalCompositeIso, compHom]

lemma equalCompositeNatIso_app (h : a ≫ p = b ≫ p) :
    (equalCompositeNatIso p a b h).app M = equalCompositeIso p a b h M := by
  ext1
  simp [equalCompositeNatIso, equalCompositeIso]

set_option backward.isDefEq.respectTransparency false in
/-- Reflexivity: the comparison for `a = a` is the identity. -/
@[simp]
lemma equalCompositeIso_refl (h : a ≫ p = a ≫ p) :
    equalCompositeIso p a a h M = Iso.refl _ := by
  ext1
  simp [equalCompositeIso, Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- Reversal: the comparison for the reversed equation is the inverse comparison. -/
lemma equalCompositeIso_symm (h : a ≫ p = b ≫ p) (h' : b ≫ p = a ≫ p) :
    equalCompositeIso p b a h' M = (equalCompositeIso p a b h M).symm := by
  ext1
  simp [equalCompositeIso, Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- Transitivity (cocycle law) of the canonical comparisons. -/
lemma equalCompositeIso_trans (h : a ≫ p = b ≫ p) (h' : b ≫ p = c ≫ p)
    (h'' : a ≫ p = c ≫ p) :
    equalCompositeIso p a b h M ≪≫ equalCompositeIso p b c h' M =
      equalCompositeIso p a c h'' M := by
  ext1
  simp [equalCompositeIso, Scheme.Modules.pullbackCongr]

/-- Naturality of the canonical comparison in the module. -/
@[reassoc]
lemma equalCompositeIso_hom_naturality (h : a ≫ p = b ≫ p) {M N : Y.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback p).map φ) ≫
        (equalCompositeIso p a b h N).hom =
      (equalCompositeIso p a b h M).hom ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback p).map φ) := by
  rw [← equalCompositeNatIso_app, ← equalCompositeNatIso_app]
  exact (equalCompositeNatIso p a b h).hom.naturality φ

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with precomposition by `q : V ⟶ U`, through the canonical composition
comparisons for `q ≫ a` and `q ≫ b`. -/
@[reassoc]
lemma equalCompositeIso_precomp_hom {V : Scheme.{u}} (q : V ⟶ U) (h : a ≫ p = b ≫ p)
    (h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p) :
    (Scheme.Modules.pullbackComp q a).hom.app ((Scheme.Modules.pullback p).obj M) ≫
        (equalCompositeIso p (q ≫ a) (q ≫ b) h' M).hom =
      (Scheme.Modules.pullback q).map (equalCompositeIso p a b h M).hom ≫
        (Scheme.Modules.pullbackComp q b).hom.app ((Scheme.Modules.pullback p).obj M) := by
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (q ≫ b) p).hom.app M)]
  have e1 := compHom_assoc q b p (q ≫ b) (b ≫ p) ((q ≫ b) ≫ p) rfl rfl rfl
    (Category.assoc _ _ _).symm M
  have e2 := compHom_assoc q a p (q ≫ a) (b ≫ p) ((q ≫ b) ≫ p) rfl h h'
    (Category.assoc _ _ _).symm M
  simp only [compHom_rfl] at e1 e2
  calc _ = (Scheme.Modules.pullbackComp q a).hom.app ((Scheme.Modules.pullback p).obj M) ≫
          compHom (q ≫ a) p ((q ≫ b) ≫ p) h' M := by
        simp [equalCompositeIso, compHom]
    _ = (Scheme.Modules.pullback q).map (compHom a p (b ≫ p) h M) ≫
          compHom q (b ≫ p) ((q ≫ b) ≫ p) (Category.assoc _ _ _).symm M := e2
    _ = (Scheme.Modules.pullback q).map (compHom a p (b ≫ p) h M) ≫
          (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackComp b p).inv.app M) ≫
            (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackComp b p).hom.app M) ≫
              compHom q (b ≫ p) ((q ≫ b) ≫ p) (Category.assoc _ _ _).symm M := by
        rw [← Functor.map_comp_assoc (Scheme.Modules.pullback q)
          ((Scheme.Modules.pullbackComp b p).inv.app M), Iso.inv_hom_id_app,
          CategoryTheory.Functor.map_id, Category.id_comp]
    _ = (Scheme.Modules.pullback q).map (compHom a p (b ≫ p) h M) ≫
          (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackComp b p).inv.app M) ≫
            (Scheme.Modules.pullbackComp q b).hom.app ((Scheme.Modules.pullback p).obj M) ≫
              (Scheme.Modules.pullbackComp (q ≫ b) p).hom.app M := by
        rw [e1]
    _ = _ := by
        rw [equalCompositeIso_hom_eq_compHom, Functor.map_comp]
        simp only [Category.assoc]

/-- Compatibility with precomposition by `q : V ⟶ U`, as an equation of isomorphisms. -/
lemma equalCompositeIso_precomp {V : Scheme.{u}} (q : V ⟶ U) (h : a ≫ p = b ≫ p)
    (h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p) :
    equalCompositeIso p (q ≫ a) (q ≫ b) h' M =
      ((Scheme.Modules.pullbackComp q a).app ((Scheme.Modules.pullback p).obj M)).symm ≪≫
        (Scheme.Modules.pullback q).mapIso (equalCompositeIso p a b h M) ≪≫
          (Scheme.Modules.pullbackComp q b).app ((Scheme.Modules.pullback p).obj M) := by
  ext1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom]
  rw [← equalCompositeIso_precomp_hom p a b M q h h', Iso.inv_hom_id_app_assoc]

end Comparison

section Automorphism

variable {U X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along equal maps acts on the structure sheaf through the canonical unit
comparisons. -/
lemma pullbackUnitIso_inv_pullbackCongr_hom {f g : U ⟶ X} (hfg : f = g) :
    (pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullbackCongr hfg).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
          (pullbackUnitIso g).hom =
      𝟙 _ := by
  subst hfg
  simp [Scheme.Modules.pullbackCongr]

/-- The automorphism of `O_U` obtained by transporting the canonical comparison
`a^* p^* M ≅ b^* p^* M` through a trivialization `α : p^* M ≅ O_X`: it is `α_b` after the
inverse of `α_a`, normalized by the canonical identifications `a^* O_X ≅ O_U ≅ b^* O_X`. -/
def equalCompositeUnitAut (p : X ⟶ Y) (a b : U ⟶ X) (h : a ≫ p = b ≫ p) {M : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    SheafOfModules.unit U.ringCatSheaf ≅ SheafOfModules.unit U.ringCatSheaf :=
  (pullbackUnitIso a).symm ≪≫ ((Scheme.Modules.pullback a).mapIso α).symm ≪≫
    equalCompositeIso p a b h M ≪≫ (Scheme.Modules.pullback b).mapIso α ≪≫ pullbackUnitIso b

variable (p : X ⟶ Y) (a b c : U ⟶ X) {M : Y.Modules}
  (α : (Scheme.Modules.pullback p).obj M ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The defining composite of the transported automorphism. -/
lemma equalCompositeUnitAut_hom (h : a ≫ p = b ≫ p) :
    (equalCompositeUnitAut p a b h α).hom =
      (pullbackUnitIso a).inv ≫ (Scheme.Modules.pullback a).map α.inv ≫
        (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map α.hom ≫
          (pullbackUnitIso b).hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the transported automorphism. -/
lemma equalCompositeUnitAut_inv (h : a ≫ p = b ≫ p) :
    (equalCompositeUnitAut p a b h α).inv =
      (pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map α.inv ≫
        (equalCompositeIso p a b h M).inv ≫ (Scheme.Modules.pullback a).map α.hom ≫
          (pullbackUnitIso a).hom := by
  simp [equalCompositeUnitAut]

set_option backward.isDefEq.respectTransparency false in
/-- Identity: the transported automorphism for `a = a` is the identity. -/
@[simp]
lemma equalCompositeUnitAut_refl (h : a ≫ p = a ≫ p) :
    equalCompositeUnitAut p a a h α = Iso.refl _ := by
  ext1
  simp [equalCompositeUnitAut_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Reversal: the transported automorphism for the reversed equation is the inverse. -/
lemma equalCompositeUnitAut_symm (h : a ≫ p = b ≫ p) (h' : b ≫ p = a ≫ p) :
    equalCompositeUnitAut p b a h' α = (equalCompositeUnitAut p a b h α).symm := by
  ext1
  rw [Iso.symm_hom, equalCompositeUnitAut_hom, equalCompositeUnitAut_inv,
    equalCompositeIso_symm p a b M h h', Iso.symm_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Cocycle law: transported automorphisms compose along `a, b, c`. -/
lemma equalCompositeUnitAut_trans (h : a ≫ p = b ≫ p) (h' : b ≫ p = c ≫ p)
    (h'' : a ≫ p = c ≫ p) :
    equalCompositeUnitAut p a b h α ≪≫ equalCompositeUnitAut p b c h' α =
      equalCompositeUnitAut p a c h'' α := by
  ext1
  rw [Iso.trans_hom, equalCompositeUnitAut_hom, equalCompositeUnitAut_hom,
    equalCompositeUnitAut_hom, ← equalCompositeIso_trans p a b c M h h' h'', Iso.trans_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with pullback along an arbitrary scheme map `q : V ⟶ U`. -/
lemma equalCompositeUnitAut_precomp {V : Scheme.{u}} (q : V ⟶ U) (h : a ≫ p = b ≫ p)
    (h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p) :
    equalCompositeUnitAut p (q ≫ a) (q ≫ b) h' α =
      (pullbackUnitIso q).symm ≪≫
        (Scheme.Modules.pullback q).mapIso (equalCompositeUnitAut p a b h α) ≪≫
          pullbackUnitIso q := by
  ext1
  have ha : (pullbackUnitIso (q ≫ a)).inv ≫
      (Scheme.Modules.pullbackComp q a).inv.app (SheafOfModules.unit X.ringCatSheaf) =
        (pullbackUnitIso q).inv ≫ (Scheme.Modules.pullback q).map (pullbackUnitIso a).inv := by
    rw [← pullbackUnitIso_inv_comp q a]
    simp
  have hb := pullbackUnitComposition V U X q b
  have na := (Scheme.Modules.pullbackComp q a).inv.naturality α.inv
  have nb := (Scheme.Modules.pullbackComp q b).hom.naturality α.hom
  simp only [Functor.comp_map] at na nb
  have hE := congrArg Iso.hom (equalCompositeIso_precomp p a b M q h h')
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom] at hE
  rw [equalCompositeUnitAut_hom, hE]
  simp only [Category.assoc]
  rw [reassoc_of% na, reassoc_of% ha, ← reassoc_of% nb, hb]
  simp [equalCompositeUnitAut_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Invariance under replacing `M` by an isomorphic module `N` and transporting the
trivialization through the pullback of the isomorphism. -/
lemma equalCompositeUnitAut_of_iso (h : a ≫ p = b ≫ p) {N : Y.Modules} (e : M ≅ N)
    (β : (Scheme.Modules.pullback p).obj N ≅ SheafOfModules.unit X.ringCatSheaf) :
    equalCompositeUnitAut p a b h ((Scheme.Modules.pullback p).mapIso e ≪≫ β) =
      equalCompositeUnitAut p a b h β := by
  ext1
  simp only [equalCompositeUnitAut_hom, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [equalCompositeIso_hom_naturality_assoc p a b h e.inv,
    ← Functor.map_comp_assoc (Scheme.Modules.pullback b) ((Scheme.Modules.pullback p).map e.inv),
    Iso.map_inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical trivialization `p^* O_Y ≅ O_X` gives the trivial automorphism. -/
@[simp]
lemma equalCompositeUnitAut_pullbackUnitIso (h : a ≫ p = b ≫ p) :
    equalCompositeUnitAut p a b h (pullbackUnitIso p) = Iso.refl _ := by
  ext1
  have ha := pullbackUnitIso_inv_comp a p
  have hb : (Scheme.Modules.pullbackComp b p).inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pullback b).map (pullbackUnitIso p).hom ≫ (pullbackUnitIso b).hom =
        (pullbackUnitIso (b ≫ p)).hom := by
    rw [← pullbackUnitComposition U X Y b p]
    simp
  rw [equalCompositeUnitAut_hom, equalCompositeIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% ha, hb, pullbackUnitIso_inv_pullbackCongr_hom, Iso.refl_hom]

end Automorphism

end Langlands.Scheme.Modules
