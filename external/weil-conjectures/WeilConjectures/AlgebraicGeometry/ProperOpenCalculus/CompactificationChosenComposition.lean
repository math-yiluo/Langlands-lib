/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence

/-! # Composition for arbitrary chosen compactifications

## References

* Stacks 0F7J--0F7K, independence of a common refining tower
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProperOpenCalculus

variable {A : Scheme.{u} → Prop} (F : ProperOpenCalculus.{u, v, w} A) (G : Geometry A)

/-- The comparison is independent of the chosen common refinement by cofilteredness. -/
def comparison (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z) :
    F.H X Y c hc ≅ F.H X Y d hd := by
  classical
  let e := (G.common X Y f d c hd hc).choose
  let he := (G.common X Y f d c hd hc).choose_spec.1
  let r := (G.common X Y f d c hd hc).choose_spec.2.1.some
  let s := (G.common X Y f d c hd hc).choose_spec.2.2.some
  exact F.compare X Y hd hc he r s

/-- Computing the comparison on any supplied common refinement gives the same map. -/
theorem comparison_eq (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (r : e.Refinement d) (s : e.Refinement c) :
    comparison F G X Y f c d hc hd = F.compare X Y hd hc he r s := by
  exact (compactification_refinement_coherence F G).2.2.1 X Y f d c _ e hd hc _ he
    _ _ r s

@[simp] theorem comparison_refl (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) :
    comparison F G X Y f c c hc hc = Iso.refl _ := by
  rw [comparison_eq F G X Y f c c c hc hc hc
    (Compactification.Refinement.id c) (Compactification.Refinement.id c)]
  exact Iso.self_symm_id _

@[simp] theorem comparison_trans (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    comparison F G X Y f c d hc hd ≪≫ comparison F G X Y f d e hd he =
      comparison F G X Y f c e hc he := by
  unfold comparison
  exact (compactification_refinement_coherence F G).2.2.2.1 X Y f e d c
    _ _ _ he hd hc _ _ _ _ _ _ _ _ _

include G in
theorem binary_exists (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ T : Compactification.Triangle f g, TriangleObjects (A := A) T := by
  obtain ⟨c, hc⟩ := G.nonempty X Z (f ≫ g)
  obtain ⟨d, hd⟩ := G.nonempty Y Z g
  obtain ⟨T, hT, _⟩ := G.compatible X Y Z f g d c hd hc
  exact ⟨T, hT⟩

/-- A chosen binary tower. All resulting maps are independent of this choice. -/
def binaryTower (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    {T : Compactification.Triangle f g // TriangleObjects (A := A) T} :=
  ⟨(binary_exists G X Y Z f g).choose, (binary_exists G X Y Z f g).choose_spec⟩

/-- The composition word evaluated on a supplied binary tower. -/
def binaryOn (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (T : Compactification.Triangle f g) (hT : TriangleObjects (A := A) T) :
    F.H X Y c hc ⋙ F.H Y Z d hd ≅ F.H X Z e he :=
  NatIso.hcomp (comparison F G X Y f c T.cf hc hT.1)
      (comparison F G Y Z g d T.cg hd hT.2.1) ≪≫
    F.towerIso X Y Z T hT ≪≫ comparison F G X Z (f ≫ g) T.cfg e hT.2.2 he

/-- Independence of the binary-tower choice, as an equality before any evaluation. -/
theorem binaryOn_independent (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (T S : Compactification.Triangle f g)
    (hT : TriangleObjects (A := A) T) (hS : TriangleObjects (A := A) S) :
    binaryOn F G X Y Z f g c d e hc hd he T hT =
      binaryOn F G X Y Z f g c d e hc hd he S hS := by
  obtain ⟨R, hR, ⟨r⟩, ⟨s⟩⟩ := G.towers X Y Z f g T S hT hS
  have ht := (compactification_refinement_coherence F G).2.2.2.2.1
    X Y Z f g T S R hT hS hR r s
  rw [← comparison_eq F G X Z (f ≫ g) T.cfg S.cfg R.cfg hT.2.2 hS.2.2 hR.2.2
    s.rfg r.rfg,
    ← comparison_eq F G X Y f T.cf S.cf R.cf hT.1 hS.1 hR.1 s.rf r.rf,
    ← comparison_eq F G Y Z g T.cg S.cg R.cg hT.2.1 hS.2.1 hR.2.1 s.rg r.rg] at ht
  apply Iso.ext
  simp only [binaryOn, Iso.trans_hom, NatIso.hcomp_hom]
  have hf := congrArg Iso.hom (comparison_trans F G X Y f c T.cf S.cf hc hT.1 hS.1)
  have hg := congrArg Iso.hom (comparison_trans F G Y Z g d T.cg S.cg hd hT.2.1 hS.2.1)
  have he' := congrArg Iso.hom
    (comparison_trans F G X Z (f ≫ g) T.cfg S.cfg e hT.2.2 hS.2.2 he)
  simp only [Iso.trans_hom] at hf hg he'
  rw [← hf, ← hg, NatTrans.exchange]
  simpa only [Category.assoc, he'] using congrArg
    (fun a ↦ NatTrans.hcomp (comparison F G X Y f c T.cf hc hT.1).hom
      (comparison F G Y Z g d T.cg hd hT.2.1).hom ≫ a ≫
        (comparison F G X Z (f ≫ g) S.cfg e hS.2.2 he).hom) ht

/-- Composition between arbitrary compactification models. -/
def binary (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    F.H X Y c hc ⋙ F.H Y Z d hd ≅ F.H X Z e he :=
  binaryOn F G X Y Z f g c d e hc hd he (binaryTower G X Y Z f g).val
    (binaryTower G X Y Z f g).property

/-- The chosen binary composition can be computed on any supplied tower. -/
theorem binary_eq (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (T : Compactification.Triangle f g) (hT : TriangleObjects (A := A) T) :
    binary F G X Y Z f g c d e hc hd he =
      binaryOn F G X Y Z f g c d e hc hd he T hT :=
  binaryOn_independent F G X Y Z f g c d e hc hd he _ T _ hT

/-- On a compatible tower its binary composition is exactly the specified tower word. -/
theorem binary_tower (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (T : Compactification.Triangle f g) (hT : TriangleObjects (A := A) T) :
    binary F G X Y Z f g T.cf T.cg T.cfg hT.1 hT.2.1 hT.2.2 =
      F.towerIso X Y Z T hT := by
  rw [binary_eq F G X Y Z f g T.cf T.cg T.cfg hT.1 hT.2.1 hT.2.2 T hT]
  apply Iso.ext
  ext M
  simp [binaryOn, comparison_refl, NatIso.hcomp]

/-- Simultaneous change of all three compactifications commutes with composition. -/
theorem binary_refinement (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c c' : Compactification f) (d d' : Compactification g)
    (e e' : Compactification (f ≫ g))
    (hc : A c.Z) (hc' : A c'.Z) (hd : A d.Z) (hd' : A d'.Z)
    (he : A e.Z) (he' : A e'.Z) :
    (NatIso.hcomp (comparison F G X Y f c c' hc hc')
      (comparison F G Y Z g d d' hd hd')).hom ≫
        (binary F G X Y Z f g c' d' e' hc' hd' he').hom =
      (binary F G X Y Z f g c d e hc hd he).hom ≫
        (comparison F G X Z (f ≫ g) e e' he he').hom := by
  simp only [binary, binaryOn, Iso.trans_hom, NatIso.hcomp_hom]
  simp only [← Category.assoc, ← NatTrans.exchange, ← Iso.trans_hom,
    comparison_trans]
  have ht := congrArg Iso.hom
    (comparison_trans F G X Z (f ≫ g) (binaryTower G X Y Z f g).val.cfg e e'
      (binaryTower G X Y Z f g).property.2.2 he he')
  simp only [Iso.trans_hom] at ht
  simp only [Iso.trans_hom, Category.assoc]
  rw [ht]

/-- The identity comparison is obtained from the trivial proper compactification. -/
def chosenIdentity (X : {X : Scheme.{u} // A X})
    (c : Compactification (𝟙 X.val)) (hc : A c.Z) :
    F.H X X c hc ≅ 𝟭 (F.obj X) :=
  comparison F G X X (𝟙 X.val) c (Compactification.ofIsProper (𝟙 X.val)) hc X.property ≪≫
    F.identityIso X

/-- The left identity law for an arbitrary identity compactification. -/
theorem binary_left (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 X.val)) (hi : A i.Z) :
    (binaryOn F G X X Y (𝟙 X.val) f i c
      (c.copy (Category.id_comp f)) hi hc hc
      (Compactification.Triangle.unitLeft c) ⟨X.property, hc, hc⟩).hom =
      Functor.whiskerRight (chosenIdentity F G X i hi).hom (F.H X Y c hc) ≫
        (Functor.leftUnitor _).hom := by
  have hu := (compactification_refinement_coherence F G).2.2.2.2.2.2.1 X Y f c hc
  unfold binaryOn
  simp only [Iso.trans_hom, NatIso.hcomp_hom]
  rw [hu]
  ext M
  dsimp only [Compactification.Triangle.unitLeft, H, Compactification.copy]
  simp [comparison_refl, chosenIdentity, H, Category.assoc]

/-- The right identity law for an arbitrary identity compactification. -/
theorem binary_right (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 Y.val)) (hi : A i.Z) :
    (binaryOn F G X Y Y f (𝟙 Y.val) c i
      (c.copy (Category.comp_id f)) hc hi hc
      (Compactification.Triangle.unitRight c) ⟨hc, Y.property, hc⟩).hom =
      Functor.whiskerLeft (F.H X Y c hc) (chosenIdentity F G Y i hi).hom ≫
        (Functor.rightUnitor _).hom := by
  have hu := (compactification_refinement_coherence F G).2.2.2.2.2.2.2 X Y f c hc
  unfold binaryOn
  simp only [Iso.trans_hom, NatIso.hcomp_hom]
  rw [hu]
  ext M
  dsimp only [Compactification.Triangle.unitRight, H, Compactification.copy]
  simp [comparison_refl, chosenIdentity, H, Category.assoc]

section AssociativityTransfer
variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]

private theorem associativity_transfer
    {f f' : C₁ ⥤ C₂} {g g' : C₂ ⥤ C₃} {h h' : C₃ ⥤ C₄}
    {fg fg' : C₁ ⥤ C₃} {gh gh' : C₂ ⥤ C₄} {fgh fgh' : C₁ ⥤ C₄}
    (a : f ≅ f') (b : g ≅ g') (c : h ≅ h')
    (ab : fg ≅ fg') (bc : gh ≅ gh') (abc : fgh ≅ fgh')
    (α : f ⋙ g ≅ fg) (α' : f' ⋙ g' ≅ fg')
    (β : g ⋙ h ≅ gh) (β' : g' ⋙ h' ≅ gh')
    (δ : fg ⋙ h ≅ fgh) (δ' : fg' ⋙ h' ≅ fgh')
    (ε : f ⋙ gh ≅ fgh) (ε' : f' ⋙ gh' ≅ fgh')
    (ha : NatTrans.hcomp a.hom b.hom ≫ α'.hom = α.hom ≫ ab.hom)
    (hb : NatTrans.hcomp b.hom c.hom ≫ β'.hom = β.hom ≫ bc.hom)
    (hc : NatTrans.hcomp ab.hom c.hom ≫ δ'.hom = δ.hom ≫ abc.hom)
    (hd : NatTrans.hcomp a.hom bc.hom ≫ ε'.hom = ε.hom ≫ abc.hom)
    (hp : Functor.whiskerRight α'.hom h' ≫ δ'.hom =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft f' β'.hom ≫ ε'.hom) :
    Functor.whiskerRight α.hom h ≫ δ.hom =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft f β.hom ≫ ε.hom := by
  ext M
  apply (cancel_mono (abc.hom.app M)).mp
  have hα := NatTrans.congr_app ha M
  have hβ := NatTrans.congr_app hb (f.obj M)
  have hδ := NatTrans.congr_app hc M
  have hε := NatTrans.congr_app hd M
  have hprimed := NatTrans.congr_app hp M
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.comp_obj] at hα hβ hδ hε hprimed ⊢
  simp only [Category.id_comp] at hprimed ⊢
  simp only [Category.assoc]
  rw [← hδ, ← hε]
  rw [← Category.assoc, ← Category.assoc, c.hom.naturality (α.hom.app M)]
  simp only [Category.assoc]
  rw [← Category.assoc (h'.map (α.hom.app M)), ← Functor.map_comp, ← hα,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hprimed]
  have hn := β'.hom.naturality (a.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (h'.map (g'.map (a.hom.app M))), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (β.hom.app (f.obj M)), ← hβ]
  simp only [Category.assoc, Functor.comp_obj]

end AssociativityTransfer

/-- Composition with a named composite, retaining the original compactification data. -/
def namedBinary (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg : X.val ⟶ Z.val) (wfg : f ≫ g = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact fg]
    (c : Compactification f) (d : Compactification g) (e : Compactification fg)
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    F.H X Y c hc ⋙ F.H Y Z d hd ≅ F.H X Z e he :=
  binary F G X Y Z f g c d (e.copy wfg) hc hd he

/-- A reflexively named composite gives the original binary word. -/
@[simp] theorem namedBinary_rfl (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    namedBinary F G X Y Z f g (f ≫ g) rfl c d e hc hd he =
      binary F G X Y Z f g c d e hc hd he := by
  rfl

/-- The named left unit word uses exactly the given compactification of f. -/
theorem namedBinary_left (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 X.val)) (hi : A i.Z) :
    (namedBinary F G X X Y (𝟙 X.val) f f (Category.id_comp f) i c c hi hc hc).hom =
      Functor.whiskerRight (chosenIdentity F G X i hi).hom (F.H X Y c hc) ≫
        (Functor.leftUnitor _).hom := by
  unfold namedBinary
  rw [binary_eq F G X X Y (𝟙 X.val) f i c (c.copy (Category.id_comp f)) hi hc hc
    (Compactification.Triangle.unitLeft c) ⟨X.property, hc, hc⟩]
  exact binary_left F G X Y f c hc i hi

/-- The named right unit word uses exactly the given compactification of f. -/
theorem namedBinary_right (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 Y.val)) (hi : A i.Z) :
    (namedBinary F G X Y Y f (𝟙 Y.val) f (Category.comp_id f) c i c hc hi hc).hom =
      Functor.whiskerLeft (F.H X Y c hc) (chosenIdentity F G Y i hi).hom ≫
        (Functor.rightUnitor _).hom := by
  unfold namedBinary
  rw [binary_eq F G X Y Y f (𝟙 Y.val) c i (c.copy (Category.comp_id f)) hc hi hc
    (Compactification.Triangle.unitRight c) ⟨hc, Y.property, hc⟩]
  exact binary_right F G X Y f c hc i hi

/-- Copying the arrow equality does not change a comparison word. -/
theorem comparison_copy (X Y : {X : Scheme.{u} // A X})
    {f f' : X.val ⟶ Y.val} (wff : f' = f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z) :
    comparison F G X Y f' (c.copy wff) (d.copy wff) hc hd =
      comparison F G X Y f c d hc hd := by
  subst f'
  rfl

/-- Refinement compatibility also holds with a named composite. -/
theorem namedBinary_refinement (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg : X.val ⟶ Z.val) (wfg : f ≫ g = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated fg] [LocallyOfFiniteType fg] [QuasiCompact fg]
    (c c' : Compactification f) (d d' : Compactification g)
    (e e' : Compactification fg)
    (hc : A c.Z) (hc' : A c'.Z) (hd : A d.Z) (hd' : A d'.Z)
    (he : A e.Z) (he' : A e'.Z) :
    (NatIso.hcomp (comparison F G X Y f c c' hc hc')
      (comparison F G Y Z g d d' hd hd')).hom ≫
        (namedBinary F G X Y Z f g fg wfg c' d' e' hc' hd' he').hom =
      (namedBinary F G X Y Z f g fg wfg c d e hc hd he).hom ≫
        (comparison F G X Z fg e e' he he').hom := by
  subst fg
  exact binary_refinement F G X Y Z f g c c' d d' e e' hc hc' hd hd' he he'

/-- Associativity for arbitrary compactifications, obtained by a common staircase. -/
theorem namedBinary_associativity (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (h : Z.val ⟶ W.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (cd : Compactification (f ≫ g)) (de : Compactification (g ≫ h))
    (cde : Compactification (f ≫ g ≫ h))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (hcd : A cd.Z) (hde : A de.Z) (hcde : A cde.Z) :
    Functor.whiskerRight (binary F G X Y Z f g c d cd hc hd hcd).hom (F.H Z W e he) ≫
        (namedBinary F G X Z W (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)
          cd e cde hcd he hcde).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.H X Y c hc) (binary F G Y Z W g h d e de hd he hde).hom ≫
          (binary F G X Y W f (g ≫ h) c de cde hc hde hcde).hom := by
  obtain ⟨T, hT⟩ := G.staircases X Y Z W f g h
  let hfg : TriangleObjects (A := A) T.fg := ⟨hT.1, hT.2.1, hT.2.2.2.1⟩
  let hgh : TriangleObjects (A := A) T.gh := ⟨hT.2.1, hT.2.2.1, hT.2.2.2.2.1⟩
  let hfg_h : TriangleObjects (A := A) T.fg_h :=
    ⟨hT.2.2.2.1, hT.2.2.1, hT.2.2.2.2.2⟩
  let hf_gh : TriangleObjects (A := A) T.f_gh :=
    ⟨hT.1, hT.2.2.2.2.1, hT.2.2.2.2.2⟩
  have hδ : namedBinary F G X Z W (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)
      T.cfg T.ch T.cfgh hT.2.2.2.1 hT.2.2.1 hT.2.2.2.2.2 =
      F.towerIso X Z W T.fg_h hfg_h :=
    binary_tower F G X Z W (f ≫ g) h T.fg_h hfg_h
  refine associativity_transfer
    (comparison F G X Y f c T.cf hc hT.1)
    (comparison F G Y Z g d T.cg hd hT.2.1)
    (comparison F G Z W h e T.ch he hT.2.2.1)
    (comparison F G X Z (f ≫ g) cd T.cfg hcd hT.2.2.2.1)
    (comparison F G Y W (g ≫ h) de T.cgh hde hT.2.2.2.2.1)
    (comparison F G X W (f ≫ g ≫ h) cde T.cfgh hcde hT.2.2.2.2.2)
    (binary F G X Y Z f g c d cd hc hd hcd) (F.towerIso X Y Z T.fg hfg)
    (binary F G Y Z W g h d e de hd he hde) (F.towerIso Y Z W T.gh hgh)
    (namedBinary F G X Z W (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)
      cd e cde hcd he hcde) (F.towerIso X Z W T.fg_h hfg_h)
    (binary F G X Y W f (g ≫ h) c de cde hc hde hcde)
    (F.towerIso X Y W T.f_gh hf_gh) ?_ ?_ ?_ ?_ ?_
  · have ht := binary_refinement F G X Y Z f g c T.cf d T.cg cd T.cfg
        hc hT.1 hd hT.2.1 hcd hT.2.2.2.1
    rw [show binary F G X Y Z f g T.cf T.cg T.cfg hT.1 hT.2.1 hT.2.2.2.1 =
      F.towerIso X Y Z T.fg hfg from binary_tower F G X Y Z f g T.fg hfg] at ht
    exact ht
  · have ht := binary_refinement F G Y Z W g h d T.cg e T.ch de T.cgh
        hd hT.2.1 he hT.2.2.1 hde hT.2.2.2.2.1
    rw [show binary F G Y Z W g h T.cg T.ch T.cgh hT.2.1 hT.2.2.1 hT.2.2.2.2.1 =
      F.towerIso Y Z W T.gh hgh from binary_tower F G Y Z W g h T.gh hgh] at ht
    exact ht
  · rw [← hδ]
    exact namedBinary_refinement F G X Z W (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)
      cd T.cfg e T.ch cde T.cfgh hcd hT.2.2.2.1 he hT.2.2.1 hcde hT.2.2.2.2.2
  · have ht := binary_refinement F G X Y W f (g ≫ h) c T.cf de T.cgh cde T.cfgh
        hc hT.1 hde hT.2.2.2.2.1 hcde hT.2.2.2.2.2
    rw [show binary F G X Y W f (g ≫ h) T.cf T.cgh T.cfgh
      hT.1 hT.2.2.2.2.1 hT.2.2.2.2.2 = F.towerIso X Y W T.f_gh hf_gh from
        binary_tower F G X Y W f (g ≫ h) T.f_gh hf_gh] at ht
    exact ht
  · exact (compactification_refinement_coherence F G).2.2.2.2.2.1 X Y Z W f g h T hT

end AlgebraicGeometry.ProperOpenCalculus
