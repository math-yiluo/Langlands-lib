import Langlands.Geometry.FormalGroup.DeligneIsoBaseChange

/-! # Identity and composition for structural graded base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GradedPiSheaf

section Components

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {a : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}
  {M N : GradedPiSheaf d R a}

/-- Construct a graded isomorphism from actual total and component isomorphisms. -/
def isoOfComponents (e : M.module ≅ N.module)
    (hpi : M.pi ≫ e.hom = e.hom ≫ N.pi)
    (c : ∀ i, M.componentSheaf i ≅ N.componentSheaf i)
    (hc : ∀ i, (c i).hom ≫ N.componentInclusion i =
      M.componentInclusion i ≫ e.hom) : M ≅ N where
  hom := {
    val := ⟨e.hom, hpi⟩
    homogeneous U i x hx := by
      have h := congrArg (fun k => k.val.app U (⟨x, hx⟩ :
        (M.component i).toSubmodule.obj U)) (hc i)
      change (((c i).hom.val.app U ⟨x, hx⟩).val) = e.hom.val.app U x at h
      exact h ▸ ((c i).hom.val.app U ⟨x, hx⟩).property }
  inv := {
    val := ⟨e.inv, by
      apply (cancel_mono e.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hpi, Iso.inv_hom_id_assoc]⟩
    homogeneous U i x hx := by
      have hi : (c i).inv ≫ M.componentInclusion i =
          N.componentInclusion i ≫ e.inv := by
        apply (cancel_mono e.hom).mp
        rw [Category.assoc, ← hc i, Iso.inv_hom_id_assoc,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have h := congrArg (fun k => k.val.app U (⟨x, hx⟩ :
        (N.component i).toSubmodule.obj U)) hi
      change (((c i).inv.val.app U ⟨x, hx⟩).val) = e.inv.val.app U x at h
      exact h ▸ ((c i).inv.val.app U ⟨x, hx⟩).property }
  hom_inv_id := Hom.ext (PiSheaf.Hom.ext e.hom_inv_id)
  inv_hom_id := Hom.ext (PiSheaf.Hom.ext e.inv_hom_id)

/-- The induced homogeneous map is the supplied component comparison. -/
theorem isoOfComponents_hom_componentMap (e : M.module ≅ N.module)
    (hpi : M.pi ≫ e.hom = e.hom ≫ N.pi)
    (c : ∀ i, M.componentSheaf i ≅ N.componentSheaf i)
    (hc : ∀ i, (c i).hom ≫ N.componentInclusion i =
      M.componentInclusion i ≫ e.hom) (i : ZMod d) :
    (isoOfComponents e hpi c hc).hom.componentMap i = (c i).hom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  apply Subtype.ext
  have h := congrArg (fun k => k.val.app U x) (hc i)
  exact h.symm

end Components

variable {S S' S'' : Scheme.{u}} {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}
  (M : GradedPiSheaf d S.sheaf (schemeScalar S a))

@[reassoc (attr := simp)]
theorem pullbackComponentIso_hom_inclusion (f : S' ⟶ S) (i : ZMod d) :
    (M.pullbackComponentIso f i).hom ≫ (M.pullback f).componentInclusion i =
      (Scheme.Modules.pullback f).map (M.componentInclusion i) :=
  splitRangeIso_hom_inclusion _ _ _

@[reassoc (attr := simp)]
theorem pullbackComponentIso_inv_inclusion (f : S' ⟶ S) (i : ZMod d) :
    (M.pullbackComponentIso f i).inv ≫
        (Scheme.Modules.pullback f).map (M.componentInclusion i) =
      (M.pullback f).componentInclusion i := by
  apply (cancel_epi (M.pullbackComponentIso f i).hom).mp
  rw [Iso.hom_inv_id_assoc, M.pullbackComponentIso_hom_inclusion]

/-- The actual homogeneous component comparison for identity-base pullback. -/
def pullbackIdComponentIso (i : ZMod d) :
    (M.pullback (𝟙 S)).componentSheaf i ≅ M.componentSheaf i :=
  (M.pullbackComponentIso (𝟙 S) i).symm ≪≫
    (Scheme.Modules.pullbackId S).app (M.componentSheaf i)

@[reassoc]
theorem pullbackIdComponentIso_inclusion (i : ZMod d) :
    (M.pullbackIdComponentIso i).hom ≫ M.componentInclusion i =
      (M.pullback (𝟙 S)).componentInclusion i ≫
        (Scheme.Modules.pullbackId S).hom.app M.module := by
  change ((M.pullbackComponentIso (𝟙 S) i).inv ≫
      (Scheme.Modules.pullbackId S).hom.app (M.componentSheaf i)) ≫ _ = _
  have hn := (Scheme.Modules.pullbackId S).hom.naturality (M.componentInclusion i)
  dsimp only [Functor.id_map] at hn
  calc
    _ = (M.pullbackComponentIso (𝟙 S) i).inv ≫
        ((Scheme.Modules.pullback (𝟙 S)).map (M.componentInclusion i) ≫
          (Scheme.Modules.pullbackId S).hom.app M.module) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => (M.pullbackComponentIso (𝟙 S) i).inv ≫ k) hn.symm)
    _ = _ := by
      rw [← Category.assoc, M.pullbackComponentIso_inv_inclusion]

/-- Canonical identity-base isomorphism preserving the actual grading and Pi. -/
def pullbackIdIso : M.pullback (𝟙 S) ≅ M :=
  isoOfComponents ((Scheme.Modules.pullbackId S).app M.module)
    ((Scheme.Modules.pullbackId S).hom.naturality M.pi)
    (M.pullbackIdComponentIso) (M.pullbackIdComponentIso_inclusion)

/-- The identity-base comparison is natural for actual graded morphisms. -/
def pullbackIdNatIso :
    pullbackFunctor (d := d) (a := a) (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.pullbackIdIso) (fun g =>
    Hom.ext (PiSheaf.Hom.ext ((Scheme.Modules.pullbackId S).hom.naturality g.val.val)))

/-- The component comparison from iterated pullback to composite-base pullback. -/
def pullbackCompComponentIso (f : S' ⟶ S) (g : S'' ⟶ S') (i : ZMod d) :
    ((M.pullback f).pullback g).componentSheaf i ≅
      (M.pullback (g ≫ f)).componentSheaf i :=
  ((M.pullback f).pullbackComponentIso g i).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (M.pullbackComponentIso f i).symm ≪≫
      (Scheme.Modules.pullbackComp g f).app (M.componentSheaf i) ≪≫
        M.pullbackComponentIso (g ≫ f) i

@[reassoc]
theorem pullbackCompComponentIso_inclusion (f : S' ⟶ S) (g : S'' ⟶ S')
    (i : ZMod d) :
    (M.pullbackCompComponentIso f g i).hom ≫
        (M.pullback (g ≫ f)).componentInclusion i =
      ((M.pullback f).pullback g).componentInclusion i ≫
        (Scheme.Modules.pullbackComp g f).hom.app M.module := by
  let P := Scheme.Modules.pullback g
  let c := Scheme.Modules.pullbackComp g f
  let q := (M.pullback f).pullbackComponentIso g i
  let r := M.pullbackComponentIso f i
  have hn := c.hom.naturality (M.componentInclusion i)
  dsimp only [Functor.comp_map] at hn
  change (((M.pullback f).pullbackComponentIso g i).inv ≫
    (P.map (M.pullbackComponentIso f i).inv ≫
      (c.hom.app (M.componentSheaf i) ≫
        (M.pullbackComponentIso (g ≫ f) i).hom))) ≫ _ = _
  calc
    _ = q.inv ≫ P.map r.inv ≫ (c.hom.app (M.componentSheaf i) ≫
        (Scheme.Modules.pullback (g ≫ f)).map (M.componentInclusion i)) := by
      simp only [q, r, Category.assoc, M.pullbackComponentIso_hom_inclusion]
    _ = q.inv ≫ P.map r.inv ≫
        (P.map ((Scheme.Modules.pullback f).map (M.componentInclusion i)) ≫
          c.hom.app M.module) :=
      congrArg (fun k => q.inv ≫ P.map r.inv ≫ k) hn.symm
    _ = (q.inv ≫ P.map
        (r.inv ≫ (Scheme.Modules.pullback f).map (M.componentInclusion i))) ≫
          c.hom.app M.module := by
      simp only [P.map_comp, Category.assoc]
    _ = (q.inv ≫ P.map ((M.pullback f).componentInclusion i)) ≫
        c.hom.app M.module :=
      congrArg (fun k => (q.inv ≫ P.map k) ≫ c.hom.app M.module)
        (M.pullbackComponentIso_inv_inclusion f i)
    _ = _ := congrArg (fun k => k ≫ c.hom.app M.module)
      ((M.pullback f).pullbackComponentIso_inv_inclusion g i)

/-- Canonical composite-base comparison preserving the actual grading and Pi. -/
def pullbackCompIso (f : S' ⟶ S) (g : S'' ⟶ S') :
    (M.pullback f).pullback g ≅ M.pullback (g ≫ f) :=
  isoOfComponents ((Scheme.Modules.pullbackComp g f).app M.module)
    ((Scheme.Modules.pullbackComp g f).hom.naturality M.pi)
    (M.pullbackCompComponentIso f g) (M.pullbackCompComponentIso_inclusion f g)

/-- Composite-base comparison is natural for actual graded morphisms. -/
def pullbackCompNatIso (f : S' ⟶ S) (g : S'' ⟶ S') :
    pullbackFunctor (d := d) (a := a) f ⋙ pullbackFunctor g ≅
      pullbackFunctor (g ≫ f) :=
  NatIso.ofComponents (fun M => M.pullbackCompIso f g) (fun h =>
    Hom.ext (PiSheaf.Hom.ext
      ((Scheme.Modules.pullbackComp g f).hom.naturality h.val.val)))

variable {S''' : Scheme.{u}}

/-- The actual graded composition comparisons satisfy associativity. -/
theorem pullbackCompIso_assoc (f : S' ⟶ S) (g : S'' ⟶ S') (h : S''' ⟶ S'') :
    (pullbackFunctor h).mapIso (M.pullbackCompIso f g) ≪≫
        M.pullbackCompIso (g ≫ f) h =
      (M.pullback f).pullbackCompIso g h ≪≫ M.pullbackCompIso f (h ≫ g) := by
  apply Iso.ext
  apply Hom.ext
  apply PiSheaf.Hom.ext
  exact (congrArg (fun e => e.hom.app M.module)
    (SheafOfModules.pullback_assoc.{u}
      f.toRingCatSheafHom g.toRingCatSheafHom h.toRingCatSheafHom)).symm

/-- Composition with the identity on the original base is the pulled identity comparison. -/
theorem pullbackCompIso_id_left (f : S' ⟶ S) :
    M.pullbackCompIso (𝟙 S) f =
      (pullbackFunctor f).mapIso M.pullbackIdIso := by
  apply Iso.ext
  apply Hom.ext
  apply PiSheaf.Hom.ext
  exact congrArg (fun e => e.hom.app M.module)
    (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)

/-- Composition with the identity on the new base is the identity comparison there. -/
theorem pullbackCompIso_id_right (f : S' ⟶ S) :
    M.pullbackCompIso f (𝟙 S') = (M.pullback f).pullbackIdIso := by
  apply Iso.ext
  apply Hom.ext
  apply PiSheaf.Hom.ext
  exact congrArg (fun e => e.hom.app M.module)
    (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)

end GradedPiSheaf

end Langlands.DeligneFormalSpace
