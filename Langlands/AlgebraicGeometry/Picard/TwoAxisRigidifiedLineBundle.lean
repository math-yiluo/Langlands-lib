import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidificationPullback
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf

/-! # Line bundles with two compatible axis rigidifications -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {S X Y Z S' X' Y' Z' S'' X'' Y'' Z'' : Scheme.{u}}

/-- An actual module sheaf with compatible trivializations along two axes. -/
structure TwoAxisRigidifiedModule (e : S ⟶ X) (t : S ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (h : e ≫ i = t ≫ j) where
  carrier : Z.Modules
  rigidification : TwoAxisRigidification e t i j h carrier

namespace TwoAxisRigidifiedModule

variable {e : S ⟶ X} {t : S ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
  {h : e ≫ i = t ≫ j}
variable {e' : S' ⟶ X'} {t' : S' ⟶ Y'} {i' : X' ⟶ Z'} {j' : Y' ⟶ Z'}
  {h' : e' ≫ i' = t' ≫ j'}
variable {e'' : S'' ⟶ X''} {t'' : S'' ⟶ Y''}
  {i'' : X'' ⟶ Z''} {j'' : Y'' ⟶ Z''} {h'' : e'' ≫ i'' = t'' ≫ j''}

/-- Morphisms preserve both chosen trivializations. -/
def Hom (M N : TwoAxisRigidifiedModule e t i j h) :=
  {f : M.carrier ⟶ N.carrier //
    (M.rigidification.first.hom ≫ (Scheme.Modules.pullback i).map f =
      N.rigidification.first.hom) ∧
    (M.rigidification.second.hom ≫ (Scheme.Modules.pullback j).map f =
      N.rigidification.second.hom)}

instance : Category (TwoAxisRigidifiedModule e t i j h) where
  Hom := Hom
  id M := ⟨𝟙 M.carrier, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by
    constructor
    · rw [Functor.map_comp, ← Category.assoc, f.property.1, g.property.1]
    · rw [Functor.map_comp, ← Category.assoc, f.property.2, g.property.2]⟩
  id_comp f := by apply Subtype.ext; exact Category.id_comp f.val
  comp_id f := by apply Subtype.ext; exact Category.comp_id f.val
  assoc f g k := by apply Subtype.ext; exact Category.assoc f.val g.val k.val

/-- Forget both rigidifications, keeping the actual module sheaf. -/
def forget (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e ≫ i = t ≫ j) : TwoAxisRigidifiedModule e t i j h ⥤ Z.Modules where
  obj M := M.carrier
  map f := f.val

instance : (forget e t i j h).Faithful where
  map_injective := Subtype.ext

/-- An isomorphism of actual modules preserving both axis trivializations. -/
def isoMk {M N : TwoAxisRigidifiedModule e t i j h} (f : M.carrier ≅ N.carrier)
    (first : M.rigidification.first.hom ≫ (Scheme.Modules.pullback i).map f.hom =
      N.rigidification.first.hom)
    (second : M.rigidification.second.hom ≫ (Scheme.Modules.pullback j).map f.hom =
      N.rigidification.second.hom) : M ≅ N where
  hom := ⟨f.hom, first, second⟩
  inv := ⟨f.inv, by
    constructor
    · rw [← first, Category.assoc, ← Functor.map_comp, f.hom_inv_id]
      simp
    · rw [← second, Category.assoc, ← Functor.map_comp, f.hom_inv_id]
      simp⟩
  hom_inv_id := by apply Subtype.ext; exact f.hom_inv_id
  inv_hom_id := by apply Subtype.ext; exact f.inv_hom_id

/-- Canonical pullback along a map of the full two-axis diagrams. -/
def pullback
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fy : Y' ⟶ Y) (fs : S' ⟶ S)
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t) :
    TwoAxisRigidifiedModule e t i j h ⥤ TwoAxisRigidifiedModule e' t' i' j' h' where
  obj M := ⟨(Scheme.Modules.pullback fz).obj M.carrier,
    M.rigidification.pullback fz fx fy fs hi hj he ht⟩
  map {M N} f := ⟨(Scheme.Modules.pullback fz).map f.val,
    ((RigidifiedModule.pullback fz fx hi).map
      (show (⟨M.carrier, M.rigidification.first⟩ : RigidifiedModule i) ⟶
        ⟨N.carrier, N.rigidification.first⟩ from ⟨f.val, f.property.1⟩)).property,
    ((RigidifiedModule.pullback fz fy hj).map
      (show (⟨M.carrier, M.rigidification.second⟩ : RigidifiedModule j) ⟶
        ⟨N.carrier, N.rigidification.second⟩ from ⟨f.val, f.property.2⟩)).property⟩
  map_id M := by apply Subtype.ext; exact (Scheme.Modules.pullback fz).map_id M.carrier
  map_comp f g := by
    apply Subtype.ext
    exact (Scheme.Modules.pullback fz).map_comp f.val g.val

/-- The ordinary identity comparison preserves both rigidifications. -/
def pullbackId (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e ≫ i = t ≫ j) :
    pullback (h' := h) (𝟙 Z) (𝟙 X) (𝟙 Y) (𝟙 S)
      (by simp) (by simp) (by simp) (by simp) ≅
      𝟭 (TwoAxisRigidifiedModule e t i j h) :=
  NatIso.ofComponents
    (fun M ↦ isoMk ((Scheme.Modules.pullbackId Z).app M.carrier)
      (RigidifiedModule.pullbackIdentity X Z i _ ⟨M.carrier, M.rigidification.first⟩)
      (RigidifiedModule.pullbackIdentity Y Z j _ ⟨M.carrier, M.rigidification.second⟩))
    (by intro M N f; apply Subtype.ext
        exact (Scheme.Modules.pullbackId Z).hom.naturality f.val)

/-- The ordinary composition comparison preserves both rigidifications. -/
def pullbackComp
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fy : Y' ⟶ Y) (fs : S' ⟶ S)
    (gz : Z'' ⟶ Z') (gx : X'' ⟶ X') (gy : Y'' ⟶ Y') (gs : S'' ⟶ S')
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t)
    (hi' : i'' ≫ gz = gx ≫ i') (hj' : j'' ≫ gz = gy ≫ j')
    (he' : e'' ≫ gx = gs ≫ e') (ht' : t'' ≫ gy = gs ≫ t')
    (hi'' : i'' ≫ (gz ≫ fz) = (gx ≫ fx) ≫ i)
    (hj'' : j'' ≫ (gz ≫ fz) = (gy ≫ fy) ≫ j)
    (he'' : e'' ≫ (gx ≫ fx) = (gs ≫ fs) ≫ e)
    (ht'' : t'' ≫ (gy ≫ fy) = (gs ≫ fs) ≫ t) :
    pullback (h := h) (h' := h') fz fx fy fs hi hj he ht ⋙
        pullback (h' := h'') gz gx gy gs hi' hj' he' ht' ≅
      pullback (h := h) (h' := h'') (gz ≫ fz) (gx ≫ fx) (gy ≫ fy) (gs ≫ fs)
        hi'' hj'' he'' ht'' :=
  NatIso.ofComponents
    (fun M ↦ isoMk ((Scheme.Modules.pullbackComp gz fz).app M.carrier)
      (RigidifiedModule.pullbackComposition X Z X' Z' X'' Z'' i i' i''
        fz fx gz gx hi hi' hi'' ⟨M.carrier, M.rigidification.first⟩)
      (RigidifiedModule.pullbackComposition Y Z Y' Z' Y'' Z'' j j' j''
        fz fy gz gy hj hj' hj'' ⟨M.carrier, M.rigidification.second⟩))
    (by intro M N f; apply Subtype.ext
        exact (Scheme.Modules.pullbackComp gz fz).hom.naturality f.val)

/-- Equal maps induce isomorphic pullbacks, independently of equation witnesses. -/
def pullbackCongr
    {fz gz : Z' ⟶ Z} {fx gx : X' ⟶ X} {fy gy : Y' ⟶ Y} {fs gs : S' ⟶ S}
    (hz : fz = gz) (hx : fx = gx) (hy : fy = gy) (hs : fs = gs)
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t)
    (hi' : i' ≫ gz = gx ≫ i) (hj' : j' ≫ gz = gy ≫ j)
    (he' : e' ≫ gx = gs ≫ e) (ht' : t' ≫ gy = gs ≫ t) :
    pullback (h := h) (h' := h') fz fx fy fs hi hj he ht ≅
      pullback (h := h) (h' := h') gz gx gy gs hi' hj' he' ht' := by
  subst gz gx gy gs
  exact Iso.refl _

end TwoAxisRigidifiedModule

/-- Two-axis-rigidified modules locally free of rank one. -/
abbrev TwoAxisRigidifiedLineBundle (e : S ⟶ X) (t : S ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (h : e ≫ i = t ≫ j) :=
  ObjectProperty.FullSubcategory
    (fun M : TwoAxisRigidifiedModule e t i j h ↦ IsLocallyFreeRankOne M.carrier)

namespace TwoAxisRigidifiedLineBundle

variable {e : S ⟶ X} {t : S ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
  {h : e ≫ i = t ≫ j}
variable {e' : S' ⟶ X'} {t' : S' ⟶ Y'} {i' : X' ⟶ Z'} {j' : Y' ⟶ Z'}
  {h' : e' ≫ i' = t' ≫ j'}
variable {e'' : S'' ⟶ X''} {t'' : S'' ⟶ Y''}
  {i'' : X'' ⟶ Z''} {j'' : Y'' ⟶ Z''} {h'' : e'' ≫ i'' = t'' ≫ j''}

/-- Equip an actual line bundle with two compatible axis trivializations. -/
def ofLineBundle (L : LineBundle Z) (ρ : TwoAxisRigidification e t i j h L.obj) :
    TwoAxisRigidifiedLineBundle e t i j h :=
  ⟨⟨L.obj, ρ⟩, L.property⟩

/-- Forget only local rank one, retaining both rigidifications. -/
def forgetToRigidified (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e ≫ i = t ≫ j) :
    TwoAxisRigidifiedLineBundle e t i j h ⥤ TwoAxisRigidifiedModule e t i j h :=
  ObjectProperty.ι _

/-- Forget the rigidifications, retaining the actual line bundle. -/
def forget (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e ≫ i = t ≫ j) : TwoAxisRigidifiedLineBundle e t i j h ⥤ LineBundle Z :=
  ObjectProperty.lift IsLocallyFreeRankOne
    (forgetToRigidified e t i j h ⋙ TwoAxisRigidifiedModule.forget e t i j h)
    (fun L ↦ L.property)

instance : (forget e t i j h).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    exact congrArg (fun k ↦ k.hom) h

/-- Lift a module isomorphism preserving both chosen axis trivializations. -/
def isoMk {L M : TwoAxisRigidifiedLineBundle e t i j h}
    (f : L.obj.carrier ≅ M.obj.carrier)
    (first : L.obj.rigidification.first.hom ≫ (Scheme.Modules.pullback i).map f.hom =
      M.obj.rigidification.first.hom)
    (second : L.obj.rigidification.second.hom ≫ (Scheme.Modules.pullback j).map f.hom =
      M.obj.rigidification.second.hom) : L ≅ M :=
  ObjectProperty.isoMk _ (TwoAxisRigidifiedModule.isoMk f first second)

/-- Pullback of actual line bundles with their compatible rigidifications. -/
def pullback
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fy : Y' ⟶ Y) (fs : S' ⟶ S)
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t) :
    TwoAxisRigidifiedLineBundle e t i j h ⥤ TwoAxisRigidifiedLineBundle e' t' i' j' h' :=
  ObjectProperty.lift
    (fun M : TwoAxisRigidifiedModule e' t' i' j' h' ↦ IsLocallyFreeRankOne M.carrier)
    (forgetToRigidified e t i j h ⋙ TwoAxisRigidifiedModule.pullback fz fx fy fs hi hj he ht)
    (fun L ↦ L.property.pullback fz)

/-- Forgetting rigidification recovers the actual line-bundle pullback. -/
def pullbackForgetIso
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fy : Y' ⟶ Y) (fs : S' ⟶ S)
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t) :
    pullback fz fx fy fs hi hj he ht ⋙ forget e' t' i' j' h' ≅
      forget e t i j h ⋙ LineBundle.pullback fz :=
  Iso.refl _

/-- Unconditional identity comparison for two-axis-rigidified line bundles. -/
def pullbackId (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e ≫ i = t ≫ j) :
    pullback (h' := h) (𝟙 Z) (𝟙 X) (𝟙 Y) (𝟙 S)
      (by simp) (by simp) (by simp) (by simp) ≅
      𝟭 (TwoAxisRigidifiedLineBundle e t i j h) :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _ ((TwoAxisRigidifiedModule.pullbackId e t i j h).app L.obj))
    (by intro L M f; apply ObjectProperty.hom_ext
        exact (TwoAxisRigidifiedModule.pullbackId e t i j h).hom.naturality f.hom)

/-- Unconditional composition comparison for two-axis-rigidified line bundles. -/
def pullbackComp
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fy : Y' ⟶ Y) (fs : S' ⟶ S)
    (gz : Z'' ⟶ Z') (gx : X'' ⟶ X') (gy : Y'' ⟶ Y') (gs : S'' ⟶ S')
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t)
    (hi' : i'' ≫ gz = gx ≫ i') (hj' : j'' ≫ gz = gy ≫ j')
    (he' : e'' ≫ gx = gs ≫ e') (ht' : t'' ≫ gy = gs ≫ t')
    (hi'' : i'' ≫ (gz ≫ fz) = (gx ≫ fx) ≫ i)
    (hj'' : j'' ≫ (gz ≫ fz) = (gy ≫ fy) ≫ j)
    (he'' : e'' ≫ (gx ≫ fx) = (gs ≫ fs) ≫ e)
    (ht'' : t'' ≫ (gy ≫ fy) = (gs ≫ fs) ≫ t) :
    pullback (h := h) (h' := h') fz fx fy fs hi hj he ht ⋙
        pullback (h' := h'') gz gx gy gs hi' hj' he' ht' ≅
      pullback (h := h) (h' := h'') (gz ≫ fz) (gx ≫ fx) (gy ≫ fy) (gs ≫ fs)
        hi'' hj'' he'' ht'' :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _
      ((TwoAxisRigidifiedModule.pullbackComp fz fx fy fs gz gx gy gs hi hj he ht
        hi' hj' he' ht' hi'' hj'' he'' ht'').app L.obj))
    (by intro L M f; apply ObjectProperty.hom_ext
        exact (TwoAxisRigidifiedModule.pullbackComp fz fx fy fs gz gx gy gs hi hj he ht
          hi' hj' he' ht' hi'' hj'' he'' ht'').hom.naturality f.hom)

/-- Equal diagram maps induce isomorphic line-bundle pullbacks. -/
def pullbackCongr
    {fz gz : Z' ⟶ Z} {fx gx : X' ⟶ X} {fy gy : Y' ⟶ Y} {fs gs : S' ⟶ S}
    (hz : fz = gz) (hx : fx = gx) (hy : fy = gy) (hs : fs = gs)
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t)
    (hi' : i' ≫ gz = gx ≫ i) (hj' : j' ≫ gz = gy ≫ j)
    (he' : e' ≫ gx = gs ≫ e) (ht' : t' ≫ gy = gs ≫ t) :
    pullback (h := h) (h' := h') fz fx fy fs hi hj he ht ≅
      pullback (h := h) (h' := h') gz gx gy gs hi' hj' he' ht' := by
  subst gz gx gy gs
  exact Iso.refl _

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
