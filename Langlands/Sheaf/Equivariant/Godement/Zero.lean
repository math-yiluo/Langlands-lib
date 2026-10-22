import Langlands.Sheaf.Equivariant.Godement.Stalks
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The equivariant sheaf of arbitrary stalk-valued sections

Over `U` the constructed sheaf consists of all families `(s_x)_{x ∈ U}` with
`s_x ∈ F_x`. Labelled restriction uses the actual stalk transport maps.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u uG

variable {R : Type u} [CommRing R]
variable {G : Type uG} [Group G] {X : Type u} [TopologicalSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

/-- Arbitrary families of stalk elements over one open. -/
abbrev StalkSections (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (U : ActionOpens G X) :=
  ∀ x : U.openSet, ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x.1

/-- The identity transport evaluates a dependent family at the same point. -/
theorem stalkPull_one_section (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (U : Opens X) (s : ∀ x : U, ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x.1)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : (1 : G) • x = y) :
    stalkPull F 1 x y h (s ⟨y, hy⟩) = s ⟨x, hx⟩ := by
  have hyx : y = x := h.symm.trans (one_smul G x)
  revert h
  subst y
  intro h
  rw [stalkPull_one]
  rfl

/-- Pullback of a family of germs along a labelled open arrow. -/
def stalkSectionsPull (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    {U V : ActionOpens G X} (f : U ⟶ V) :
    StalkSections F V →ₗ[R] StalkSections F U where
  toFun s x := stalkPull F f.label x.1 (f.label • x.1) rfl
    (s ⟨f.label • x.1, f.mapsTo x.1 x.2⟩)
  map_add' s t := by ext x; exact map_add _ _ _
  map_smul' r s := by ext x; exact map_smul _ _ _

/-- The actual transport presheaf of arbitrary stalk-valued sections. -/
def zeroPresheaf (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (StalkSections F U.unop)
  map f := ModuleCat.ofHom (stalkSectionsPull F f.unop)
  map_id U := by
    ext s x
    exact stalkPull_one_section F U.unop.openSet s x.1 _ x.2 _ rfl
  map_comp {U V W} f k := by
    ext s x
    change stalkPull F (f.unop.label * k.unop.label) x.1
        ((f.unop.label * k.unop.label) • x.1) rfl
        (s ⟨_, _⟩) =
      stalkPull F k.unop.label x.1 (k.unop.label • x.1) rfl
        (stalkPull F f.unop.label (k.unop.label • x.1)
          (f.unop.label • (k.unop.label • x.1)) rfl (s ⟨_, _⟩))
    have aux : ∀ (z : X) (hz : (f.unop.label * k.unop.label) • x.1 = z)
        (hmem : z ∈ U.unop.openSet),
        stalkPull F (f.unop.label * k.unop.label) x.1 z hz (s ⟨z, hmem⟩) =
          stalkPull F k.unop.label x.1 (k.unop.label • x.1) rfl
            (stalkPull F f.unop.label (k.unop.label • x.1)
              (f.unop.label • (k.unop.label • x.1)) rfl
                (s ⟨_, f.unop.mapsTo _ (k.unop.mapsTo _ x.2)⟩)) := by
      intro z hz hmem
      have hzx : z = f.unop.label • (k.unop.label • x.1) :=
        hz.symm.trans (mul_smul _ _ _)
      revert hz
      subst z
      intro hz
      rw [stalkPull_mul F k.unop.label f.unop.label x.1
        (k.unop.label • x.1) (f.unop.label • (k.unop.label • x.1)) rfl rfl]
      rfl
    exact aux _ rfl _

/-- Ordinary restriction is the dependent-function presheaf on the stalk family. -/
def zeroUnderlyingIso (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (underlyingPresheaf G X (ModuleCat.{u} R)).obj (zeroPresheaf F) ⋙ forget (ModuleCat.{u} R) ≅
      TopCat.presheafToTypes (TopCat.of X) (fun x => ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).stalk x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro s
    funext x
    exact stalkPull_one_section F U.unop s x.1 _ (f.unop.le x.2) _ rfl)

/-- Arbitrary stalk families satisfy the actual module-valued sheaf condition. -/
theorem zero_isSheaf (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (zeroPresheaf F)).IsSheaf := by
  apply (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
    (Opens.grothendieckTopology X) _ (forget (ModuleCat.{u} R))).2
  exact (TopCat.Presheaf.isSheaf_iso_iff (zeroUnderlyingIso F)).2
    (TopCat.Presheaf.toTypes_isSheaf (TopCat.of X) _)

/-- The constructed equivariant sheaf of arbitrary stalk-valued sections. -/
def zeroSheaf (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    TopologicalSheaf G X (ModuleCat.{u} R) :=
  ⟨zeroPresheaf F, zero_isSheaf F⟩

/-- A morphism of transport presheaves acts on every stalk in a family. -/
def zeroMap {F F' : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R}
    (f : F ⟶ F') : zeroSheaf F ⟶ zeroSheaf F' :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun s x := (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x.1).map
            ((underlyingPresheaf G X (ModuleCat.{u} R)).map f) (s x)
          map_add' s t := by ext x; exact map_add _ _ _
          map_smul' r s := by ext x; exact map_smul _ _ _ }
      naturality U V k := by
        ext s
        funext x
        exact congrArg (fun a => a (s ⟨_, k.unop.mapsTo x.1 x.2⟩))
          (stalkPull_naturality f k.unop.label x.1 (k.unop.label • x.1) rfl) }

variable (R G X)

/-- The degree-zero equivariant Godement functor. -/
def zeroFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤
      TopologicalSheaf G X (ModuleCat.{u} R) where
  obj F := zeroSheaf F.obj
  map f := zeroMap f.hom
  map_id F := by
    apply ObjectProperty.hom_ext
    ext U s
    funext x
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x.1).map
      ((underlyingPresheaf G X (ModuleCat.{u} R)).map (𝟙 F.obj)) (s x) = s x
    simp
  map_comp f k := by
    apply ObjectProperty.hom_ext
    ext U s
    funext x
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x.1).map
      ((underlyingPresheaf G X (ModuleCat.{u} R)).map (f.hom ≫ k.hom)) (s x) = _
    simp only [Functor.map_comp]
    rfl

variable {R G X}

/-- Send a section to its family of germs, respecting every transport arrow. -/
def germFamily (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    F ⟶ zeroPresheaf F where
  app U := ModuleCat.ofHom
    { toFun s x := ((underlyingPresheaf G X (ModuleCat.{u} R)).obj F).germ U.unop.openSet x.1 x.2 s
      map_add' s t := by ext x; exact map_add _ _ _
      map_smul' r s := by ext x; exact map_smul _ _ _ }
  naturality U V f := by
    ext s
    funext x
    exact (congrArg (fun a => a s)
      (germ_stalkPull_arrow F f.unop x.1 (f.unop.label • x.1) rfl x.2)).symm

variable (R G X)

/-- The natural coaugmentation is constructed from ordinary germ maps. -/
def coaugmentation :
    𝟭 (TopologicalSheaf G X (ModuleCat.{u} R)) ⟶ zeroFunctor R G X where
  app F := ObjectProperty.homMk (germFamily F.obj)
  naturality F F' f := by
    apply ObjectProperty.hom_ext
    ext U s
    funext x
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply
      U.unop.openSet x.1 x.2
      ((underlyingPresheaf G X (ModuleCat.{u} R)).map f.hom) s).symm

variable {R G X}

/-- A section of a sheaf is determined by its constructed family of germs. -/
theorem germFamily_injective (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G X) : Function.Injective ((germFamily F.obj).app (op U)) := by
  intro s t h
  apply TopCat.Presheaf.section_ext ((toSheaf G X (ModuleCat.{u} R)).obj F)
  intro x hx
  exact congrFun h ⟨x, hx⟩

/-- The constructed equivariant Godement coaugmentation is a monomorphism. -/
instance mono_coaugmentation (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    Mono ((coaugmentation R G X).app F) where
  right_cancellation {E} f k h := by
    apply ObjectProperty.hom_ext
    ext U s
    apply germFamily_injective F U.unop
    exact congrArg (fun a => a.hom.app U s) h

end Langlands.Sheaf.Equivariant.Godement
