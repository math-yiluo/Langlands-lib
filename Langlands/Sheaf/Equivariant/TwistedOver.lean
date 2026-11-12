import Langlands.Sheaf.Equivariant.LocalAction
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Endomorphism

/-!
# The twisted category over an object with a group action

Let `G` act on an object `X` of a category `C` through `ρ : G →* Aut X`, and let
`P` be a morphism property. The twisted category has the objects of
`P.Over ⊤ X`; a morphism `U ⟶ V` is a group element `g` with an arrow
`f : U.left ⟶ V.left` covering `ρ g`, i.e. `f ≫ V.hom = U.hom ≫ (ρ g).hom`.
Presheaves on it are presheaves on `P.Over ⊤ X` with the compatible isomorphisms
`F(U) ≅ F(gU)` of an equivariant sheaf, where `gU` has structure map
`U.hom ≫ (ρ g).hom`. A topology on `P.Over ⊤ X` invariant under these
translations induces a topology on the twisted category, for which the inclusion
of `P.Over ⊤ X` is continuous and cocontinuous.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory Opposite

universe w v u uG

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C) {X : C}
variable {G : Type uG} [Group G]

/-- The objects of the twisted category: objects of `P.Over ⊤ X`. -/
@[ext]
structure TwistedOver (ρ : G →* Aut X) where
  /-- The underlying object over `X`. -/
  obj : P.Over ⊤ X

variable (ρ : G →* Aut X)

namespace TwistedOver

variable {P ρ}

/-- The structure map to `X`. -/
abbrev hom (U : TwistedOver P ρ) : U.obj.left ⟶ X := U.obj.hom

/-- A twisted morphism `U ⟶ V`: a group element `twist` and an arrow of
underlying objects covering the action of `twist` on `X`. -/
@[ext]
structure Hom (U V : TwistedOver P ρ) where
  /-- The group element covered by the morphism. -/
  twist : G
  /-- The underlying arrow. -/
  left : U.obj.left ⟶ V.obj.left
  w : left ≫ V.hom = U.hom ≫ (ρ twist).hom

attribute [reassoc] Hom.w

theorem rho_mul_hom (g g' : G) : (ρ (g * g')).hom = (ρ g').hom ≫ (ρ g).hom := by
  rw [map_mul]
  rfl

theorem rho_one_hom : (ρ 1).hom = 𝟙 X := by
  rw [map_one]
  rfl

@[simp]
theorem rho_inv_hom_hom (g : G) : (ρ g⁻¹).hom ≫ (ρ g).hom = 𝟙 X := by
  rw [← rho_mul_hom, mul_inv_cancel, rho_one_hom]

@[simp]
theorem rho_hom_inv_hom (g : G) : (ρ g).hom ≫ (ρ g⁻¹).hom = 𝟙 X := by
  rw [← rho_mul_hom, inv_mul_cancel, rho_one_hom]

theorem hom_comp_rho_hom_inv (U : TwistedOver P ρ) (g : G) :
    (U.hom ≫ (ρ g).hom) ≫ (ρ g⁻¹).hom = U.hom := by
  rw [Category.assoc, rho_hom_inv_hom, Category.comp_id]

/-- The identity: trivial twist and identity arrow. -/
def Hom.id (U : TwistedOver P ρ) : Hom U U where
  twist := 1
  left := 𝟙 _
  w := by rw [rho_one_hom, Category.id_comp, Category.comp_id]

/-- Composition multiplies twists, the later twist on the left. -/
def Hom.comp {U V W : TwistedOver P ρ} (f : Hom U V) (g : Hom V W) : Hom U W where
  twist := g.twist * f.twist
  left := f.left ≫ g.left
  w := by rw [Category.assoc, g.w, f.w_assoc, rho_mul_hom]

instance category : Category.{max v uG} (TwistedOver P ρ) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (mul_one _) (Category.id_comp _)
  comp_id _ := Hom.ext (one_mul _) (Category.comp_id _)
  assoc _ _ _ := Hom.ext (mul_assoc _ _ _).symm (Category.assoc _ _ _)

@[ext]
theorem hom_ext {U V : TwistedOver P ρ} {f f' : U ⟶ V} (h₁ : Hom.twist f = Hom.twist f')
    (h₂ : Hom.left f = Hom.left f') : f = f' :=
  Hom.ext h₁ h₂

@[simp]
theorem id_twist (U : TwistedOver P ρ) : Hom.twist (𝟙 U) = 1 := rfl

@[simp]
theorem id_left (U : TwistedOver P ρ) : Hom.left (𝟙 U) = 𝟙 U.obj.left := rfl

@[simp]
theorem comp_twist {U V W : TwistedOver P ρ} (f : U ⟶ V) (g : V ⟶ W) :
    Hom.twist (f ≫ g) = Hom.twist g * Hom.twist f := rfl

@[simp]
theorem comp_left {U V W : TwistedOver P ρ} (f : U ⟶ V) (g : V ⟶ W) :
    Hom.left (f ≫ g) = Hom.left f ≫ Hom.left g := rfl

/-- Build a twisted morphism from a group element and a covering arrow. -/
def homMk {U V : TwistedOver P ρ} (g : G) (f : U.obj.left ⟶ V.obj.left)
    (w : f ≫ V.hom = U.hom ≫ (ρ g).hom) : U ⟶ V :=
  ⟨g, f, w⟩

@[simp]
theorem homMk_twist {U V : TwistedOver P ρ} (g : G) (f : U.obj.left ⟶ V.obj.left)
    (w : f ≫ V.hom = U.hom ≫ (ρ g).hom) : Hom.twist (homMk g f w) = g := rfl

@[simp]
theorem homMk_left {U V : TwistedOver P ρ} (g : G) (f : U.obj.left ⟶ V.obj.left)
    (w : f ≫ V.hom = U.hom ≫ (ρ g).hom) : Hom.left (homMk g f w) = f := rfl

variable (P ρ)

/-- The inclusion of `P.Over ⊤ X`: morphisms over `X` are the morphisms with
trivial twist. -/
@[reducible, simps obj]
def ι : P.Over ⊤ X ⥤ TwistedOver P ρ where
  obj U := ⟨U⟩
  map {U V} f := homMk 1 f.left (by
    rw [rho_one_hom, Category.comp_id]
    exact MorphismProperty.Over.w f)
  map_id _ := hom_ext rfl rfl
  map_comp _ _ := hom_ext (mul_one 1).symm rfl

variable {P ρ}

@[simp]
theorem ι_map_twist {U V : P.Over ⊤ X} (f : U ⟶ V) : Hom.twist ((ι P ρ).map f) = 1 := rfl

@[simp]
theorem ι_map_left {U V : P.Over ⊤ X} (f : U ⟶ V) : Hom.left ((ι P ρ).map f) = f.left := rfl

instance : (ι P ρ).Faithful where
  map_injective {_ _} _ _ h := MorphismProperty.Over.Hom.ext (congrArg Hom.left h)

/-- A twisted morphism with trivial twist comes from a morphism over `X`. -/
theorem exists_ι_map_of_twist_eq_one {U V : P.Over ⊤ X} (f : (ι P ρ).obj U ⟶ (ι P ρ).obj V)
    (hf : Hom.twist f = 1) : ∃ f' : U ⟶ V, (ι P ρ).map f' = f :=
  ⟨MorphismProperty.Over.homMk (Hom.left f) (by
    have := Hom.w f
    rw [hf, rho_one_hom, Category.comp_id] at this
    exact this),
    hom_ext hf.symm rfl⟩

section Translation

variable [P.RespectsIso]
variable (P ρ)

/-- Translation by `g`: `U ↦ gU`, with structure map `U.hom ≫ (ρ g).hom` and the
same underlying arrows. For a space with a left action this is isomorphic over
`X` to `U ×_{X, g⁻¹} X`. -/
def translate (g : G) : P.Over ⊤ X ⥤ P.Over ⊤ X :=
  (MorphismProperty.Comma.mapRightIso (𝟭 C) (Discrete.natIso fun _ => (ρ g : X ≅ X)) :
    P.Over ⊤ X ≌ P.Over ⊤ X).functor

variable {P ρ}

@[simp]
theorem translate_obj_left (g : G) (U : P.Over ⊤ X) : ((translate P ρ g).obj U).left = U.left :=
  rfl

@[simp]
theorem translate_obj_hom (g : G) (U : P.Over ⊤ X) :
    ((translate P ρ g).obj U).hom = U.hom ≫ (ρ g).hom :=
  rfl

@[simp]
theorem translate_map_left (g : G) {U V : P.Over ⊤ X} (f : U ⟶ V) :
    ((translate P ρ g).map f).left = f.left :=
  rfl

theorem hom_translate (g : G) (U : P.Over ⊤ X) :
    TwistedOver.hom ((ι P ρ).obj ((translate P ρ g).obj U)) =
      TwistedOver.hom ((ι P ρ).obj U) ≫ (ρ g).hom :=
  rfl

variable (ρ) in
/-- The relabelling isomorphism `U ⟶ gU` with twist `g` and identity arrow. -/
def relabel (g : G) (U : P.Over ⊤ X) : (ι P ρ).obj U ⟶ (ι P ρ).obj ((translate P ρ g).obj U) :=
  homMk g (𝟙 U.left) (Category.id_comp _)

@[simp]
theorem relabel_twist (g : G) (U : P.Over ⊤ X) : Hom.twist (relabel ρ g U) = g := rfl

@[simp]
theorem relabel_left (g : G) (U : P.Over ⊤ X) : Hom.left (relabel ρ g U) = 𝟙 U.left := rfl

variable (ρ) in
/-- The inverse of the relabelling isomorphism. -/
def relabelInv (g : G) (U : P.Over ⊤ X) :
    (ι P ρ).obj ((translate P ρ g).obj U) ⟶ (ι P ρ).obj U :=
  homMk g⁻¹ (𝟙 U.left)
    ((Category.id_comp _).trans (hom_comp_rho_hom_inv ((ι P ρ).obj U) g).symm)

instance (g : G) (U : P.Over ⊤ X) : IsIso (relabel ρ g U) :=
  ⟨relabelInv ρ g U, hom_ext (inv_mul_cancel g) (Category.id_comp _),
    hom_ext (mul_inv_cancel g) (Category.id_comp _)⟩

/-- Relabelling is natural. -/
@[reassoc]
theorem ι_map_comp_relabel (g : G) {U V : P.Over ⊤ X} (f : U ⟶ V) :
    (ι P ρ).map f ≫ relabel ρ g V = relabel ρ g U ≫ (ι P ρ).map ((translate P ρ g).map f) :=
  hom_ext ((mul_one g).trans (one_mul g).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The arrow over `X` underlying a twisted morphism with twist `g`, from the
translate of its source by `g`. -/
def untwist (g : G) {U V : P.Over ⊤ X} (f : (ι P ρ).obj U ⟶ (ι P ρ).obj V)
    (hf : Hom.twist f = g) : (translate P ρ g).obj U ⟶ V :=
  MorphismProperty.Over.homMk (A := (translate P ρ g).obj U) (B := V)
    (Hom.left (U := (ι P ρ).obj U) (V := (ι P ρ).obj V) f) (by
      have := Hom.w f
      rw [hf] at this
      exact this)

@[simp]
theorem untwist_left (g : G) {U V : P.Over ⊤ X} (f : (ι P ρ).obj U ⟶ (ι P ρ).obj V)
    (hf : Hom.twist f = g) : (untwist g f hf).left = Hom.left f :=
  rfl

/-- Every twisted morphism with twist `g` is the relabelling by `g` followed by a
morphism over `X`. -/
theorem relabel_comp_ι_map_untwist (g : G) {U V : P.Over ⊤ X}
    (f : (ι P ρ).obj U ⟶ (ι P ρ).obj V) (hf : Hom.twist f = g) :
    relabel ρ g U ≫ (ι P ρ).map (untwist g f hf) = f :=
  hom_ext ((one_mul g).trans hf.symm) (Category.id_comp _)

end Translation

section Topology

variable [P.RespectsIso]
variable (J : GrothendieckTopology (P.Over ⊤ X))

/-- A topology on `P.Over ⊤ X` is invariant under the group action when every
translation is cocontinuous. -/
class IsTranslationInvariant : Prop where
  isCocontinuous : ∀ g : G, (translate P ρ g).IsCocontinuous J J

variable (ρ) in
/-- The twisted topology: a sieve covers when its arrows over `X` form a
covering sieve. -/
def twistedTopology [IsTranslationInvariant (ρ := ρ) J] :
    GrothendieckTopology (TwistedOver P ρ) where
  sieves U := {S | Sieve.functorPullback (ι P ρ) (X := U.obj) S ∈ J U.obj}
  top_mem' U := by
    change Sieve.functorPullback (ι P ρ) (X := U.obj) ⊤ ∈ J U.obj
    rw [Sieve.functorPullback_top]
    exact J.top_mem _
  pullback_stable' := by
    rintro ⟨U⟩ ⟨V⟩ S f hS
    have hS : Sieve.functorPullback (ι P ρ) S ∈ J U := hS
    change Sieve.functorPullback (ι P ρ) (S.pullback f) ∈ J V
    have := (IsTranslationInvariant.isCocontinuous (ρ := ρ) (J := J) (Hom.twist f)).cover_lift
      (J.pullback_stable (untwist _ f rfl) hS)
    refine J.superset_covering ?_ this
    intro W k hk
    change S.arrows ((ι P ρ).map ((translate P ρ (Hom.twist f)).map k ≫ untwist _ f rfl)) at hk
    change S.arrows ((ι P ρ).map k ≫ f)
    have := S.downward_closed hk (relabel ρ (Hom.twist f) W)
    rwa [Functor.map_comp, ← ι_map_comp_relabel_assoc, relabel_comp_ι_map_untwist] at this
  transitive' := by
    rintro ⟨U⟩ S hS R hR
    change Sieve.functorPullback (ι P ρ) R ∈ J U
    refine J.transitive hS _ fun W f hf => ?_
    rw [← Sieve.functorPullback_pullback]
    exact hR hf

variable [IsTranslationInvariant (ρ := ρ) J]

theorem mem_twistedTopology_iff {U : P.Over ⊤ X} (S : Sieve ((ι P ρ).obj U)) :
    S ∈ twistedTopology ρ J ((ι P ρ).obj U) ↔ Sieve.functorPullback (ι P ρ) S ∈ J U :=
  Iff.rfl

/-- The inclusion of `P.Over ⊤ X` is cocontinuous: this is the definition of the
twisted topology. -/
instance : (ι P ρ).IsCocontinuous J (twistedTopology ρ J) where
  cover_lift hS := hS

/-- The inclusion of `P.Over ⊤ X` preserves covering sieves. -/
theorem ι_coverPreserving : CoverPreserving J (twistedTopology ρ J) (ι P ρ) where
  cover_preserve {U} S hS := by
    rw [mem_twistedTopology_iff]
    exact J.superset_covering (Sieve.le_functorPushforward_pullback _ S) hS

/-- The inclusion of `P.Over ⊤ X` is compatible-preserving. Two twisted
morphisms whose composites with arrows over `X` agree have the same twist;
they are one relabelling followed by arrows over `X` which agree after
composition. -/
theorem ι_compatiblePreserving (K : GrothendieckTopology (TwistedOver P ρ)) :
    CompatiblePreserving.{w} K (ι P ρ) := by
  constructor
  intro F Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ he
  obtain ⟨W⟩ := W
  have ht : Hom.twist f₂ = Hom.twist f₁ := by
    simpa using (congrArg Hom.twist he).symm
  rw [← relabel_comp_ι_map_untwist (U := W) (Hom.twist f₁) f₁ rfl,
    ← relabel_comp_ι_map_untwist (U := W) (Hom.twist f₁) f₂ ht]
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg (F.obj.map (relabel ρ (Hom.twist f₁) W).op)
    (hx (untwist _ f₁ rfl) (untwist _ f₂ ht) hg₁ hg₂
      (MorphismProperty.Over.Hom.ext (congrArg Hom.left he)))

/-- The inclusion of `P.Over ⊤ X` is continuous: sheaves on the twisted site
restrict to sheaves on `P.Over ⊤ X`. -/
instance : (ι P ρ).IsContinuous J (twistedTopology ρ J) :=
  Functor.isContinuous_of_coverPreserving (ι_compatiblePreserving _) (ι_coverPreserving J)

/-- A presheaf of types on the twisted site is a sheaf when its restriction to
`P.Over ⊤ X` is a sheaf. A compatible family on a covering sieve restricts to a
compatible family on its arrows over `X`; its amalgamation is an amalgamation of
the whole family, because every twisted arrow is a relabelling followed by an
arrow over `X` of the same sieve. -/
theorem isSheaf_of_isSheaf_comp {F : (TwistedOver P ρ)ᵒᵖ ⥤ Type w}
    (hF : Presieve.IsSheaf J ((ι P ρ).op ⋙ F)) :
    Presieve.IsSheaf (twistedTopology ρ J) F := by
  rintro ⟨U⟩ S hS x hx
  have hS' : Sieve.functorPullback (ι P ρ) S ∈ J U := hS
  let y : Presieve.FamilyOfElements ((ι P ρ).op ⋙ F) (Sieve.functorPullback (ι P ρ) S).arrows :=
    fun _ f hf => x ((ι P ρ).map f) hf
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact hx ((ι P ρ).map g₁) ((ι P ρ).map g₂) h₁ h₂
      (by rw [← Functor.map_comp, ← Functor.map_comp, w])
  obtain ⟨t, ht, ht'⟩ := hF _ hS' y hy
  refine ⟨t, ?_, ?_⟩
  · rintro ⟨V⟩ f hf
    have hfac := relabel_comp_ι_map_untwist (Hom.twist f) f rfl
    have hf' : S.arrows ((ι P ρ).map (untwist _ f rfl)) := by
      have := S.downward_closed hf (inv (relabel ρ (Hom.twist f) V))
      rwa [(IsIso.inv_comp_eq _).2 hfac.symm] at this
    have h₁ := ht (untwist _ f rfl) hf'
    have h₂ := Presieve.FamilyOfElements.comp_of_compatible S hx hf' (relabel ρ (Hom.twist f) V)
    calc F.map f.op t
        = F.map (relabel ρ (Hom.twist f) V).op (F.map ((ι P ρ).map (untwist _ f rfl)).op t) := by
          conv_lhs => rw [← hfac]
          rw [op_comp, Functor.map_comp_apply]
      _ = F.map (relabel ρ (Hom.twist f) V).op (x _ hf') := congrArg _ h₁
      _ = x f hf := by
          rw [← h₂]
          congr 1
  · intro t' ht''
    exact ht' t' fun W f hf => ht'' ((ι P ρ).map f) hf

/-- A presheaf on the twisted site is a sheaf exactly when its restriction to
`P.Over ⊤ X` is a sheaf: sheaves on the twisted site are sheaves on
`P.Over ⊤ X` with an equivariant structure. -/
theorem isSheaf_iff_isSheaf_comp {A : Type*} [Category A] (F : (TwistedOver P ρ)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (twistedTopology ρ J) F ↔ Presheaf.IsSheaf J ((ι P ρ).op ⋙ F) := by
  refine ⟨fun hF => (ι P ρ).op_comp_isSheaf J (twistedTopology ρ J) ⟨F, hF⟩, fun hF E => ?_⟩
  exact isSheaf_of_isSheaf_comp J (hF E)

variable (ρ) in
/-- Restriction of sheaves on the twisted site to `P.Over ⊤ X`: forget the
equivariant structure. -/
abbrev restriction (A : Type*) [Category A] :
    Sheaf (twistedTopology ρ J) A ⥤ Sheaf J A :=
  (ι P ρ).sheafPushforwardContinuous A J (twistedTopology ρ J)

end Topology

section Lifts

/-- A homomorphism from a subgroup `H` to the endomorphisms of `U` lifts the
action of `H` on `X` when `h` acts through a twisted endomorphism with twist
`h⁻¹`. Then `h` acts on the sections of a presheaf by restriction along it, a
left action. -/
def IsLift {U : TwistedOver P ρ} {H : Subgroup G} (a : H →* (End U)ᵐᵒᵖ) : Prop :=
  ∀ h : H, Hom.twist (a h).unop = (h : G)⁻¹

variable [TopologicalSpace G]

/-- A local action system on the twisted category consists of lifts when all its
admissible local actions are lifts. -/
def _root_.Langlands.Sheaf.Equivariant.LocalActionSystem.IsLiftSystem
    (L : LocalActionSystem (TwistedOver P ρ) G) : Prop :=
  ∀ (U : TwistedOver P ρ) (H : OpenSubgroup G) (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ),
    L.IsAdmissible U H a → IsLift a

end Lifts

section Base

variable [P.ContainsIdentities]
variable (P ρ)

/-- The base object: `X` with its identity structure map. -/
def base : TwistedOver P ρ :=
  ⟨MorphismProperty.Over.mk ⊤ (𝟙 X) (P.id_mem X)⟩

variable {P ρ}

@[simp]
theorem base_obj_left : (base P ρ).obj.left = X := rfl

theorem hom_base : TwistedOver.hom (base P ρ) = 𝟙 X := rfl

/-- The twisted endomorphism of the base given by the action of `g`. -/
def baseEndo (g : G) : base P ρ ⟶ base P ρ :=
  homMk g (ρ g).hom ((Category.comp_id (ρ g).hom).trans (Category.id_comp (ρ g).hom).symm)

@[simp]
theorem baseEndo_twist (g : G) : Hom.twist (baseEndo (P := P) (ρ := ρ) g) = g := rfl

@[simp]
theorem baseEndo_left (g : G) : Hom.left (baseEndo (P := P) (ρ := ρ) g) = (ρ g).hom := rfl

theorem baseEndo_mul (g g' : G) :
    baseEndo (P := P) (ρ := ρ) (g * g') = baseEndo g' ≫ baseEndo g :=
  hom_ext rfl (rho_mul_hom g g')

theorem baseEndo_one : baseEndo (P := P) (ρ := ρ) 1 = 𝟙 _ :=
  hom_ext rfl rho_one_hom

variable (P ρ)

/-- The action of `G` on the base: `g` acts by the twisted endomorphism given by
`g⁻¹`, so that `g` acts on sections by restriction along it. -/
def baseAction : G →* (End (base P ρ))ᵐᵒᵖ where
  toFun g := MulOpposite.op (baseEndo g⁻¹)
  map_one' := by
    rw [inv_one, baseEndo_one]
    rfl
  map_mul' g g' := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op, MulOpposite.unop_op,
      mul_inv_rev, baseEndo_mul]
    rfl

variable {P ρ}

theorem baseAction_apply (g : G) : (baseAction P ρ g).unop = baseEndo g⁻¹ := rfl

/-- The action of `G` on the base lifts the action on `X`. -/
theorem isLift_baseAction :
    IsLift ((baseAction P ρ).comp (⊤ : Subgroup G).subtype) :=
  fun _ => rfl

end Base

end TwistedOver

end Langlands.Sheaf.Equivariant
