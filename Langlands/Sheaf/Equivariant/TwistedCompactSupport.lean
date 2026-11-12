import Langlands.Sheaf.Equivariant.TwistedOver
import Langlands.Sheaf.Equivariant.LocalActionCohomology
import Langlands.Sheaf.PointSupport
import Langlands.Representation.Category.SmoothPartAdjunction
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Equivariant compactly supported sections on a twisted site

Let `G` act on `X` and let `Φ` be a family of points of a site over `X`, indexed
by a topological space `I` with an action of `G`, such that the fiber of a
translate `gU` at `g • i` is identified with the fiber of `U` at `i`. Then for a
presheaf on the twisted category, the support of the translate `g · s` of a
global section `s` is `g • support s`. So compactly supported global sections
form a subrepresentation of the global sections. Its smooth part is Berkovich's
`Γ_{c,X{G}}`; on discrete sheaves, its right derived functors are the
compactly supported cohomology as smooth representations.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.PointSupport
open scoped Pointwise

universe w v u uG uI

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable {J : GrothendieckTopology (P.Over ⊤ X)}
variable {I : Type uI} [MulAction G I]

variable (ρ) in
/-- Compatibility of a family of points with the translations: the fiber functor
of `Φ (g • i)` precomposed with translation by `g` is identified with the fiber
functor of `Φ i`. For points over geometric points `x̄ᵢ` of `X`, the points of
`gU` over `g x̄ᵢ` are the points of `U` over `x̄ᵢ`. -/
structure PointEquivariance (Φ : I → J.Point.{w}) where
  /-- The identification of fibers. -/
  fiberIso : ∀ (g : G) (i : I), translate P ρ g ⋙ (Φ (g • i)).fiber ≅ (Φ i).fiber

variable {Φ : I → J.Point.{w}}

section Germs

omit [P.RespectsIso] in
theorem eq_comp_rho_inv_of_comp_rho_eq {A : C} {a b : A ⟶ X} (g : G)
    (h : a ≫ (ρ g).hom = b) : a = b ≫ (ρ g⁻¹).hom := by
  rw [← h, Category.assoc, rho_hom_inv_hom, Category.comp_id]

omit [P.RespectsIso] in
theorem comp_rho_inv_comp_rho {A : C} (a : A ⟶ X) (g : G) :
    (a ≫ (ρ g⁻¹).hom) ≫ (ρ g).hom = a := by
  rw [Category.assoc, rho_inv_hom_hom, Category.comp_id]

/-- The translate of `V` by `g⁻¹`, translated back by `g`, is `V`. -/
def translateInvIso (g : G) (V : P.Over ⊤ X) :
    (translate P ρ g).obj ((translate P ρ g⁻¹).obj V) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans
      (comp_rho_inv_comp_rho (TwistedOver.hom ((ι P ρ).obj V)) g).symm)

/-- A morphism `V ⟶ gU` over `X` comes from a morphism `g⁻¹V ⟶ U`. -/
def untranslate (g : G) {U V : P.Over ⊤ X} (f : V ⟶ (translate P ρ g).obj U) :
    (translate P ρ g⁻¹).obj V ⟶ U :=
  MorphismProperty.Over.homMk f.left
    (eq_comp_rho_inv_of_comp_rho_eq (a := f.left ≫ TwistedOver.hom ((ι P ρ).obj U))
      (b := TwistedOver.hom ((ι P ρ).obj V)) g
      ((Category.assoc _ _ _).trans (MorphismProperty.Over.w f)))

theorem translate_map_untranslate (g : G) {U V : P.Over ⊤ X}
    (f : V ⟶ (translate P ρ g).obj U) :
    (translate P ρ g).map (untranslate g f) = (translateInvIso g V).hom ≫ f :=
  MorphismProperty.Over.Hom.ext (Category.id_comp _).symm

/-- Relabelling, as a natural transformation from the translated restriction of a
presheaf on the twisted category to its restriction. Its components are
invertible. -/
def relabelNatTrans {A : Type*} [Category A] (F : (TwistedOver P ρ)ᵒᵖ ⥤ A) (g : G) :
    (translate P ρ g).op ⋙ (ι P ρ).op ⋙ F ⟶ (ι P ρ).op ⋙ F where
  app U := F.map (relabel ρ g U.unop).op
  naturality U V f := by
    change F.map ((ι P ρ).map ((translate P ρ g).map f.unop)).op ≫
        F.map (relabel ρ g V.unop).op =
      F.map (relabel ρ g U.unop).op ≫ F.map ((ι P ρ).map f.unop).op
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ι_map_comp_relabel]

instance twistedCompactSupportInstance1 {A : Type*} [Category A] (F : (TwistedOver P ρ)ᵒᵖ ⥤ A) (g : G) :
    IsIso (relabelNatTrans F g) := by
  have : ∀ U, IsIso ((relabelNatTrans F g).app U) := fun U => by
    change IsIso (F.map (relabel ρ g U.unop).op)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

variable {R : Type w} [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- Germ transport: the germ of `t` over `gU` at `Φ (g • i)` vanishes exactly when
the germ of `t`, as a section of the translated presheaf over `U`, vanishes at
`Φ i`. -/
theorem toPresheafFiber_eq_zero_iff (E : PointEquivariance ρ Φ)
    (Q : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) (g : G) (i : I) {U : P.Over ⊤ X}
    (x : (Φ i).fiber.obj U) (t : Q.obj (op ((translate P ρ g).obj U))) :
    (Φ (g • i)).toPresheafFiber ((translate P ρ g).obj U) ((E.fiberIso g i).inv.app U x) Q t = 0 ↔
      (Φ i).toPresheafFiber U x ((translate P ρ g).op ⋙ Q) t = 0 := by
  have e₁ := (Φ (g • i)).toPresheafFiber_eq_iff' ((translate P ρ g).obj U)
    ((E.fiberIso g i).inv.app U x) t 0
  have e₂ := (Φ i).toPresheafFiber_eq_iff' U x (P := (translate P ρ g).op ⋙ Q) t 0
  rw [map_zero] at e₁ e₂
  rw [e₁, e₂]
  constructor
  · rintro ⟨V, f, y, hy, hf⟩
    refine ⟨(translate P ρ g⁻¹).obj V, untranslate g f,
      (E.fiberIso g i).hom.app _ ((Φ (g • i)).fiber.map (translateInvIso g V).inv y), ?_, ?_⟩
    · rw [← NatTrans.naturality_apply (E.fiberIso g i).hom (untranslate g f)]
      change (E.fiberIso g i).hom.app U ((Φ (g • i)).fiber.map
        ((translate P ρ g).map (untranslate g f))
          ((Φ (g • i)).fiber.map (translateInvIso g V).inv y)) = x
      rw [translate_map_untranslate, ← Functor.map_comp_apply, Iso.inv_hom_id_assoc, hy]
      exact Iso.inv_hom_id_app_apply (E.fiberIso g i) U x
    · change Q.map ((translate P ρ g).map (untranslate g f)).op t =
        Q.map ((translate P ρ g).map (untranslate g f)).op 0
      rw [translate_map_untranslate, op_comp, Q.map_comp, ModuleCat.comp_apply,
        ModuleCat.comp_apply, hf]
  · rintro ⟨W, k, z, hz, hk⟩
    refine ⟨(translate P ρ g).obj W, (translate P ρ g).map k,
      (E.fiberIso g i).inv.app W z, ?_, hk⟩
    exact (NatTrans.naturality_apply (E.fiberIso g i).inv k z).symm.trans (by rw [hz])

omit [MulAction G I] in
/-- Relabelling does not change whether a germ vanishes. -/
theorem toPresheafFiber_relabel_eq_zero_iff (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R)
    (g : G) (i : I) {U : P.Over ⊤ X} (x : (Φ i).fiber.obj U)
    (t : ((translate P ρ g).op ⋙ (ι P ρ).op ⋙ F).obj (op U)) :
    (Φ i).toPresheafFiber U x ((ι P ρ).op ⋙ F) ((relabelNatTrans F g).app (op U) t) = 0 ↔
      (Φ i).toPresheafFiber U x ((translate P ρ g).op ⋙ (ι P ρ).op ⋙ F) t = 0 := by
  rw [← GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  have : Mono ((Φ i).presheafFiber.map (relabelNatTrans F g)) := inferInstance
  have hinj := (ModuleCat.mono_iff_injective _).1 this
  constructor
  · intro h
    exact hinj (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

end Germs

section Support

variable [P.ContainsIdentities]
variable {R : Type w} [CommRing R]

variable (P ρ) in
/-- The base object is terminal among objects over `X`. -/
def isTerminalBaseObj : IsTerminal (base P ρ).obj :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f => MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))

/-- The action of `g` on global sections: restriction along the relabelling by
`g⁻¹` after restriction along a morphism over `X`. -/
theorem actionRepresentation_baseAction_eq (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R)
    (g : G) (s : F.obj (op (base P ρ))) :
    actionRepresentation F (baseAction P ρ) g s =
      (relabelNatTrans F g⁻¹).app (op (base P ρ).obj)
        (((ι P ρ).op ⋙ F).map (untwist g⁻¹ (U := (base P ρ).obj) (V := (base P ρ).obj)
          (baseEndo g⁻¹) rfl).op s) := by
  rw [actionRepresentation_apply, baseAction_apply]
  conv_lhs => rw [← relabel_comp_ι_map_untwist g⁻¹ (U := (base P ρ).obj) (V := (base P ρ).obj)
    (baseEndo g⁻¹) rfl]
  rw [op_comp, F.map_comp, ModuleCat.comp_apply]
  rfl

variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- The support of the translate `g · s` of a global section is `g • support s`. -/
theorem support_actionRepresentation (E : PointEquivariance ρ Φ)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) (g : G) (s : F.obj (op (base P ρ))) :
    support Φ ((ι P ρ).op ⋙ F) (actionRepresentation F (baseAction P ρ) g s) =
      g • support Φ ((ι P ρ).op ⋙ F) (X := (base P ρ).obj) s := by
  ext i
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show (∃ x : (Φ i).fiber.obj (base P ρ).obj, (Φ i).toPresheafFiber _ x ((ι P ρ).op ⋙ F)
      (actionRepresentation F (baseAction P ρ) g s) ≠ 0) ↔
    ∃ y : (Φ (g⁻¹ • i)).fiber.obj (base P ρ).obj,
      (Φ (g⁻¹ • i)).toPresheafFiber _ y ((ι P ρ).op ⋙ F) s ≠ 0
  let m := untwist (ρ := ρ) g⁻¹ (U := (base P ρ).obj) (V := (base P ρ).obj)
    (baseEndo (P := P) (ρ := ρ) g⁻¹) rfl
  have key : ∀ x : (Φ i).fiber.obj (base P ρ).obj,
      (Φ i).toPresheafFiber _ x ((ι P ρ).op ⋙ F)
          (actionRepresentation F (baseAction P ρ) g s) = 0 ↔
        (Φ (g⁻¹ • i)).toPresheafFiber _
          ((Φ (g⁻¹ • i)).fiber.map m ((E.fiberIso g⁻¹ i).inv.app _ x)) ((ι P ρ).op ⋙ F) s = 0 := by
    intro x
    have h₀ := congrArg (ConcreteCategory.hom ((Φ i).toPresheafFiber _ x ((ι P ρ).op ⋙ F)))
      (actionRepresentation_baseAction_eq F g s)
    rw [h₀, toPresheafFiber_relabel_eq_zero_iff, ← toPresheafFiber_eq_zero_iff E,
      GrothendieckTopology.Point.toPresheafFiber_w_apply]
  let := (Φ i).uniqueFiberObj _ (isTerminalBaseObj P ρ)
  let := (Φ (g⁻¹ • i)).uniqueFiberObj _ (isTerminalBaseObj P ρ)
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, fun h => hx ((key x).2 h)⟩
  · rintro ⟨y, hy⟩
    refine ⟨default, fun h => hy ?_⟩
    rw [Subsingleton.elim y ((Φ (g⁻¹ • i)).fiber.map m ((E.fiberIso g⁻¹ i).inv.app _ default))]
    exact (key default).1 h

end Support

section Compact

variable [P.ContainsIdentities]
variable {R : Type w} [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace I] [ContinuousConstSMul G I]

/-- The translate of a compactly supported global section is compactly
supported. -/
theorem isCompactlySupported_actionRepresentation (E : PointEquivariance ρ Φ)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) (g : G) {s : F.obj (op (base P ρ))}
    (hs : IsCompactlySupported Φ ((ι P ρ).op ⋙ F) (X := (base P ρ).obj) s) :
    IsCompactlySupported Φ ((ι P ρ).op ⋙ F) (X := (base P ρ).obj)
      (actionRepresentation F (baseAction P ρ) g s) := by
  obtain ⟨K, hK, hsK⟩ := hs
  exact ⟨g • K, hK.smul g,
    (support_actionRepresentation E F g s).trans_subset (Set.smul_set_mono hsK)⟩

variable (R) in
/-- The compactly supported global sections, as a subrepresentation of the global
sections. -/
def compactRepresentation (E : PointEquivariance ρ Φ)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) :
    Representation R G (compactSubmodule Φ R ((ι P ρ).op ⋙ F) (base P ρ).obj) where
  toFun g := (actionRepresentation F (baseAction P ρ) g).restrict
    fun _ hs => isCompactlySupported_actionRepresentation E F g hs
  map_one' := by
    ext s
    exact congrArg (fun φ : Module.End R _ => φ s.1) (map_one (actionRepresentation F _))
  map_mul' g h := by
    ext s
    exact congrArg (fun φ : Module.End R _ => φ s.1) (map_mul (actionRepresentation F _) g h)

theorem compactRepresentation_apply (E : PointEquivariance ρ Φ)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) (g : G)
    (s : compactSubmodule Φ R ((ι P ρ).op ⋙ F) (base P ρ).obj) :
    (compactRepresentation R E F g s).1 = actionRepresentation F (baseAction P ρ) g s.1 :=
  rfl

/-- A morphism of presheaves restricts to an intertwiner of compactly supported
global sections. -/
def compactIntertwiningMap (E : PointEquivariance ρ Φ)
    {F F' : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F') :
    (compactRepresentation R E F).IntertwiningMap (compactRepresentation R E F') :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((compactSections Φ R (base P ρ).obj).map (Functor.whiskerLeft (ι P ρ).op φ)).hom
    fun g s => Subtype.ext (NatTrans.naturality_apply φ (baseAction P ρ g).unop.op s.1)

variable (R) in
/-- Compactly supported global sections of presheaves on the twisted category, as
representations of `G`. -/
def compactSectionsRep (E : PointEquivariance ρ Φ) :
    ((TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R G where
  obj F := Rep.of (compactRepresentation R E F)
  map φ := Rep.ofHom (compactIntertwiningMap E φ)
  map_id _ := rfl
  map_comp _ _ := rfl

instance compactSectionsRep_additive (E : PointEquivariance ρ Φ) :
    (compactSectionsRep R E).Additive where
  map_add := rfl

end Compact

section Sheaves

variable [P.ContainsIdentities]
variable {R : Type w} [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace I] [ContinuousConstSMul G I]
variable (J) [IsTranslationInvariant (ρ := ρ) J]

variable (R) in
/-- Compactly supported global sections of module sheaves on the twisted site, as
representations of `G`. -/
def sheafCompactSectionsRep (E : PointEquivariance ρ Φ) :
    Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ Rep.{w} R G :=
  sheafToPresheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⋙ compactSectionsRep R E

instance sheafCompactSectionsRep_additive (E : PointEquivariance ρ Φ) :
    (sheafCompactSectionsRep J R E).Additive :=
  inferInstanceAs (sheafToPresheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⋙
    compactSectionsRep R E).Additive

/-- The module underlying the compactly supported global sections of a sheaf on
the twisted site is the module of compactly supported sections of its restriction
to the site over `X`. -/
def sheafCompactSectionsRepForgetIso (E : PointEquivariance ρ Φ) :
    sheafCompactSectionsRep J R E ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ≅
      restriction ρ J (ModuleCat.{w} R) ⋙ sheafCompactSections J Φ R (base P ρ).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

omit [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)] [TopologicalSpace I]
  [ContinuousConstSMul G I] in
/-- Restriction of module sheaves from the twisted site preserves finite limits. -/
instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction ρ J (ModuleCat.{w} R)) := by
  have : PreservesFiniteLimits (restriction ρ J (ModuleCat.{w} R) ⋙
      sheafToPresheaf J (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso ((ι P ρ).sheafPushforwardContinuousCompSheafToPresheafIso
      (ModuleCat.{w} R) J (twistedTopology ρ J)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (ModuleCat.{w} R))

/-- Compactly supported global sections are left exact. -/
instance sheafCompactSectionsRep_preservesFiniteLimits [HasSheafify J (ModuleCat.{w} R)]
    (E : PointEquivariance ρ Φ) : PreservesFiniteLimits (sheafCompactSectionsRep J R E) := by
  have : PreservesFiniteLimits
      (sheafCompactSectionsRep J R E ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso (sheafCompactSectionsRepForgetIso J E).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R G) (ModuleCat.{w} R))

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The smooth-part functor is a right adjoint, hence left exact. -/
instance smoothPartFunctor_isRightAdjoint :
    (SmoothRep.smoothPartFunctor.{w, uG, w} R G).IsRightAdjoint :=
  (SmoothRep.toRepSmoothPartAdjunction R G).isRightAdjoint

variable (R) in
/-- Smooth compactly supported global sections: the smooth part of the
compactly supported global sections, Berkovich's `Γ_{c,X{G}}`. -/
def sheafCompactSectionsSmooth (E : PointEquivariance ρ Φ) :
    Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ SmoothRep.{w, uG, w} R G :=
  sheafCompactSectionsRep J R E ⋙ SmoothRep.smoothPartFunctor R G

instance sheafCompactSectionsSmooth_additive (E : PointEquivariance ρ Φ) :
    (sheafCompactSectionsSmooth J R E).Additive where
  map_add := rfl

instance sheafCompactSectionsSmooth_preservesFiniteLimits [HasSheafify J (ModuleCat.{w} R)]
    (E : PointEquivariance ρ Φ) : PreservesFiniteLimits (sheafCompactSectionsSmooth J R E) :=
  comp_preservesFiniteLimits _ _

section Discrete

variable (L : LocalActionSystem (TwistedOver P ρ) G)

variable (R) in
/-- Smooth compactly supported global sections of discrete module sheaves on the
twisted site. -/
def discreteCompactSections (E : PointEquivariance ρ Φ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ SmoothRep.{w, uG, w} R G :=
  L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    sheafCompactSectionsSmooth J R E

instance discreteCompactSections_additive (E : PointEquivariance ρ Φ) :
    (discreteCompactSections J R L E).Additive :=
  inferInstanceAs (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    sheafCompactSectionsSmooth J R E).Additive

variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]

/-- Smooth compactly supported global sections of discrete sheaves are left
exact. -/
instance discreteCompactSections_preservesFiniteLimits (E : PointEquivariance ρ Φ) :
    PreservesFiniteLimits (discreteCompactSections J R L E) :=
  comp_preservesFiniteLimits _ _

variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

variable (R) in
/-- Degree `q` compactly supported cohomology of discrete module sheaves on the
twisted site, as smooth representations of `G`: the right derived functors of
the smooth compactly supported global sections, computed with injective
resolutions among discrete sheaves. This is the shape of Berkovich's
`H^q_c(X{G}, F)`. -/
def discreteCompactDerived (E : PointEquivariance ρ Φ) (q : ℕ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ SmoothRep.{w, uG, w} R G :=
  (discreteCompactSections J R L E).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def discreteCompactDerivedZeroIso (E : PointEquivariance ρ Φ) :
    discreteCompactDerived J R L E 0 ≅ discreteCompactSections J R L E :=
  (discreteCompactSections J R L E).rightDerivedZeroIsoSelf

/-- The derived functors are computed by any injective resolution among discrete
sheaves. -/
def discreteCompactDerivedIso (E : PointEquivariance ρ Φ)
    {F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)} (I : InjectiveResolution F)
    (q : ℕ) :
    (discreteCompactDerived J R L E q).obj F ≅
      (HomologicalComplex.homologyFunctor (SmoothRep.{w, uG, w} R G) (ComplexShape.up ℕ) q).obj
        (((discreteCompactSections J R L E).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (discreteCompactSections J R L E) q

omit [HasSheafify J (ModuleCat.{w} R)] in
/-- The derived functors vanish in positive degrees on injective discrete
sheaves. -/
theorem isZero_discreteCompactDerived_succ_of_injective (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) [Injective F] (q : ℕ) :
    IsZero ((discreteCompactDerived J R L E (q + 1)).obj F) :=
  (discreteCompactSections J R L E).isZero_rightDerived_obj_injective_succ q F

end Discrete

end Sheaves

end Langlands.Sheaf.Equivariant.TwistedOver
