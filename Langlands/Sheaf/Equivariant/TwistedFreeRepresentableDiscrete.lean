import Langlands.Sheaf.Equivariant.TwistedFreeRepresentable
import Langlands.Sheaf.Equivariant.LocalActionFree

/-! # Discrete free representables from eventual equivariance -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

open CategoryTheory Opposite
open Langlands.Cohomology.SiteCech

universe u v z w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type z} [Group G] {ρ : G →* Aut X}
variable (L : GlobalLift (P := P) (ρ := ρ))

theorem action_comp (g h : G) :
    (L.action g).unop ≫ (L.action h).unop = (L.action (g * h)).unop := by
  rw [map_mul]
  rfl

/-- Normalized restriction fixes a map exactly when that map intertwines the
two lifted actions. -/
theorem precomp_eq_iff {V : TwistedOver P ρ} (f : V ⟶ V) (g : G)
    (hf : Hom.twist f = g⁻¹) (k : V.obj ⟶ L.obj) :
    L.precomp f k = k ↔
      f ≫ (ι P ρ).map k = (ι P ρ).map k ≫ (L.action g).unop := by
  constructor
  · intro h
    have h' := congrArg (fun t => (ι P ρ).map t ≫ (L.action g).unop) h
    rw [L.ι_precomp, hf, Category.assoc, Category.assoc, L.action_comp,
      inv_mul_cancel, map_one] at h'
    change f ≫ (ι P ρ).map k ≫ 𝟙 _ =
      (ι P ρ).map k ≫ (L.action g).unop at h'
    simpa only [Category.comp_id] using h'
  · intro h
    apply (ι P ρ).map_injective
    rw [L.ι_precomp, hf, ← Category.assoc, h, Category.assoc, L.action_comp,
      mul_inv_cancel, map_one]
    exact Category.comp_id _

variable [TopologicalSpace G]
variable (S : LocalActionSystem (TwistedOver P ρ) G)

/-- Every ordinary map to the lifted object intertwines each admissible local
action with the global lift after shrinking its acting open subgroup. -/
def EventuallyEquivariant : Prop :=
  ∀ (V : TwistedOver P ρ) (H : OpenSubgroup G)
    (a : (H : Subgroup G) →* (End V)ᵐᵒᵖ), S.IsAdmissible V H a →
    ∀ k : V.obj ⟶ L.obj, ∃ N : OpenSubgroup G, N ≤ H ∧
      ∀ h : (H : Subgroup G), (h : G) ∈ N →
        (a h).unop ≫ (ι P ρ).map k =
          (ι P ρ).map k ≫ (L.action (h : G)).unop

variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- Eventual equivariance makes the lifted ordinary representable discrete. -/
theorem isDiscrete_presheaf (hS : S.IsLiftSystem) (hL : L.EventuallyEquivariant S) :
    S.IsDiscrete L.presheaf := by
  intro V H a ha s
  change Shrink.{w} (V.obj ⟶ L.obj) at s
  obtain ⟨N, hNH, hN⟩ := hL V H a ha ((equivShrink _).symm s)
  refine ⟨N, hNH, fun h hh => ?_⟩
  change equivShrink _ (L.precomp (a h).unop ((equivShrink _).symm s)) = s
  rw [(L.precomp_eq_iff _ (h : G) (hS V H a ha h) _).2 (hN h hh),
    Equiv.apply_symm_apply]

/-- For a system of lifts, eventual equivariance is also necessary for
discreteness of the lifted representable. -/
theorem eventuallyEquivariant_iff (hS : S.IsLiftSystem) :
    L.EventuallyEquivariant S ↔ S.IsDiscrete L.presheaf := by
  refine ⟨L.isDiscrete_presheaf S hS, ?_⟩
  intro hL V H a ha k
  obtain ⟨N, hNH, hN⟩ := hL V H a ha (equivShrink _ k)
  refine ⟨N, hNH, fun h hh => ?_⟩
  apply (L.precomp_eq_iff _ (h : G) (hS V H a ha h) _).1
  have hfix := hN h hh
  change equivShrink _ (L.precomp (a h).unop
    ((equivShrink _).symm (equivShrink _ k))) = equivShrink _ k at hfix
  rw [Equiv.symm_apply_apply] at hfix
  exact (equivShrink _).injective hfix

section Sheaf

variable [P.RespectsIso]
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [S.HasFiniteEquivariantRefinements (twistedTopology ρ J)]

/-- The actual free lifted sheaf is discrete under eventual equivariance and
finite equivariant refinements. -/
theorem isDiscrete_freeSheaf (hS : S.IsLiftSystem) (hL : L.EventuallyEquivariant S) :
    S.IsDiscrete (L.freeSheaf J R).obj :=
  LocalActionSystem.IsDiscrete.freeSheaf R S (twistedTopology ρ J)
    (L.isDiscrete_presheaf S hS hL)

/-- The free lifted sheaf as an object of the category of discrete sheaves. -/
def discreteFreeSheaf (hS : S.IsLiftSystem) (hL : L.EventuallyEquivariant S) :
    S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  ⟨L.freeSheaf J R, L.isDiscrete_freeSheaf S J R hS hL⟩

/-- Fixed sections are represented in the discrete sheaf category itself. -/
def discreteFreeSheafHomEquivFixedSections
    (hS : S.IsLiftSystem) (hL : L.EventuallyEquivariant S)
    (F : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) :
    (L.discreteFreeSheaf S J R hS hL ⟶ F) ≃
      L.FixedSections (F.obj.obj ⋙ forget (ModuleCat.{w} R)) :=
  { toFun := fun f => L.freeSheafHomEquivFixedSections J R F.obj f.hom
    invFun := fun s => ⟨(L.freeSheafHomEquivFixedSections J R F.obj).symm s⟩
    left_inv := fun f => by
      apply ObjectProperty.hom_ext
      exact (L.freeSheafHomEquivFixedSections J R F.obj).left_inv f.hom
    right_inv := fun s =>
      (L.freeSheafHomEquivFixedSections J R F.obj).right_inv s }

variable [HasSheafify J (ModuleCat.{w} R)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- Lifting a fixed section in the discrete category and restricting to the
ordinary site recovers exactly that section. -/
theorem fixedSectionLift_restricts
    (hS : S.IsLiftSystem) (hL : L.EventuallyEquivariant S)
    (F : S.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (s : L.FixedSections (F.obj.obj ⋙ forget (ModuleCat.{w} R))) :
    freeRepresentableHomEquiv J R L.obj
        ((restriction ρ J (ModuleCat.{w} R)).obj F.obj)
        ((L.freeSheafRestrictionIso J R).inv ≫
          (restriction ρ J (ModuleCat.{w} R)).map
            ((L.discreteFreeSheafHomEquivFixedSections S J R hS hL F).symm s).hom) =
      s.val := by
  exact (L.freeRepresentableHomEquiv_restriction J R F.obj
    ((L.freeSheafHomEquivFixedSections J R F.obj).symm s)).trans
      (congrArg Subtype.val
        ((L.freeSheafHomEquivFixedSections J R F.obj).apply_symm_apply s))

end Sheaf

end Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift
