import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Category.SmoothPartAdjunction
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Functorial carrier universe lifts

Internal infrastructure for the small-diagram preservation assertions of
Renard VI.1.2. Carrier lifts act on maps by conjugating with `up` and `down`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX uG uV uR

namespace Langlands

namespace ModuleUniverseLift

variable {R : Type uR} [Ring R] {ι : Type uV}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Lifting carriers preserves the explicit direct-sum coproduct cocone. -/
def coproductIsColimit (Z : ι → ModuleCat.{uV} R) [DecidableEq ι] :
    IsColimit ((ModuleCat.uliftFunctor.{uX} R).mapCocone
      (ModuleCat.coproductCocone Z)) where
  desc s := ModuleCat.ofHom
    ((DirectSum.toModule (M := fun i => Z i) R ι _
      (fun i => (s.ι.app ⟨i⟩).hom.comp
        (ULift.moduleEquiv (R := R) (M := Z i)).symm.toLinearMap)).comp
      (ULift.moduleEquiv (R := R) (M := DirectSum ι (fun i => Z i))).toLinearMap)
  fac s j := by
    rcases j with ⟨i⟩
    ext x
    change _ = (s.ι.app ⟨i⟩).hom x
    dsimp [ModuleCat.uliftFunctor, ModuleCat.coproductCocone, ULift.moduleEquiv]
    simp only [DirectSum.toModule_lof, LinearMap.comp_apply]
    rfl
  uniq s m h := by
    have hm :
        m.hom.comp (ULift.moduleEquiv (R := R) (M := DirectSum ι (fun i => Z i))).symm.toLinearMap =
          DirectSum.toModule (M := fun i => Z i) R ι _
            (fun i => (s.ι.app ⟨i⟩).hom.comp
        (ULift.moduleEquiv (R := R) (M := Z i)).symm.toLinearMap) := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      have hi := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (h ⟨i⟩))
        (ULift.up x)
      change m.hom (ULift.up (DirectSum.lof R ι (fun i => Z i) i x)) =
        (s.ι.app ⟨i⟩).hom (ULift.up x) at hi
      simpa only [LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe,
        ULift.moduleEquiv_symm_apply] using! hi
    ext x
    exact DFunLike.congr_fun hm x.down

instance preservesCoproduct (Z : ι → ModuleCat.{uV} R) :
    PreservesColimit (Discrete.functor Z) (ModuleCat.uliftFunctor.{uX} R) := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone
    (ModuleCat.coproductCoconeIsColimit Z) (coproductIsColimit Z)

instance preservesCoproducts :
    PreservesColimitsOfShape (Discrete ι) (ModuleCat.uliftFunctor.{uX, uV} R) :=
  preservesColimitsOfShape_of_discrete _

/-- The module carrier lift preserves all colimits with small indexing category. -/
instance preservesColimits :
    PreservesColimitsOfSize.{uV, uV} (ModuleCat.uliftFunctor.{uX, uV} R) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts _

end ModuleUniverseLift

namespace RepUniverseLift

variable (G : Type uG) [Group G]

/-- Carrier universe lift on algebraic complex representations. -/
def functor : Rep.{uV} ℂ G ⥤ Rep.{max uV uX} ℂ G where
  obj A := Rep.of (universeLiftRepresentation.{uX} A.ρ)
  map f := Rep.ofHom
    ((universeLiftEquiv _).toIntertwiningMap.comp
      (f.hom.comp (universeLiftEquiv _).symm.toIntertwiningMap))
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

@[simp]
theorem map_apply {A B : Rep.{uV} ℂ G} (f : A ⟶ B) (x : ULift.{uX} A.V) :
    ((functor.{uX} G).map f).hom x = ULift.up (f.hom x.down) := rfl

/-- Lifting algebraic representation carriers is fully faithful. -/
def fullyFaithful : (functor.{uX, uG, uV} G).FullyFaithful where
  preimage f := Rep.ofHom
    ((universeLiftEquiv _).symm.toIntertwiningMap.comp
      (f.hom.comp (universeLiftEquiv _).toIntertwiningMap))
  map_preimage f := by
    ext x
    rfl
  preimage_map f := by
    ext x
    rfl

instance : (functor.{uX, uG, uV} G).Full := (fullyFaithful G).full
instance : (functor.{uX, uG, uV} G).Faithful := (fullyFaithful G).faithful

/-- Forgetting a lifted action is the module carrier lift. -/
def forgetIso :
    functor.{uX, uG, uV} G ⋙ forget₂ (Rep ℂ G) (ModuleCat ℂ) ≅
      forget₂ (Rep.{uV} ℂ G) (ModuleCat ℂ) ⋙ ModuleCat.uliftFunctor.{uX} ℂ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    ext x
    rfl)

instance preservesLimits :
    PreservesLimitsOfSize.{uV, uV} (functor.{uX, uG, uV} G) := by
  have : PreservesLimitsOfSize.{uV, uV}
      (functor.{uX, uG, uV} G ⋙ forget₂ (Rep ℂ G) (ModuleCat ℂ)) :=
    preservesLimits_of_natIso (forgetIso G).symm
  have : ReflectsLimitsOfSize.{uV, uV}
      (forget₂ (Rep.{max uV uX} ℂ G) (ModuleCat ℂ)) :=
    reflectsLimitsOfSize_shrink.{uV, uX, uV, uX} _
  exact preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep ℂ G) (ModuleCat ℂ))

instance preservesColimits :
    PreservesColimitsOfSize.{uV, uV} (functor.{uX, uG, uV} G) := by
  have : PreservesColimitsOfSize.{uV, uV}
      (functor.{uX, uG, uV} G ⋙ forget₂ (Rep ℂ G) (ModuleCat ℂ)) :=
    preservesColimits_of_natIso (forgetIso G).symm
  have : ReflectsColimitsOfSize.{uV, uV}
      (forget₂ (Rep.{max uV uX} ℂ G) (ModuleCat ℂ)) :=
    reflectsColimitsOfSize_shrink.{uV, uX, uV, uX} _
  exact preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep ℂ G) (ModuleCat ℂ))

end RepUniverseLift

namespace SmoothRep

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- The published smooth carrier lift, made functorial by conjugation. -/
def universeLiftFunctor :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, max uV uX} ℂ G where
  obj A := universeLift.{uX} A
  map f := ofHom
    ((universeLiftEquiv _).toIntertwiningMap.comp
      ((hom f).comp (universeLiftEquiv _).symm.toIntertwiningMap))
  map_id _ := by
    apply ObjectProperty.hom_ext
    ext x
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    ext x
    rfl

@[simp]
theorem universeLiftFunctor_map_apply {A B : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) (x : universeLift.{uX} A) :
    hom ((universeLiftFunctor G).map f) x = ULift.up (hom f x.down) := rfl

/-- Smooth carrier lifts are fully faithful. -/
def fullyFaithfulUniverseLiftFunctor :
    (universeLiftFunctor.{uX, uG, uV} G).FullyFaithful where
  preimage f := ofHom
    ((universeLiftEquiv _).symm.toIntertwiningMap.comp
      ((hom f).comp (universeLiftEquiv _).toIntertwiningMap))
  map_preimage f := by
    apply ObjectProperty.hom_ext
    ext x
    rfl
  preimage_map f := by
    apply ObjectProperty.hom_ext
    ext x
    rfl

instance : (universeLiftFunctor.{uX, uG, uV} G).Full :=
  (fullyFaithfulUniverseLiftFunctor G).full

instance : (universeLiftFunctor.{uX, uG, uV} G).Faithful :=
  (fullyFaithfulUniverseLiftFunctor G).faithful

/-- Smooth and algebraic carrier lifts commute with the inclusion. -/
def universeLiftFunctorToRepIso :
    universeLiftFunctor.{uX, uG, uV} G ⋙ toRep ≅
      toRep ⋙ RepUniverseLift.functor.{uX, uG, uV} G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    ext x
    rfl)

variable [IsTopologicalGroup G]

/-- Raising smooth carrier universes preserves small colimits. -/
instance universeLiftFunctor_preservesColimits :
    PreservesColimitsOfSize.{uV, uV} (universeLiftFunctor.{uX, uG, uV} G) := by
  have : PreservesColimitsOfSize.{uV, uV}
      (toRep : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uV} ℂ G) :=
    (toRepSmoothPartAdjunction ℂ G).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{uV, uV}
      (universeLiftFunctor.{uX, uG, uV} G ⋙ toRep) :=
    preservesColimits_of_natIso (universeLiftFunctorToRepIso G).symm
  exact preservesColimits_of_reflects_of_preserves _ toRep

end SmoothRep

end Langlands
