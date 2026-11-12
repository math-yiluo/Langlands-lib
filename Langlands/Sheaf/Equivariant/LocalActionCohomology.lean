import Langlands.Sheaf.Equivariant.LocalActionDiscretePart
import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Derived sections of discrete sheaves as representations

An action of a monoid `K` on an object `U` of a site by endomorphisms makes the
sections over `U` of every module presheaf a representation of `K`,
functorially. For module sheaves this functor is left exact. For an admissible
local action of an open subgroup `H` on `U`, sections of discrete sheaves are
smooth representations of `H`. Discrete module sheaves form an abelian category
with enough injectives under the hypotheses of `LocalActionDiscretePart`, so these
section functors have right derived functors: the cohomology of `U` with
coefficients in a discrete sheaf, as a representation.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG uK uR w

variable {T : Type u} [Category.{v} T]
variable {R : Type uR} [CommRing R]

section Sections

variable {K : Type uK} [Monoid K]

/-- The representation of `K` on the sections over `U` of a module presheaf,
given an action `a` of `K` on `U` by endomorphisms: `k` acts by restriction
along `(a k).unop`. -/
def actionRepresentation (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    Representation R K (F.obj (op U)) where
  toFun k := (F.map (a k).unop.op).hom
  map_one' := by
    rw [map_one]
    change (F.map (𝟙 (op U))).hom = 1
    rw [F.map_id]
    rfl
  map_mul' g h := by
    rw [map_mul, MulOpposite.unop_mul, End.mul_def, op_comp, F.map_comp]
    rfl

theorem actionRepresentation_apply (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {U : T} (a : K →* (End U)ᵐᵒᵖ)
    (k : K) (s : F.obj (op U)) :
    actionRepresentation F a k s = (F.map (a k).unop.op).hom s :=
  rfl

/-- For an open subgroup, this is the published local representation. -/
theorem actionRepresentation_eq_localRepresentation {G : Type uG} [Group G] [TopologicalSpace G]
    (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {U : T} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) :
    actionRepresentation F a = localRepresentation F a :=
  rfl

/-- A morphism of presheaves is equivariant on sections over `U`. -/
def actionIntertwiningMap {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F') {U : T}
    (a : K →* (End U)ᵐᵒᵖ) :
    (actionRepresentation F a).IntertwiningMap (actionRepresentation F' a) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (actionRepresentation F a)
    (actionRepresentation F' a) (φ.app (op U)).hom fun k s => by
      rw [actionRepresentation_apply, actionRepresentation_apply]
      exact NatTrans.naturality_apply φ (a k).unop.op s

@[simp]
theorem actionIntertwiningMap_apply {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ F') {U : T}
    (a : K →* (End U)ᵐᵒᵖ) (s : F.obj (op U)) :
    actionIntertwiningMap φ a s = φ.app (op U) s :=
  rfl

variable (R) in
/-- Sections over `U` as a representation of `K`, functorially in the module
presheaf. -/
def sectionsRep {U : T} (a : K →* (End U)ᵐᵒᵖ) : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R K where
  obj F := Rep.of (actionRepresentation F a)
  map φ := Rep.ofHom (actionIntertwiningMap φ a)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem sectionsRep_obj_ρ {U : T} (a : K →* (End U)ᵐᵒᵖ) (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    ((sectionsRep R a).obj F).ρ = actionRepresentation F a :=
  rfl

@[simp]
theorem sectionsRep_map_hom_apply {U : T} (a : K →* (End U)ᵐᵒᵖ) {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R}
    (φ : F ⟶ F') (s : F.obj (op U)) :
    ((sectionsRep R a).map φ).hom s = φ.app (op U) s :=
  rfl

instance sectionsRep_additive {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    (sectionsRep R a : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R K).Additive where
  map_add := by
    intros
    ext
    rfl

/-- The module underlying the sections representation is evaluation at `U`. -/
def sectionsRepForgetIso {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    sectionsRep R a ⋙ forget₂ (Rep.{w} R K) (ModuleCat.{w} R) ≅
      (evaluation Tᵒᵖ (ModuleCat.{w} R)).obj (op U) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable (J : GrothendieckTopology T)

variable (R) in
/-- Sections over `U` of module sheaves, as a representation of `K`. -/
def sheafSectionsRep {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    Sheaf J (ModuleCat.{w} R) ⥤ Rep.{w} R K :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ sectionsRep R a

/-- Sections of module sheaves over `U` are left exact as a representation-valued
functor. -/
instance sheafSectionsRep_preservesFiniteLimits {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    PreservesFiniteLimits
      (sheafSectionsRep R J a : Sheaf J (ModuleCat.{w} R) ⥤ Rep.{w} R K) := by
  have : PreservesFiniteLimits
      (sheafSectionsRep R J a ⋙ forget₂ (Rep.{w} R K) (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso
      (Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{w} R)) (sectionsRepForgetIso a)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R K) (ModuleCat.{w} R))

instance sheafSectionsRep_additive {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    (sheafSectionsRep R J a : Sheaf J (ModuleCat.{w} R) ⥤ Rep.{w} R K).Additive :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{w} R) ⋙ sectionsRep R a).Additive

end Sections

section Discrete

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (R) (L : LocalActionSystem T G) (J : GrothendieckTopology T)

section RepValued

variable {K : Type uK} [Monoid K]

/-- Sections over `U` of discrete module sheaves, as a representation of `K`. -/
def discreteSectionsRep {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ Rep.{w} R K :=
  L.discreteSheafInclusion (ModuleCat.{w} R) J ⋙ sheafSectionsRep R J a

instance discreteSectionsRep_additive {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    (discreteSectionsRep R L J a : L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ Rep.{w} R K).Additive :=
  inferInstanceAs
    (L.discreteSheafInclusion (ModuleCat.{w} R) J ⋙ sheafSectionsRep R J a).Additive

variable [HasSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]

/-- Sections of discrete module sheaves are left exact. -/
instance discreteSectionsRep_preservesFiniteLimits {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    PreservesFiniteLimits
      (discreteSectionsRep R L J a : L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ Rep.{w} R K) :=
  comp_preservesFiniteLimits _ _

variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- Degree `q` cohomology over `U` of discrete module sheaves, as a
representation of `K`: the right derived functors of the sections, computed
with injective resolutions among discrete sheaves. -/
def discreteDerivedRep {U : T} (a : K →* (End U)ᵐᵒᵖ) (q : ℕ) :
    L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ Rep.{w} R K :=
  (discreteSectionsRep R L J a).rightDerived q

/-- In degree zero, derived sections are sections. -/
def discreteDerivedRepZeroIso {U : T} (a : K →* (End U)ᵐᵒᵖ) :
    discreteDerivedRep R L J a 0 ≅ (discreteSectionsRep R L J a :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ Rep.{w} R K) :=
  (discreteSectionsRep R L J a).rightDerivedZeroIsoSelf

/-- Derived sections are the homology of the sections of any injective
resolution among discrete sheaves. -/
def discreteDerivedRepIso {U : T} (a : K →* (End U)ᵐᵒᵖ)
    {F : L.DiscreteSheaf (ModuleCat.{w} R) J} (I : InjectiveResolution F) (q : ℕ) :
    (discreteDerivedRep R L J a q).obj F ≅
      (HomologicalComplex.homologyFunctor (Rep.{w} R K) (ComplexShape.up ℕ) q).obj
        (((discreteSectionsRep R L J a).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (discreteSectionsRep R L J a) q

/-- Derived sections vanish in positive degrees on injective discrete sheaves. -/
theorem isZero_discreteDerivedRep_succ_of_injective {U : T} (a : K →* (End U)ᵐᵒᵖ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) J) [Injective F] (q : ℕ) :
    IsZero ((discreteDerivedRep R L J a (q + 1)).obj F) :=
  (discreteSectionsRep R L J a).isZero_rightDerived_obj_injective_succ q F

end RepValued

section Smooth

variable {U : T} {H : OpenSubgroup G} {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ}

/-- On an object with an admissible local action of `H`, the sections of a
discrete module sheaf form a smooth representation of `H`. -/
theorem isSmooth_actionRepresentation (ha : L.IsAdmissible U H a)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) J) : IsSmooth (actionRepresentation F.obj.obj a) :=
  (L.isDiscrete_iff_isSmooth F.obj.obj).1 F.property U H a ha

/-- Sections over an object with an admissible local action of `H`, on discrete
module sheaves, as smooth representations of `H`. -/
def discreteSectionsSmooth (ha : L.IsAdmissible U H a) :
    L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G) :=
  (smoothRepProperty R (H : Subgroup G)).lift (discreteSectionsRep R L J a)
    (isSmooth_actionRepresentation R L J ha)

/-- The algebraic representation underlying the smooth sections. -/
def discreteSectionsSmoothToRepIso (ha : L.IsAdmissible U H a) :
    (discreteSectionsSmooth R L J ha :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G)) ⋙
        SmoothRep.toRep ≅ discreteSectionsRep R L J a :=
  ObjectProperty.liftCompιIso _ _ _

instance discreteSectionsSmooth_additive (ha : L.IsAdmissible U H a) :
    (discreteSectionsSmooth R L J ha :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G)).Additive where
  map_add := by
    intros
    rfl

variable [HasSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]

/-- Smooth sections of discrete module sheaves are left exact. -/
instance discreteSectionsSmooth_preservesFiniteLimits (ha : L.IsAdmissible U H a) :
    PreservesFiniteLimits (discreteSectionsSmooth R L J ha :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G)) := by
  have : PreservesFiniteLimits ((discreteSectionsSmooth R L J ha :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G)) ⋙
        SmoothRep.toRep) :=
    preservesFiniteLimits_of_natIso (discreteSectionsSmoothToRepIso R L J ha).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- Degree `q` cohomology over an object with an admissible local action of
`H`, with coefficients in a discrete module sheaf, as a smooth representation of
`H`. -/
def discreteDerived (ha : L.IsAdmissible U H a) (q : ℕ) :
    L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G) :=
  (discreteSectionsSmooth R L J ha).rightDerived q

/-- In degree zero, derived smooth sections are smooth sections. -/
def discreteDerivedZeroIso (ha : L.IsAdmissible U H a) :
    discreteDerived R L J ha 0 ≅ (discreteSectionsSmooth R L J ha :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R (H : Subgroup G)) :=
  (discreteSectionsSmooth R L J ha).rightDerivedZeroIsoSelf

/-- Derived smooth sections are the homology of the smooth sections of any
injective resolution among discrete sheaves. -/
def discreteDerivedIso (ha : L.IsAdmissible U H a) {F : L.DiscreteSheaf (ModuleCat.{w} R) J}
    (I : InjectiveResolution F) (q : ℕ) :
    (discreteDerived R L J ha q).obj F ≅
      (HomologicalComplex.homologyFunctor (SmoothRep.{uR, uG, w} R (H : Subgroup G))
        (ComplexShape.up ℕ) q).obj
        (((discreteSectionsSmooth R L J ha).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (discreteSectionsSmooth R L J ha) q

/-- Derived smooth sections vanish in positive degrees on injective discrete
sheaves. -/
theorem isZero_discreteDerived_succ_of_injective (ha : L.IsAdmissible U H a)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) J) [Injective F] (q : ℕ) :
    IsZero ((discreteDerived R L J ha (q + 1)).obj F) :=
  (discreteSectionsSmooth R L J ha).isZero_rightDerived_obj_injective_succ q F

end Smooth

end Discrete

end Langlands.Sheaf.Equivariant
