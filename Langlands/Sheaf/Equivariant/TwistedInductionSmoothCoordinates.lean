import Langlands.Sheaf.Equivariant.TwistedInductionCoordinateMaps
import Langlands.Sheaf.Equivariant.LocalActionSmoothPart
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Module and locally discrete coordinates for twisted induction
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

open CategoryTheory CategoryTheory.Limits Opposite
open LocalActionSystem

universe v u uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)
variable {R : Type w} [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The coordinate projections jointly distinguish module sections, without a size condition on G. -/
theorem section_ext (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) (U : TwistedOver P ρ)
    {s t : ((ι P ρ).op.ran.obj F).obj (op U)}
    (h : ∀ g, projection ρ F U g s = projection ρ F U g t) : s = t := by
  have e : ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t) := by
    apply (fanIsLimit ρ F U).hom_ext
    rintro ⟨g⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change projection ρ F U g (r • s) = projection ρ F U g (r • t)
    simp only [map_smul, h g]
  simpa using congrArg (fun k => k.hom (1 : R)) e

/-- All coordinates as a dependent family, viewed as a linear map. -/
def coordinateLinearMap (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) (U : TwistedOver P ρ) :
    ((ι P ρ).op.ran.obj F).obj (op U) →ₗ[R] ∀ g, ↑(objects ρ F U g) :=
  LinearMap.pi fun g => (projection ρ F U g).hom

/-- Every family of module coordinates is realized, by the universal property of the actual Kan fan. -/
theorem coordinateLinearMap_bijective (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    (U : TwistedOver P ρ) : Function.Bijective (coordinateLinearMap ρ F U) := by
  constructor
  · intro s t h
    exact section_ext ρ F U fun g => congrFun h g
  · intro t
    let c : Fan (objects ρ F U) := Fan.mk (ModuleCat.of R R)
      fun g => ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (t g))
    let l : ModuleCat.of R R ⟶ ((ι P ρ).op.ran.obj F).obj (op U) :=
      (fanIsLimit ρ F U).lift c
    refine ⟨l.hom (1 : R), ?_⟩
    funext g
    have e := (fanIsLimit ρ F U).fac c (Discrete.mk g)
    have e' := congrArg (fun k => k.hom (1 : R)) e
    change projection ρ F U g (l.hom (1 : R)) = (1 : R) • t g at e'
    simpa only [coordinateLinearMap, LinearMap.pi_apply, one_smul] using e'

/-- Linear coordinates for the actual induction value, with independent group and module universes. -/
def moduleCoordinates (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) (U : TwistedOver P ρ) :
    ((ι P ρ).op.ran.obj F).obj (op U) ≃ₗ[R] ∀ g, ↑(objects ρ F U g) :=
  LinearEquiv.ofBijective (coordinateLinearMap ρ F U) (coordinateLinearMap_bijective ρ F U)

@[simp]
theorem moduleCoordinates_apply (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    (U : TwistedOver P ρ) (s : ((ι P ρ).op.ran.obj F).obj (op U)) (g : G) :
    moduleCoordinates ρ F U s g = projection ρ F U g s := rfl

/-- Restriction along a twisted arrow, expressed purely in translated module coordinates. -/
def coordinateMap (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) {U V : TwistedOver P ρ}
    (f : U ⟶ V) : (∀ g, ↑(objects ρ F V g)) →ₗ[R] ∀ g, ↑(objects ρ F U g) :=
  LinearMap.pi fun g => (F.map (transport ρ f g).op).hom.comp
    (LinearMap.proj (g * (Hom.twist f)⁻¹))

/-- The explicit coordinate map is the existing right Kan map. -/
theorem moduleCoordinates_map (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    {U V : TwistedOver P ρ} (f : U ⟶ V) (s : ((ι P ρ).op.ran.obj F).obj (op V)) :
    moduleCoordinates ρ F U (((ι P ρ).op.ran.obj F).map f.op s) =
      coordinateMap ρ F f (moduleCoordinates ρ F V s) := by
  funext g
  exact congrArg (fun k => k.hom s) (map_projection ρ F f g)

variable [TopologicalSpace G]

/-- An open subgroup fixes a coordinate family under the explicit reindexing and restriction maps. -/
def IsCoordinateDiscrete (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    {U : TwistedOver P ρ} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (t : ∀ g, ↑(objects ρ F U g)) : Prop :=
  ∃ K : OpenSubgroup G, K ≤ H ∧ ∀ h : (H : Subgroup G), (h : G) ∈ K →
    coordinateMap ρ F (a h).unop t = t

/-- Discreteness of an actual induction section is exactly discreteness of its coordinate family. -/
theorem isDiscreteSection_iff (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    {U : TwistedOver P ρ} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ)
    (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    IsDiscreteSection ((ι P ρ).op.ran.obj F) a s ↔
      IsCoordinateDiscrete ρ F a (moduleCoordinates ρ F U s) := by
  constructor
  · rintro ⟨K, hKH, hK⟩
    refine ⟨K, hKH, fun h hh => ?_⟩
    rw [← moduleCoordinates_map, hK h hh]
  · rintro ⟨K, hKH, hK⟩
    refine ⟨K, hKH, fun h hh => ?_⟩
    apply (moduleCoordinates ρ F U).injective
    rw [moduleCoordinates_map, hK h hh]

variable (L : LocalActionSystem (TwistedOver P ρ) G)

/-- The sieve of restrictions of a coordinate family that factor through a discrete local coordinate family. -/
def coordinateDiscreteSieve (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    {U : TwistedOver P ρ} (t : ∀ g, ↑(objects ρ F U g)) : Sieve U where
  arrows W p := ∃ (V : TwistedOver P ρ) (k : W ⟶ V) (f : V ⟶ U) (H : OpenSubgroup G)
    (a : (H : Subgroup G) →* (End V)ᵐᵒᵖ),
    L.IsAdmissible V H a ∧ IsCoordinateDiscrete ρ F a (coordinateMap ρ F f t) ∧ k ≫ f = p
  downward_closed := by
    rintro W W' p ⟨V, k, f, H, a, ha, ht, rfl⟩ k'
    exact ⟨V, k' ≫ k, f, H, a, ha, ht, Category.assoc _ _ _⟩

/-- The explicit coordinate sieve is the actual discrete sieve of the induced section. -/
theorem coordinateDiscreteSieve_eq (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    {U : TwistedOver P ρ} (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    coordinateDiscreteSieve ρ L F (moduleCoordinates ρ F U s) =
      L.discreteSieve ((ι P ρ).op.ran.obj F) s := by
  ext W p
  constructor
  · rintro ⟨V, k, f, H, a, ha, ht, hp⟩
    refine ⟨V, k, f, H, a, ha, ?_, hp⟩
    apply (isDiscreteSection_iff ρ F a _).2
    rwa [moduleCoordinates_map]
  · rintro ⟨V, k, f, H, a, ha, hs, hp⟩
    refine ⟨V, k, f, H, a, ha, ?_, hp⟩
    rw [← moduleCoordinates_map]
    exact (isDiscreteSection_iff ρ F a _).1 hs

variable (J : GrothendieckTopology (TwistedOver P ρ)) [L.HasAdmissibleRefinements J]

/-- The submodule of coordinate families whose explicit discrete sieve covers. -/
def smoothCoordinateSubmodule (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) (U : TwistedOver P ρ) :
    Submodule R (∀ g, ↑(objects ρ F U g)) :=
  (smoothSubmodule L J ((ι P ρ).op.ran.obj F) U).map (moduleCoordinates ρ F U).toLinearMap

/-- Membership in smooth coordinates is exactly the explicit covering-sieve condition. -/
theorem mem_smoothCoordinateSubmodule_iff (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    (U : TwistedOver P ρ) (t : ∀ g, ↑(objects ρ F U g)) :
    t ∈ smoothCoordinateSubmodule ρ L J F U ↔ coordinateDiscreteSieve ρ L F t ∈ J U := by
  rw [smoothCoordinateSubmodule, Submodule.mem_map_equiv, mem_smoothSubmodule_iff,
    ← coordinateDiscreteSieve_eq ρ L F ((moduleCoordinates ρ F U).symm t),
    LinearEquiv.apply_symm_apply]

/-- Linear coordinates for sections of the existing locally discrete presheaf part. -/
def smoothModuleCoordinates (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R) (U : TwistedOver P ρ) :
    (smoothPresheaf L J ((ι P ρ).op.ran.obj F)).obj (op U) ≃ₗ[R]
      smoothCoordinateSubmodule ρ L J F U :=
  (moduleCoordinates ρ F U).submoduleMap _

@[simp]
theorem smoothModuleCoordinates_val (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R)
    (U : TwistedOver P ρ) (s : (smoothPresheaf L J ((ι P ρ).op.ran.obj F)).obj (op U)) :
    (smoothModuleCoordinates ρ L J F U s).val = moduleCoordinates ρ F U s.val := rfl

section Sheaf

variable (J₀ : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J₀]
variable [L.HasAdmissibleRefinements (twistedTopology ρ J₀)]

/-- Coordinates for the actual sheaf coreflector of induction. -/
def smoothInductionCoordinates (F : Sheaf J₀ (ModuleCat.{w} R)) (U : TwistedOver P ρ) :
    (((smoothCoreflector L (twistedTopology ρ J₀)).obj
      ((induction ρ J₀ (ModuleCat.{w} R)).obj F)).obj.obj.obj (op U)) ≃ₗ[R]
      smoothCoordinateSubmodule ρ L (twistedTopology ρ J₀) F.obj U :=
  smoothModuleCoordinates ρ L (twistedTopology ρ J₀) F.obj U

/-- The coordinates are exactly those of the coreflector inclusion into actual induction. -/
@[simp]
theorem smoothInductionCoordinates_val (F : Sheaf J₀ (ModuleCat.{w} R)) (U : TwistedOver P ρ)
    (s : (((smoothCoreflector L (twistedTopology ρ J₀)).obj
      ((induction ρ J₀ (ModuleCat.{w} R)).obj F)).obj.obj.obj (op U))) :
    (smoothInductionCoordinates ρ L J₀ F U s).val =
      moduleCoordinates ρ F.obj U
        (((smoothSubsheafι L (twistedTopology ρ J₀)).app
          ((induction ρ J₀ (ModuleCat.{w} R)).obj F)).hom.app (op U) s) := rfl

end Sheaf

end Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates
