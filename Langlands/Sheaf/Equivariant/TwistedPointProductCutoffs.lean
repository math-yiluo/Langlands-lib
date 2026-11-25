import Langlands.Sheaf.Equivariant.TwistedInductionCutoffs
import Langlands.Sheaf.PointProductSetSections

/-! # Stable spatial cutoffs in induced point products -/

noncomputable section

attribute [local instance] Classical.propDecidable

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u uG wI w uY wM

namespace Langlands.Sheaf.PointProduct

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → J.Point.{max wI w})
variable {R : Type (max wI w)} [CommRing R]

private local instance : HasProducts.{wI} (ModuleCat.{max wI w} R) := by
  let := hasLimitsOfSizeShrink.{wI, wI} (ModuleCat.{max wI w} R)
  infer_instance

variable (M : I → ModuleCat.{max wI w} R)

/-- Restriction of a raw point product along an arrow with injective point fibers
is surjective on sections: extend each coefficient function by zero. -/
theorem map_surjective_of_fiber_injective {U V : C} (f : U ⟶ V)
    (hf : ∀ i, Function.Injective ((points i).fiber.map f)) :
    Function.Surjective ((productSheaf points (ModuleCat R) M).obj.map f.op) := by
  classical
  intro s
  let t : ∀ i, (points i).fiber.obj V → M i := fun i y =>
    if hy : ∃ x, (points i).fiber.map f x = y then
      sectionCoordinates points M U s i hy.choose else 0
  refine ⟨(sectionCoordinates points M V).symm t, ?_⟩
  apply (sectionCoordinates points M U).injective
  funext i x
  rw [sectionCoordinates_restrict, LinearEquiv.apply_symm_apply]
  change (if hy : ∃ z, (points i).fiber.map f z = (points i).fiber.map f x then
    sectionCoordinates points M U s i hy.choose else 0) = _
  rw [dite_eq_left ⟨x, rfl⟩]
  exact congrArg (fun z => sectionCoordinates points M U s i z)
    (hf i (Exists.choose_spec (show ∃ z,
      (points i).fiber.map f z = (points i).fiber.map f x from ⟨x, rfl⟩)))

/-- In particular, raw point products have surjective restrictions along monomorphisms. -/
theorem map_surjective_of_mono [LocallySmall.{max wI w} C]
    {U V : C} (f : U ⟶ V) [Mono f] :
    Function.Surjective ((productSheaf points (ModuleCat R) M).obj.map f.op) :=
  map_surjective_of_fiber_injective points M f
    (fun i => (points i).fiber_map_injective_of_mono f)

end Langlands.Sheaf.PointProduct

namespace Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

open CategoryTheory CategoryTheory.Limits Opposite
open LocalActionSystem Langlands.Sheaf.PointProduct

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)
variable {J : GrothendieckTopology (P.Over ⊤ X)}
variable {I : Type wI} (points : I → J.Point.{max wI w})
variable {R : Type (max wI w)} [CommRing R]

local instance : HasProducts.{wI} (ModuleCat.{max wI w} R) := by
  let := hasLimitsOfSizeShrink.{wI, wI} (ModuleCat.{max wI w} R)
  infer_instance

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{max wI w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]
variable (M : I → ModuleCat.{max wI w} R)

section Spatial

variable {Y : Type uY} [MulAction G Y] (π : I → Y) (V : Set Y)

/-- Keep a point coefficient exactly when its original spatial coordinate lies in `V`. -/
def spatialCoefficientMask (g : G) : M ⟶ M := fun i =>
  if g⁻¹ • π i ∈ V then 𝟙 (M i) else 0

/-- The corresponding natural endomorphism of the raw point-product presheaf. -/
def spatialMask (g : G) :
    (productSheaf points (ModuleCat R) M).obj ⟶
      (productSheaf points (ModuleCat R) M).obj :=
  ((productFunctor points (ModuleCat R)).map (spatialCoefficientMask M π V g)).hom

/-- A stable set makes the coefficient mask invariant under right subgroup multiplication. -/
theorem spatialCoefficientMask_mul {H : Subgroup G}
    (hV : ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V)
    (g k : G) (hk : k ∈ H) :
    spatialCoefficientMask M π V (g * k) = spatialCoefficientMask M π V g := by
  classical
  funext i
  have he : (g * k)⁻¹ • π i ∈ V ↔ g⁻¹ • π i ∈ V := by
    constructor
    · intro hy
      have hh := hV k hk _ hy
      simpa only [mul_inv_rev, mul_smul, smul_inv_smul] using hh
    · intro hy
      simpa only [mul_inv_rev, mul_smul] using hV k⁻¹ (H.inv_mem hk) _ hy
  simp only [spatialCoefficientMask, he]

omit [P.RespectsIso] in
/-- A stable set gives the same invariance for the actual product endomorphisms. -/
theorem spatialMask_mul {H : Subgroup G}
    (hV : ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V)
    (g k : G) (hk : k ∈ H) :
    spatialMask points M π V (g * k) = spatialMask points M π V g := by
  unfold spatialMask
  rw [spatialCoefficientMask_mul M π V hV g k hk]

/-- Cut off actual induced sections by their original spatial coordinates. -/
def spatialCutoff (U : TwistedOver P ρ)
    (s : ((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj).obj (op U)) :
    ((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj).obj (op U) :=
  indexedMapApp ρ (spatialMask points M π V) U s

/-- The cutoff is literally multiplication of each point coordinate by its mask. -/
theorem spatialCutoff_coordinates (U : TwistedOver P ρ)
    (s : ((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj).obj (op U))
    (g : G) (i : I) (p : (points i).fiber.obj ((translate P ρ g).obj U.obj)) :
    sectionCoordinates points M ((translate P ρ g).obj U.obj)
        (moduleCoordinates ρ (productSheaf points (ModuleCat R) M).obj U
          (spatialCutoff ρ points M π V U s) g) i p =
      if g⁻¹ • π i ∈ V then
        sectionCoordinates points M ((translate P ρ g).obj U.obj)
          (moduleCoordinates ρ (productSheaf points (ModuleCat R) M).obj U s g) i p
      else 0 := by
  classical
  rw [spatialCutoff, indexedMapApp_coordinates]
  simp only [sectionCoordinates_apply]
  have he := ConcreteCategory.congr_hom
    (sectionCoordinate_map points M (spatialCoefficientMask M π V g)
      ((translate P ρ g).obj U.obj) i p)
    (moduleCoordinates ρ (productSheaf points (ModuleCat R) M).obj U s g)
  change sectionCoordinate points M ((translate P ρ g).obj U.obj) i p
      ((spatialMask points M π V g).app _
        (moduleCoordinates ρ (productSheaf points (ModuleCat R) M).obj U s g)) =
    (spatialCoefficientMask M π V g i)
      (sectionCoordinate points M ((translate P ρ g).obj U.obj) i p
        (moduleCoordinates ρ (productSheaf points (ModuleCat R) M).obj U s g)) at he
  rw [he]
  split_ifs <;> simp_all [spatialCoefficientMask]

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
variable (K : GrothendieckTopology (TwistedOver P ρ)) [L.HasAdmissibleRefinements K]

include hL in
/-- Stable spatial masks preserve the actual locally discrete part of induction. -/
theorem spatialCutoff_mem_smoothSubmodule (H : OpenSubgroup G)
    (hV : ∀ h ∈ H, ∀ y ∈ V, h • y ∈ V)
    (U : TwistedOver P ρ)
    (s : ((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj).obj (op U))
    (hs : s ∈ smoothSubmodule L K
      ((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj) U) :
    spatialCutoff ρ points M π V U s ∈ smoothSubmodule L K
      ((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj) U :=
  indexedMapApp_mem_smoothSubmodule ρ L hL K (spatialMask points M π V) H
    (spatialMask_mul points M π V hV) U s hs

end Spatial

/-- Surjective ordinary-coordinate restrictions give surjective restrictions
of the actual right Kan induction. -/
theorem map_surjective_of_coordinates {S : Type wM} [CommRing S]
    [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{wM} S,
      (ι P ρ).op.HasPointwiseRightKanExtension F]
    {F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{wM} S}
    {U V : TwistedOver P ρ} (f : U ⟶ V)
    (hF : ∀ g, Function.Surjective (F.map (transport ρ f g).op)) :
    Function.Surjective (((ι P ρ).op.ran.obj F).map f.op) := by
  classical
  intro s
  have hp := fun g => hF g (moduleCoordinates ρ F U s g)
  choose t₀ ht using hp
  let e : G ≃ G := Equiv.mulRight (Hom.twist f)⁻¹
  let t := (Equiv.piCongrLeft (fun g => ↑(objects ρ F V g)) e) t₀
  refine ⟨(moduleCoordinates ρ F V).symm t, ?_⟩
  apply (moduleCoordinates ρ F U).injective
  rw [moduleCoordinates_map]
  funext g
  simp only [coordinateMap, LinearMap.pi_apply, LinearEquiv.apply_symm_apply]
  change F.map (transport ρ f g).op
    ((Equiv.piCongrLeft (fun j => ↑(objects ρ F V j)) e) t₀ (e g)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  exact ht g

/-- Raw induced point products extend sections along arrows whenever
all translated point-fiber maps are injective. -/
theorem pointProduct_map_surjective_of_fiber_injective
    {U V : TwistedOver P ρ} (f : U ⟶ V)
    (hF : ∀ g i, Function.Injective ((points i).fiber.map (transport ρ f g))) :
    Function.Surjective
      (((ι P ρ).op.ran.obj (productSheaf points (ModuleCat R) M).obj).map f.op) :=
  map_surjective_of_coordinates ρ f fun g =>
    Langlands.Sheaf.PointProduct.map_surjective_of_fiber_injective points M
      (transport ρ f g) (hF g)

end Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates
