import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.Torus.Products
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Products and smooth intersections of actual integral group models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H J : GroupScheme (Spec (CommRingCat.of K))}

/-- Composition retains the originally specified generic group homomorphisms. -/
def Hom.comp {L : IntegralModel R K G} {M : IntegralModel R K H}
    {N : IntegralModel R K J} {f : G ⟶ H} {g : H ⟶ J}
    (φ : L.Hom M f) (ψ : M.Hom N g) : L.Hom N (f ≫ g) where
  hom := φ.hom ≫ ψ.hom
  generic_comm := by
    rw [Functor.map_comp, Category.assoc, ψ.generic_comm,
      ← Category.assoc, φ.generic_comm, Category.assoc]

variable (M : IntegralModel R K G) (N : IntegralModel R K H)

/-- The actual product model, with the product of the supplied generic identifications. -/
def product : IntegralModel R K (G ⊗ H) where
  group := M.group ⊗ N.group
  affine := prop_tensor_hom (@IsAffineHom) M.group.X N.group.X
    inferInstance inferInstance
  flat := prop_tensor_hom (@Flat) M.group.X N.group.X
    inferInstance inferInstance
  finiteType := prop_tensor_hom (@LocallyOfFiniteType) M.group.X N.group.X
    inferInstance inferInstance
  genericIso := baseChangeTensorIso (Spec.algebraMap R K) M.group N.group ≪≫
    (M.genericIso ⊗ᵢ N.genericIso)

/-- The first product projection extends the original first generic projection. -/
def productFst : (M.product N).Hom M (fst G H) where
  hom := fst M.group N.group
  generic_comm := by
    change _ = (baseChangeTensorIso (Spec.algebraMap R K) M.group N.group).hom ≫
      (M.genericIso.hom ⊗ₘ N.genericIso.hom) ≫ fst G H
    rw [tensorHom_fst, ← Category.assoc]
    exact congrArg (fun a => a ≫ M.genericIso.hom)
      (Functor.OplaxMonoidal.δ_fst (baseChange (Spec.algebraMap R K)) M.group N.group).symm

/-- The second product projection extends the original second generic projection. -/
def productSnd : (M.product N).Hom N (snd G H) where
  hom := snd M.group N.group
  generic_comm := by
    change _ = (baseChangeTensorIso (Spec.algebraMap R K) M.group N.group).hom ≫
      (M.genericIso.hom ⊗ₘ N.genericIso.hom) ≫ snd G H
    rw [tensorHom_snd, ← Category.assoc]
    exact congrArg (fun a => a ≫ N.genericIso.hom)
      (Functor.OplaxMonoidal.δ_snd (baseChange (Spec.algebraMap R K)) M.group N.group).symm

/-- Products of smooth actual models are smooth. -/
theorem product_isSmooth (hM : M.IsSmooth) (hN : N.IsSmooth) :
    (M.product N).IsSmooth :=
  prop_tensor_hom (@Smooth) M.group.X N.group.X hM hN

/-- The product model has exactly those generic points whose two projections are integral. -/
theorem product_integralPoints :
    (M.product N).integralPoints =
      M.integralPoints.comap (rationalPoints.map (fst G H)) ⊓
        N.integralPoints.comap (rationalPoints.map (snd G H)) := by
  ext g
  change g ∈ (M.product N).integralPoints ↔
    rationalPoints.map (fst G H) g ∈ M.integralPoints ∧
      rationalPoints.map (snd G H) g ∈ N.integralPoints
  constructor
  · intro hg
    exact ⟨(M.productFst N).map_mem_integralPoints hg,
      (M.productSnd N).map_mem_integralPoints hg⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let z : (M.product N).integralSections :=
      (productPointsEquiv M.group N.group (Over.mk (𝟙 _))).symm (x, y)
    have hz₁ : rationalPoints.map (M.productFst N).hom z = x :=
      congrArg Prod.fst
        ((productPointsEquiv M.group N.group (Over.mk (𝟙 _))).apply_symm_apply (x, y))
    have hz₂ : rationalPoints.map (M.productSnd N).hom z = y :=
      congrArg Prod.snd
        ((productPointsEquiv M.group N.group (Over.mk (𝟙 _))).apply_symm_apply (x, y))
    refine ⟨z, ?_⟩
    apply (productPointsEquiv G H (Over.mk (𝟙 _))).injective
    apply Prod.ext
    · change rationalPoints.map (fst G H) ((M.product N).integralPointMap z) =
        rationalPoints.map (fst G H) g
      rw [← (M.productFst N).integralPointMap_naturality z, hz₁, hx]
    · change rationalPoints.map (snd G H) ((M.product N).integralPointMap z) =
        rationalPoints.map (snd G H) g
      rw [← (M.productSnd N).integralPointMap_naturality z, hz₂, hy]

/-- Pulling the product's integral-point subgroup back along the original
generic diagonal gives the literal intersection. -/
theorem product_integralPoints_comap_diagonal (M N : IntegralModel R K G) :
    (M.product N).integralPoints.comap
        (rationalPoints.map (lift (𝟙 G) (𝟙 G))) =
      M.integralPoints ⊓ N.integralPoints := by
  rw [product_integralPoints]
  ext g
  change
    (rationalPoints.map (fst G G)
        (rationalPoints.map (lift (𝟙 G) (𝟙 G)) g) ∈ M.integralPoints ∧
      rationalPoints.map (snd G G)
        (rationalPoints.map (lift (𝟙 G) (𝟙 G)) g) ∈ N.integralPoints) ↔
      (g ∈ M.integralPoints ∧ g ∈ N.integralPoints)
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
    lift_fst, lift_snd, Grp.id_hom_hom, Category.comp_id]

/-- Generic-identity maps put the source's actual integral points in the intersection. -/
theorem Hom.integralPoints_le_inf {L M N : IntegralModel R K G}
    (φ : L.Hom M (𝟙 G)) (ψ : L.Hom N (𝟙 G)) :
    L.integralPoints ≤ M.integralPoints ⊓ N.integralPoints := by
  intro g hg
  change g ∈ M.integralPoints ∧ g ∈ N.integralPoints
  constructor
  · simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      φ.map_mem_integralPoints hg
  · simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      ψ.map_mem_integralPoints hg

/-- A smooth actual model for the intersection of two actual integral-point subgroups. -/
def SmoothIntersectionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom],
    Smooth G.X.hom →
    ∀ M N : IntegralModel R K G,
      ∃ L : IntegralModel R K G,
        L.IsSmooth ∧ Nonempty (L.Hom M (𝟙 G)) ∧ Nonempty (L.Hom N (𝟙 G)) ∧
          L.integralPoints = M.integralPoints ⊓ N.integralPoints

end Langlands.GroupScheme.IntegralModel
