import Langlands.Geometry.Building.ValuationBuildingApartmentAxiomTransport
import Langlands.Geometry.Building.ParahoricBuildingAxioms

/-! # Transport of every actual root-reflection element -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Geometry.Building.AffineRootSystem
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B₁ B₂ : ValuationBuildingData G)
  (σ : B₁.S ≅ B₂.S)
  (hσ : B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i)

include hσ

/-- The same ordered pair is an actual opposite factor pair on either torus parametrization. -/
theorem isOppositeFactorPair_torusIso_iff (a : characterLattice B₁.S)
    (u : rationalPoints G) (p : rationalPoints G × rationalPoints G) :
    RelativeRoot.IsOppositeFactorPair B₂.i (characterLattice.congr σ a) u p ↔
      RelativeRoot.IsOppositeFactorPair B₁.i a u p := by
  change (p.1 ∈ rootGroupPoints B₂.i (-(characterLattice.congr σ a)) ∧
      p.2 ∈ rootGroupPoints B₂.i (-(characterLattice.congr σ a)) ∧
      p.1 * u * p.2 ∈ normalizerPoints B₂.i) ↔ _
  rw [← map_neg, rootGroupPoints_eq_of_torusIso σ hσ,
    ← normalizerPoints_eq_of_torusIso B₁ B₂ σ hσ]
  rfl

/-- The full types of ordered opposite factor pairs are identified by the identity on points. -/
def oppositeFactorPairsEquivOfTorusIso (a : characterLattice B₁.S)
    (u : rationalPoints G) :
    {p // RelativeRoot.IsOppositeFactorPair B₁.i a u p} ≃
      {p // RelativeRoot.IsOppositeFactorPair B₂.i (characterLattice.congr σ a) u p} where
  toFun p := ⟨p.val, (isOppositeFactorPair_torusIso_iff B₁ B₂ σ hσ a u p.val).2 p.property⟩
  invFun p := ⟨p.val, (isOppositeFactorPair_torusIso_iff B₁ B₂ σ hσ a u p.val).1 p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem oppositeFactorPairsEquivOfTorusIso_apply (a : characterLattice B₁.S)
    (u : rationalPoints G)
    (p : {p // RelativeRoot.IsOppositeFactorPair B₁.i a u p}) :
    (oppositeFactorPairsEquivOfTorusIso B₁ B₂ σ hσ a u p).val = p.val := rfl

/-- The transported normalizer element retains the actual product of the ordered factors. -/
theorem normalizerEquiv_reflectionElement
    {α : relativeRoots B₁.i} {β : relativeRoots B₂.i}
    (hβ : (β : characterLattice B₂.S) = characterLattice.congr σ α)
    {u : rationalPoints G} {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B₁.i (α : characterLattice B₁.S) u p) :
    normalizerEquivOfTorusIso B₁ B₂ σ hσ (B₁.reflectionElement hp) =
      B₂.reflectionElement (by
        rw [hβ]
        exact (isOppositeFactorPair_torusIso_iff B₁ B₂ σ hσ α u p).2 hp) := by
  apply Subtype.ext
  rfl

variable (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hfamily : ∀ x : B₁.Apartment,
    (e x).val = RootFunctionFamily.transportEquiv σ (Iso.refl G) x.val)

include hfamily

omit hσ in
/-- Every actual family value agrees, at every corresponding apartment point. -/
theorem val_apply_of_family_comparison (x : B₁.Apartment)
    (a : characterLattice B₁.S) (u : rationalPoints G) :
    (e x).val (characterLattice.congr σ a) u = x.val a u := by
  rw [hfamily, RootFunctionFamily.transportEquiv_apply]
  simp only [AddEquiv.symm_apply_apply, Iso.refl_inv, rationalPoints.map_apply,
    Grp.id_hom_hom, Category.comp_id]

omit hσ in
/-- The full actual reflection hyperplane is the image of the source hyperplane. -/
theorem image_reflectionHyperplane_of_family_comparison
    (α : relativeRoots B₁.i) (β : relativeRoots B₂.i)
    (hβ : (β : characterLattice B₂.S) = characterLattice.congr σ α)
    (u : rationalPoints G) :
    e '' B₁.reflectionHyperplane α u = B₂.reflectionHyperplane β u := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image]
  change x.val α u = 0 ↔ (e x).val β u = 0
  rw [hβ, val_apply_of_family_comparison B₁ B₂ σ e hfamily]

/-- The affine reflection functional agrees on every nonidentity actual root point. -/
theorem reflectionFunctional_of_family_comparison
    (α : relativeRoots B₁.i) (β : relativeRoots B₂.i)
    (hβ : (β : characterLattice B₂.S) = characterLattice.congr σ α)
    {u : rationalPoints G} (hu : u ∈ B₁.rootGroup α) (h1 : u ≠ 1) :
    affineFunctionalTransport e (B₁.reflectionFunctional α u) =
      B₂.reflectionFunctional β u := by
  have hu₂ : u ∈ B₂.rootGroup β := by
    change u ∈ rootGroupPoints B₂.i β
    rw [hβ, rootGroupPoints_eq_of_torusIso σ hσ]
    exact hu
  apply AffineMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  apply WithTop.coe_injective
  simp only [affineFunctionalTransport_apply, e.symm_apply_apply]
  rw [B₁.coe_reflectionFunctional_apply hu h1, B₂.coe_reflectionFunctional_apply hu₂ h1,
    hβ, val_apply_of_family_comparison B₁ B₂ σ e hfamily]

/-- AS1 transfers for every actual ordered opposite factor pair. -/
theorem hasRootReflections_of_comparison
    (hact : ∀ (n : normalizerPoints B₁.i) (x : B₁.Apartment),
      e (B₁.normalizerAction n x) =
        B₂.normalizerAction (normalizerEquivOfTorusIso B₁ B₂ σ hσ n) (e x))
    (hB : B₁.HasRootReflections) : B₂.HasRootReflections := by
  intro β u hu h1 p hp y hy
  let hs : B₁.i ≫ (Iso.refl G).hom =
      CommGroupScheme.groupHom σ.hom ≫ B₂.i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  obtain ⟨α, rfl⟩ := (relativeRootsTransportEquiv σ (Iso.refl G) hs).surjective β
  have hu₁ : u ∈ B₁.rootGroup α := by
    change u ∈ rootGroupPoints B₁.i α
    have hu' : u ∈ rootGroupPoints B₂.i (characterLattice.congr σ α) := hu
    rwa [rootGroupPoints_eq_of_torusIso σ hσ] at hu'
  have hp₁ := (isOppositeFactorPair_torusIso_iff B₁ B₂ σ hσ α u p).1 hp
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ B₁.reflectionHyperplane α u := by
    change x.val α u = 0
    change (e x).val (characterLattice.congr σ α) u = 0 at hy
    rwa [val_apply_of_family_comparison B₁ B₂ σ e hfamily] at hy
  have hfix := hB α u hu₁ h1 p hp₁ x hx
  have hn : normalizerEquivOfTorusIso B₁ B₂ σ hσ (B₁.reflectionElement hp₁) =
      B₂.reflectionElement hp := by
    apply Subtype.ext
    rfl
  have h := hact (B₁.reflectionElement hp₁) x
  rw [hn, B₁.normalizerAction_apply, B₂.normalizerAction_apply, hfix] at h
  exact h.symm

end Langlands.Geometry.Building.ValuationBuildingData
