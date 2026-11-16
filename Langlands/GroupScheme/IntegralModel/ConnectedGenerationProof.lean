import Langlands.GroupScheme.IntegralModel.ConnectedGenerationField
import Langlands.GroupScheme.IntegralModel.CongruenceLifting
import Langlands.GroupScheme.IntegralModel.GreenbergPointModel
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.RelativeIdentityComponentDvrAffinenessProof
import Langlands.GroupScheme.RelativeIdentityComponentProperties
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationFieldProof
import Langlands.GroupScheme.IntegralModel.CongruenceLiftingProof
import Langlands.GroupScheme.IntegralModel.GreenbergPointModelProof

/-! # Proof of KP Lemma A.4.26 -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ConnectedGeneration

/-- Precomposing with a surjective homomorphism does not change the range. -/
theorem range_comp_of_surjective {A B C : Type*} [Group A] [Group B] [Group C]
    (φ : B →* C) (ψ : A →* B) (hψ : Function.Surjective ψ) :
    (φ.comp ψ).range = φ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective ψ hψ,
    ← MonoidHom.range_eq_map]

end ConnectedGeneration

open ConnectedGeneration in
/-- KP Lemma A.4.26 follows from its field step, Henselian lifting at every
congruence level and Greenberg models of congruence-level points. -/
theorem connectedGeneration_of_prerequisites
    (hF : ConnectedGenerationFieldStatement.{u})
    (hH : IntegralModel.HenselianCongruenceLiftingStatement.{u})
    (hG : IntegralModel.GreenbergPointModelStatement.{u}) :
    ConnectedGenerationStatement.{u} := by
  intro R _ _ _ _ _ X _ hX n Y _ hY hYc f hfin hm N i hi
  obtain ⟨m, hker⟩ := hm
  have : ∀ j, GeometricallyConnected (Y j).X.hom := hYc
  have := hfin
  have : Smooth X.X.hom := hX
  obtain ⟨G, eX, hGa, hGs, hfun⟩ := hG R m X hX
  have := hGa
  choose GY eY g hGYa hGYs hcomm hconn using fun j => hfun (Y j) (hY j) (f j)
  have : ∀ j, IsAffineHom (GY j).X.hom := hGYa
  have : ∀ j, GeometricallyConnected (GY j).X.hom := fun j => hconn j (hYc j)
  -- The reduced generated subgroup corresponds to the field generated subgroup.
  have hmap : ((generatedImages f).map
      (baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) X)).map
        eX.toMonoidHom = generatedImages g := by
    simp only [generatedImages, Subgroup.map_iSup, MonoidHom.map_range]
    refine iSup_congr fun j => ?_
    have hcomp : eX.toMonoidHom.comp
        ((baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) X).comp
          (rationalPoints.map (f j))) =
        (rationalPoints.map (g j)).comp ((eY j).toMonoidHom.comp
          (baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) (Y j))) := by
      refine MonoidHom.ext fun y => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← hcomm j]
      exact congrArg eX (baseChangeSectionHom_naturality _ (f j) y)
    rw [hcomp, range_comp_of_surjective]
    exact (eY j).surjective.comp (hH R (Y j) (hY j) m)
  -- Finite index transfers to the field generated subgroup.
  have hsurjX := hH R X hX m
  have hfinG : (generatedImages g).FiniteIndex := by
    rw [← hmap, Subgroup.map_map]
    exact Subgroup.FiniteIndex.map_of_surjective _ (eX.surjective.comp hsurjX)
  -- The field step identifies it with the identity component of `G`.
  obtain ⟨G0, i0, hi0, -, -⟩ := RelativeIdentityComponent.smoothExistence _ G hGs
  have hFG := hF (IsLocalRing.ResidueField R) G hGs n GY hGYs
    (fun j => hconn j (hYc j)) g hfinG G0 i0 hi0
  -- The relative identity component of `X` is smooth, affine and connected.
  have hNa : IsAffineHom N.X.hom :=
    RelativeIdentityComponent.smoothDvrAffineness R X hX ‹_› N i hi
  have := hNa
  obtain ⟨H, j, hj, -, hHc⟩ := RelativeIdentityComponent.smoothExistence _ X hX
  have := hHc
  have hNc : GeometricallyConnected N.X.hom := hi.geometricallyConnected hj
  have hNs : Smooth N.X.hom := by
    have := hi.isOpenImmersion
    have e := Over.w i.hom.hom
    rw [← e]
    infer_instance
  obtain ⟨GN, eN, gN, -, -, hNcomm, hNconn⟩ := hfun N hNs i
  have := hNconn hNc
  have hle : (rationalPoints.map gN).range ≤ (rationalPoints.map i0).range :=
    le_trans (le_iSup (fun _ : PUnit.{1} => (rationalPoints.map gN).range) PUnit.unit)
      (generatedImages_le_componentRange (I := PUnit.{1}) (fun _ => gN) i0 hi0)
  -- Reduction of the component lands in the reduction of the generated subgroup.
  have hredle : ((rationalPoints.map i).range).map
        (baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) X) ≤
      (generatedImages f).map
        (baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) X) := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    have h1 : eX (baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) X
        (rationalPoints.map i y)) ∈ generatedImages g := by
      rw [hFG]
      apply hle
      refine ⟨eN (baseChangeSectionHom (IntegralModel.congruenceBaseMap R m) N y), ?_⟩
      rw [← hNcomm]
      exact congrArg eX (baseChangeSectionHom_naturality _ i y).symm
    rw [← hmap] at h1
    obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp h1
    rw [← eX.injective hweq]
    exact hw
  exact eq_componentRange_of_reduction f i hi m hker hredle

/-- KP Lemma A.4.26 from Greenberg point models alone, using the published
proofs of the field step and of Henselian lifting at every congruence level. -/
theorem connectedGeneration_of_greenbergPointModel
    (hG : IntegralModel.GreenbergPointModelStatement.{u}) :
    ConnectedGenerationStatement.{u} :=
  connectedGeneration_of_prerequisites connectedGenerationField
    IntegralModel.henselianCongruenceLifting hG

/-- **KP Lemma A.4.26.** Over a Henselian DVR with algebraically closed residue
field, finitely many smooth affine geometrically connected groups whose images
generate a finite-index subgroup of `X(R)` containing a positive congruence
kernel generate exactly the integral points of the relative identity component. -/
theorem connectedGeneration : ConnectedGenerationStatement.{u} :=
  connectedGeneration_of_greenbergPointModel IntegralModel.greenbergPointModel

end Langlands.GroupScheme
