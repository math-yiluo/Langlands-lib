import Langlands.ClassField.Global.TensorUnitCochains
import Langlands.GroupScheme.CentralIsogeny.GaloisLiftScalarExtension
import Langlands.GroupScheme.ComponentFieldEmbeddings
import Langlands.GroupScheme.Rational.CentralMuCocycleLift
import Langlands.GroupScheme.Rational.NumberFieldWeilCocycleTransfer
import Langlands.GroupScheme.Rational.WeilUnitDiagonalCharacter

/-! # The tensor-unit obstruction of a central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pullback to a number field preserves triviality on the entire cover at each place. -/
theorem Cocycle.LocallyTrivial.numberFieldBaseChange {F B : Type u}
    [Field F] [NumberField F] [Field B] [NumberField B] [Algebra F B]
    {H : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}
    {ξ : Cocycle H U} (h : ξ.LocallyTrivial) :
    (ξ.baseChangePullback (Spec.algebraMap F B)).LocallyTrivial := by
  intro w
  let v := Global.restrictPlace F B w
  let b := Spec.algebraMap F B
  let c := Spec.algebraMap B (Global.placeCompletion B w)
  let d := Spec.algebraMap F (Global.placeCompletion F v)
  let e := Spec.map (CommRingCat.ofHom (Global.placeCompletionExtension F B w))
  have hsq : c ≫ b = e ≫ d := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun j : F →+* Global.placeCompletion B w => Spec.map (CommRingCat.ofHom j))
    ext x
    exact (Global.placeCompletionExtension_algebraMap F B w x).symm
  exact Cocycle.isTrivial_baseChangePullback_twice b c d e hsq ξ (h v)

namespace IsCentralIsogeny

open Langlands.ClassField.Global Langlands.ClassFieldTheory.Local
open TensorUnitShapiro

variable {F B L : Type u} [Field F] [Field B] [Field L]
  [Algebra F B] [Algebra F L] [FiniteDimensional F B]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

local notation "W" => WeilGm.groupScheme (CommRingCat.of F) B
local notation "b" => Spec.algebraMap F B

/-- A homomorphism from the kernel to a Weil group gives a tensor unit on each point. -/
def kernelTensorUnitMap (q : kernel f ⟶ W) (R : Type u) [CommRing R] [Algebra F R] :
    GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R) →* (B ⊗[F] R)ˣ :=
  (WeilGm.affineUnitsEquiv (CommRingCat.of F) B (CommAlgCat.of F R)).toMonoidHom.comp
    (GroupScheme.affinePointsTarget (kernel f) q (CommAlgCat.of F R))

/-- Central tensor-unit coordinates commute with every coefficient algebra map. -/
theorem kernelTensorUnitMap_naturality (q : kernel f ⟶ W)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (j : R →ₐ[F] S) (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R)) :
    kernelTensorUnitMap q S (GroupScheme.affinePointMap (kernel f) (CommAlgCat.ofHom j) x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B j).toMonoidHom
        (kernelTensorUnitMap q R x) := by
  change WeilGm.affineUnitsEquiv (CommRingCat.of F) B (CommAlgCat.of F S)
    (((algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom j).op ≫ x) ≫ q.hom.hom) = _
  rw [Category.assoc, WeilGm.affineUnitsEquiv_naturality]
  rfl

/-- The central defect expressed as units of the original tensor algebra. -/
def kernelTensorDefect (q : kernel f ⟶ W)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    Gal(L/F) × Gal(L/F) → (B ⊗[F] L)ˣ := fun p => kernelTensorUnitMap q L (d.defect p)

private def kernelTensorDefectCocycle (q : kernel f ⟶ W)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    cocycles₂ (tensorUnitRepresentation F B L) := by
  refine ⟨fun p => Additive.ofMul (hf.kernelTensorDefect q d p), (mem_cocycles₂_iff _).mpr ?_⟩
  intro σ τ υ
  have h := congrArg (kernelTensorUnitMap q L) (hf.galoisLift_isMulCocycle₂ ξ d σ τ υ)
  have ha : kernelTensorUnitMap q L (σ • d.defect (τ, υ)) =
      tensorAction F B L σ (kernelTensorUnitMap q L (d.defect (τ, υ))) :=
    kernelTensorUnitMap_naturality q σ.toAlgHom _
  rw [map_mul, map_mul, ha] at h
  exact congrArg Additive.ofMul h

/-- The relative degree-two class of the central tensor-unit defect. -/
def kernelTensorObstruction (q : kernel f ⟶ W)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    groupCohomology (tensorUnitRepresentation F B L) 2 :=
  H2π _ (hf.kernelTensorDefectCocycle q d)

/-- Vanishing in tensor-unit cohomology gives an actual tensor-unit primitive. -/
theorem exists_tensorPrimitive_of_obstruction_eq_zero (q : kernel f ⟶ W)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)
    (h : hf.kernelTensorObstruction q d = 0) :
    ∃ a : Gal(L/F) → (B ⊗[F] L)ˣ, ∀ σ τ, tensorDifferential a σ τ = hf.kernelTensorDefect q d (σ, τ) := by
  obtain ⟨a, ha⟩ := (H2π_eq_zero_iff (hf.kernelTensorDefectCocycle q d)).mp h
  refine ⟨fun σ => (a σ).toMul, fun σ τ => ?_⟩
  have hστ := congrArg (fun v => (v (σ, τ)).toMul) ha
  rw [d₁₂_hom_apply] at hστ
  exact hστ

/-- Over the coefficient base the Weil inclusion yields a character of the actual kernel. -/
def kernelWeilCharacter (q : kernel f ⟶ W) :
    kernel ((GroupScheme.baseChange b).map f) ⟶ (Gm (Spec (CommRingCat.of B))).toGrp :=
  (kernelBaseChangeIso b f).inv ≫ (GroupScheme.baseChange b).map q ≫
    WeilGm.diagonalCharacter (CommRingCat.of F) (CommRingCat.of B)

variable [Algebra B L] [IsScalarTower F B L]

private theorem kernelWeilCharacter_points (q : kernel f ⟶ W)
    (x : GaloisCocycle.cover B L ⟶ (kernel ((GroupScheme.baseChange b).map f)).X) :
    (hf.baseChange b).kernelUnitMap (kernelWeilCharacter q) L x =
      Units.map (WeilGm.evaluationCoefficient F B L).toMonoidHom
        (kernelTensorUnitMap q L (scalarExtensionKernelPointsEquiv (f := f) x)) := by
  change Gm.affineUnitsEquiv (CommRingCat.of B) (CommAlgCat.of B L)
    (x ≫ (kernelWeilCharacter q).hom.hom) = _
  simp only [kernelWeilCharacter, Grp.comp_hom_hom, ← Category.assoc]
  rw [WeilGm.diagonalCharacter_affine, GaloisCocycle.scalarExtensionPointsEquiv_comp]
  rfl

variable [Algebra.IsSeparable F B] [Normal F L]

private theorem evaluationCoefficient_eq_embedding (x : (B ⊗[F] L)ˣ) :
    Units.map (WeilGm.evaluationCoefficient F B L).toMonoidHom x =
      unitEmbeddingEquiv F B L x (IsScalarTower.toAlgHom F B L) := by
  apply Units.ext
  change WeilGm.evaluationCoefficient F B L (x : B ⊗[F] L) =
    tensorEmbeddingEquiv F B L (x : B ⊗[F] L) (IsScalarTower.toAlgHom F B L)
  generalize (x : B ⊗[F] L) = t
  induction t using TensorProduct.inductionOn with
  | tmul y z => simp [mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable [FiniteDimensional F L]

/-- Under Shapiro the relative tensor-unit defect is precisely the defect evaluated by the
inclusion character on the compatible scalar-extended cover. -/
theorem kernelTensorObstruction_shapiro (q : kernel f ⟶ W)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    (cohomologyIso F B L 2).hom (hf.kernelTensorObstruction q d) =
      (hf.baseChange b).kernelUnitObstruction (kernelWeilCharacter q)
        (hf.scalarExtensionGaloisLift (K := B) (M := L) d) := by
  rw [cohomologyIso_hom, kernelTensorObstruction, H2π_comp_map_apply]
  unfold kernelUnitObstruction relativeUnitsClass₂
  apply congrArg (H2π (unitsRepresentation B L)).hom
  apply Subtype.ext
  funext p
  obtain ⟨σ, τ⟩ := p
  change Additive.ofMul (unitEmbeddingEquiv F B L
    (hf.kernelTensorDefect q d (σ.restrictScalars F, τ.restrictScalars F))
    (IsScalarTower.toAlgHom F B L)) = Additive.ofMul
      ((hf.baseChange b).kernelUnitMap (kernelWeilCharacter q) L
        ((hf.scalarExtensionGaloisLift (K := B) (M := L) d).defect (σ, τ)))
  apply congrArg Additive.ofMul
  rw [← evaluationCoefficient_eq_embedding, hf.kernelWeilCharacter_points,
    hf.scalarExtensionGaloisLift_defect, GaloisPoint.relativeExtend_self, MonoidHom.id_apply]
  have he (s : L ≃ₐ[B] L) : (s.restrictScalars F).restrictNormal L = s.restrictScalars F := by
    ext x
    exact (s.restrictScalars F).restrictNormal_commutes L x
  rw [he, he]
  rfl

/-- Local triviality kills the actual central defect in tensor-unit cohomology. -/
theorem kernelTensorObstruction_eq_zero [NumberField F] [NumberField B] [NumberField L] [IsGalois F L]
    (q : kernel f ⟶ W) {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)
    (h : ξ.LocallyTrivial) : hf.kernelTensorObstruction q d = 0 := by
  let : IsGalois B L := IsGalois.tower_top_of_isGalois F B L
  let : FiniteDimensional B L := FiniteDimensional.right F B L
  have h' : (GaloisCocycle.scalarExtension (K := B) (M := L) ξ).LocallyTrivial :=
    h.numberFieldBaseChange.refine GaloisCocycle.pullbackCoverPoint
  apply (ConcreteCategory.bijective_of_isIso (cohomologyIso F B L 2).hom).injective
  rw [map_zero, hf.kernelTensorObstruction_shapiro]
  exact (hf.baseChange b).kernelUnitObstruction_eq_zero (kernelWeilCharacter q) _ h'

end IsCentralIsogeny
end Langlands.GroupScheme
