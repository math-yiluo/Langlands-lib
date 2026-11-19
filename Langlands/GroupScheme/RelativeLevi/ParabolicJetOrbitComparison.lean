import Langlands.GroupScheme.RelativeLevi.ParabolicJetLiftComparison
import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientJetPositivity
import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetConjugateKernel
import Langlands.GroupScheme.HomogeneousCharacterLineBundle
import Langlands.RingTheory.Grassmannian.FaithfulKernelComparison

/-! # The actual stabilized quotient parabolic jet kernel -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open AffineCoordinates Corepresented IdentityJet TorusSubgroupModuli SubgroupFunctor
open SelfNormalizingAmbient HomogeneousQuotientFromEmbedding
open Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant
open Langlands.Scheme.Modules

private theorem affinePoint_comp_orbitHom
    {R : CommRingCat.{u}} {F : CommAlgCat R ⥤ GrpCat.{u}} {B : CommAlgCat R}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) {m : ℕ} {K : Ideal B}
    (hK : augIdeal e ^ m ≤ K) {C : Type u} [AddCommGroup C] [Module R C]
    {k : ℕ} (eW : ((B ⧸ K) × C) ≃ₗ[R] (Fin k → R))
    (E : Module.Grassmannian.ProjectiveEmbedding.Rep R ((B ⧸ augIdeal e ^ m) × C) k)
    {A : CommAlgCat R} (x : (algSpec R).obj (op A) ⟶ (groupScheme F e).X) :
    x ≫ orbitHom e hK eW E.pt B (e.homEquiv (𝟙 B)) =
      orbitHom e hK eW E.pt A (affinePointsEquiv F e A x) := by
  let φ := (algSpec.fullyFaithful.preimage x).unop
  have hx : (algSpec R).map φ.op = x := algSpec.fullyFaithful.map_preimage x
  have hp : F.map φ (e.homEquiv (𝟙 B)) = affinePointsEquiv F e A x := by
    change F.map φ (e.homEquiv (𝟙 B)) = e.homEquiv φ
    have hh := e.homEquiv_comp φ (𝟙 B)
    change e.homEquiv (𝟙 B ≫ φ) = F.map φ (e.homEquiv (𝟙 B)) at hh
    rw [Category.id_comp] at hh
    exact hh.symm
  rw [← hx, map_orbitHom hK eW E.hpt, hp, hx]

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  (hG : IsReductive G) (i : H ⟶ G) (hi : IsRelativeParabolicSubgroup i)
  (Q : HomogeneousQuotient i) (D : ProperQuotientJetData i Q)

private theorem quotient_affine : IsAffineHom Q.projection.left := isAffineHom_projection i Q
attribute [local instance] quotient_affine

private theorem baseChange_affine {S T : Scheme.{u}} (K : GroupScheme S)
    [IsAffineHom K.X.hom] (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj K).X.hom := by
  change IsAffineHom (Limits.pullback.snd K.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
attribute [local instance] baseChange_affine

/-- The actual affine inverse image of an affine quotient open in the original group. -/
def quotientLiftOpen (U : Q.scheme.left.affineOpens) : G.X.left.affineOpens :=
  ⟨Q.projection.left ⁻¹ᵁ U, U.2.preimage Q.projection.left⟩

/-- Coefficients pulled back along the actual quotient projection. -/
def quotientLiftCoefficient (U : Q.scheme.left.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom (quotientLiftOpen i Q U)
    Γ(Q.scheme.left, U) →ₐ[R] Γ(G.X.left, quotientLiftOpen i Q U) :=
  familyCoefficientHom Q.projection U (quotientLiftOpen i Q U) le_rfl

/-- The actual universal group point as a section of the base-changed group. -/
def quotientLiftConjugator :
    Over.mk (𝟙 G.X.left) ⟶ ((GroupScheme.baseChange G.X.hom).obj G).X :=
  (baseChangeBasePointsEquiv G.X.hom G).symm (𝟙 G.X)

private theorem quotientLiftConjugator_projection :
    conjugatorProjection G G.X.hom (quotientLiftConjugator (G := G)) =
      (groupSchemeIso G).inv.hom.hom.left := by
  have hh := congrArg (fun x : Over.mk G.X.hom ⟶ G.X => x.left)
    ((baseChangeBasePointsEquiv G.X.hom G).apply_symm_apply (𝟙 G.X))
  rw [baseChangeBasePointsEquiv_left] at hh
  change (quotientLiftConjugator (G := G)).left ≫ Limits.pullback.fst G.X.hom G.X.hom = 𝟙 _ at hh
  unfold conjugatorProjection
  rw [← Category.assoc, hh]
  exact Category.id_comp _

/-- The classified quotient point pulls back to the orbit point of the actual lift. -/
theorem quotientAffinePoint_map_eq_orbitPoint (U : Q.scheme.left.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
    let V := quotientLiftOpen i Q U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom V
    Module.Grassmannian.map (quotientLiftCoefficient i Q U)
        (affineOpenPoint D.embeddingData.grassmannian D.embeddingData.embedding.left
          Q.scheme.hom (Over.w D.embeddingData.embedding) U) =
      orbitPoint (corepresentation G) le_sup_right (CommAlgCat.of R Γ(G.X.left, V))
        D.embeddingData.targetEquiv
        (affinePointsEquiv (functor G) (corepresentation G) (CommAlgCat.of R Γ(G.X.left, V))
          (parameterAffinePoint G G.X.hom (quotientLiftConjugator (G := G)) V)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
  let V := quotientLiftOpen i Q U
  let := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom V
  let E := D.embeddingData.grassmannian
  let f := D.embeddingData.embedding.left
  let x := parameterAffinePoint G G.X.hom (quotientLiftConjugator (G := G)) V
  apply (E.pt Γ(G.X.left, V)).injective
  apply Subtype.ext
  rw [E.hpt, pt_affineOpenPoint]
  have hchart : Spec.map (CommRingCat.ofHom (quotientLiftCoefficient i Q U).toRingHom) ≫
      U.2.fromSpec = V.2.fromSpec ≫ Q.projection.left := by
    change Spec.map (Q.projection.left.appLE U V le_rfl) ≫ U.2.fromSpec = _
    exact IsAffineOpen.SpecMap_appLE_fromSpec Q.projection.left U.2 V.2 le_rfl
  rw [← Category.assoc, hchart, Category.assoc]
  have hf := congrArg (fun a => a.left) D.embeddingData.fac
  have hiG : (groupSchemeIso G).inv.hom.hom.left ≫
      (groupSchemeIso G).hom.hom.hom.left = 𝟙 G.X.left :=
    congrArg (fun a : G ⟶ G => a.hom.hom.left) (groupSchemeIso G).inv_hom_id
  have hfac : Q.projection.left ≫ f = (groupSchemeIso G).inv.hom.hom.left ≫
      (orbitHom (corepresentation G) le_sup_right D.embeddingData.targetEquiv E.pt
        (algebra G) ((corepresentation G).homEquiv (𝟙 (algebra G)))).left := by
    rw [← hf]
    change _ = (groupSchemeIso G).inv.hom.hom.left ≫
      ((groupSchemeIso G).hom.hom.hom.left ≫ Q.projection.left ≫ f)
    rw [← Category.assoc (groupSchemeIso G).inv.hom.hom.left, hiG, Category.id_comp]
  rw [hfac, ← Category.assoc]
  have hx : x.left = V.2.fromSpec ≫ (groupSchemeIso G).inv.hom.hom.left := by
    change V.2.fromSpec ≫ conjugatorProjection G G.X.hom (quotientLiftConjugator (G := G)) = _
    rw [quotientLiftConjugator_projection]
  rw [← hx]
  exact congrArg (fun a => a.left)
    (affinePoint_comp_orbitHom (corepresentation G) le_sup_right
      D.embeddingData.targetEquiv E x)

/-- The actual quotient coefficient map is faithfully flat. -/
theorem quotientLiftCoefficient_faithfullyFlat (U : Q.scheme.left.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom (quotientLiftOpen i Q U)
    letI : Algebra Γ(Q.scheme.left, U) Γ(G.X.left, quotientLiftOpen i Q U) :=
      (quotientLiftCoefficient i Q U).toAlgebra
    Module.FaithfullyFlat Γ(Q.scheme.left, U) Γ(G.X.left, quotientLiftOpen i Q U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
  let := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom (quotientLiftOpen i Q U)
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  have hf := Langlands.Scheme.UnitCocycleDescent.faithfullyFlat_app Q.projection.left U.2
    (U.2.preimage Q.projection.left)
  change (Q.projection.left.appLE U (Q.projection.left ⁻¹ᵁ U) le_rfl).hom.FaithfullyFlat
  rw [Scheme.Hom.appLE_eq_app]
  exact hf

/-- Actual quotient-family tensor vanishing is exactly the lifted orbit-map vanishing. -/
theorem quotientTensor_eq_zero_iff_orbit (U : Q.scheme.left.affineOpens) :
    letI : IsAffineHom H.X.hom := hi.isAffineHom
    let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
    letI : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
    let V := quotientLiftOpen i Q U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom V
    ∀ z : Γ(Q.scheme.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (D.order + 1)),
      ambientTensorCoordinates G Q.scheme.hom r.hom D.order U z = 0 ↔
        D.conjugateOrbitMap G.X.hom (quotientLiftConjugator (G := G)) D.order V
          ((quotientLiftCoefficient i Q U).toLinearMap.rTensor _ z) = 0 := by
  let : IsAffineHom H.X.hom := hi.isAffineHom
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let := Scheme.TwoAffineOpenCover.algebraOfHom Q.scheme.hom U
  let V := quotientLiftOpen i Q U
  let := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom V
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  change ∀ z : Γ(Q.scheme.left, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (D.order + 1)),
    ambientTensorCoordinates G Q.scheme.hom r.hom D.order U z = 0 ↔
      D.conjugateOrbitMap G.X.hom (quotientLiftConjugator (G := G)) D.order V
        ((quotientLiftCoefficient i Q U).toLinearMap.rTensor _ z) = 0
  intro z
  have hclosed : IsClosedSubgroup i := relativeParabolicClosed _ G H i hG hi
  have hker := D.ker_conjugateTensorCoordinates G.X.hom (quotientLiftConjugator (G := G))
    hclosed D.order V
  have hk := SetLike.ext_iff.mp hker
    ((quotientLiftCoefficient i Q U).toLinearMap.rTensor _ z)
  change ambientTensorCoordinates G G.X.hom (conjugateFamily i (𝟙 G.X)) D.order V
      ((quotientLiftCoefficient i Q U).toLinearMap.rTensor _ z) = 0 ↔ _ at hk
  let : IsAffineHom (𝟙 G.X ≫ Q.projection).left := by
    simpa only [Category.id_comp] using (quotient_affine i Q)
  let : Flat (𝟙 G.X ≫ Q.projection).left := by
    simpa only [Category.id_comp] using (inferInstance : Flat Q.projection.left)
  let : Surjective (𝟙 G.X ≫ Q.projection).left := by
    simpa only [Category.id_comp] using Q.surjective_projection
  have hLift := quotientJet_tensor_eq_zero_iff_lift hG i hi Q (𝟙 G.X) D.order U
  simp only [Category.id_comp] at hLift
  exact (hLift z).trans hk

/-- The actual stabilized tensor kernel equals the retained Grassmannian classified kernel. -/
theorem hasStabilizedJetKernelComparison : HasStabilizedJetKernelComparison hG i hi Q D := by
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let p := Q.scheme.hom
  let C := ModuleCat.of R D.embeddingData.complement
  let M := IdentityJet.module r.group D.order
  let q := IdentityJet.ambientGlobalGenerator G p r.hom D.order
  let E := D.embeddingData.grassmannian
  let f := D.embeddingData.embedding.left
  change ∀ U : Q.scheme.left.affineOpens,
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    (stabilizedTensorMap p M q C U).ker =
      (affineOpenPoint E f p (Over.w D.embeddingData.embedding) U).toSubmodule
  intro U
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  let V := quotientLiftOpen i Q U
  let := Scheme.TwoAffineOpenCover.algebraOfHom G.X.hom V
  let φ := quotientLiftCoefficient i Q U
  rw [stabilizedTensorMap_ker]
  change Langlands.Grassmannian.productKernel (C := C)
      (globalFamilyTensorMap p M q U) = _
  rw [globalFamilyTensorMap_ambientGlobalGenerator]
  apply Langlands.Grassmannian.productKernel_eq_classified φ
    (quotientLiftCoefficient_faithfullyFlat i Q U)
    (ambientTensorCoordinates G p r.hom D.order U)
    (D.conjugateOrbitMap G.X.hom (quotientLiftConjugator (G := G)) D.order V)
  · rw [quotientAffinePoint_map_eq_orbitPoint i Q D U, orbitPoint_toSubmodule]
    rfl
  · exact quotientTensor_eq_zero_iff_orbit hG i hi Q D U

end Langlands.GroupScheme.ParabolicSubgroupModuli
