import Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationStatement
import Langlands.AbelianScheme.AmpleGenericTranslationVanishingStatement
import Langlands.AbelianScheme.AmpleGenericTangentVanishingStatement
import Langlands.AbelianScheme.AmpleNonvanishingSection
import Langlands.AbelianScheme.SquareSectionInvariance
import Langlands.AbelianScheme.FieldTheoremOfTheSquareProof
import Langlands.AbelianScheme.MultiplicationIsogenyProof
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # The cube of an ample line bundle separates points and tangents, from the two generic
invariance statements

Mumford's §17 uses triples of translates with parameters summing to zero. In the
adaptation here, two equal translation parameters allow the first two factors to be
replaced by an arbitrary section of `L ⊗ L`. Over an algebraically closed field, a failure
of `L³` to separate distinct rational points `x₀, x₁` or a nonzero tangent at `x₀`
then gives a generic vanishing implication for the complete system of `L ⊗ L`,
respectively under translation by `x₀⁻¹ x₁` or along the invariant tangent field.
The conditional argument uses
`AmpleGenericTranslationVanishingStatement` and `AmpleGenericTangentVanishingStatement`
to exclude these. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.GroupScheme Langlands.GroupScheme.SeparatingLineBundle

section Generic

variable {K : Type u} [Field K] (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X]

/-- The morphism `y ↦ c * y⁻²` of a commutative group scheme over `K`. -/
def squareInvTranslate (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) : G.X ⟶ G.X :=
  (GroupScheme.multiplication G (-2)).hom.hom ≫ translation G c

/-- On rational points, `squareInvTranslate G c` is `y ↦ c * y⁻²`. -/
lemma comp_squareInvTranslate (c y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    y ≫ squareInvTranslate G c = c * y ^ (-2 : ℤ) := by
  rw [squareInvTranslate, ← Category.assoc, GroupScheme.points_multiplication, comp_translation]

omit [IsCommMonObj G.X] in
/-- A rational point lies in the preimage of the nonvanishing locus of `s` under `f` exactly
when `s` does not vanish at its image. -/
lemma mem_preimage_trivializationOpen_iff (L : LineBundle G.X.left) (s : GlobalSections L.obj)
    (f : G.X ⟶ G.X) (y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    y.left (IsLocalRing.closedPoint K) ∈ f.left ⁻¹ᵁ trivializationOpen L.obj s ↔
      ¬ VanishesAlong L (y ≫ f).left s := by
  rw [vanishesAlong_field_iff L _ s (IsLocalRing.closedPoint K), not_not, Over.comp_left,
    Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]
  exact Iff.rfl

omit [IsCommMonObj G.X] in
/-- The preimage of the nonvanishing locus of `s` under a surjective endomorphism is
nonempty when `s` is nonzero at some rational point. -/
lemma preimage_trivializationOpen_nonempty (L : LineBundle G.X.left) (s : GlobalSections L.obj)
    (hs : ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, ¬ VanishesAlong L y.left s)
    (f : G.X ⟶ G.X) [Surjective f.left] :
    ((f.left ⁻¹ᵁ trivializationOpen L.obj s : G.X.left.Opens) : Set G.X.left).Nonempty := by
  obtain ⟨y, hy⟩ := hs
  rw [vanishesAlong_field_iff L _ s (IsLocalRing.closedPoint K), not_not] at hy
  obtain ⟨w, hw⟩ := f.left.surjective (y.left (IsLocalRing.closedPoint K))
  refine ⟨w, ?_⟩
  change w ∈ f.left ⁻¹ᵁ trivializationOpen L.obj s
  rw [Scheme.Hom.mem_preimage, hw]
  exact hy

/-- Translation by a rational point is an isomorphism of the underlying scheme. -/
instance isIso_translation_left (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    IsIso (translation G c).left :=
  ⟨⟨(translation G c⁻¹).left, by
      rw [left_translation_comp, inv_mul_cancel, translation_one, Over.id_left],
    by rw [left_translation_comp, mul_inv_cancel, translation_one, Over.id_left]⟩⟩

variable [Smooth G.X.hom] [IsProper G.X.hom] [GeometricallyConnected G.X.hom]

/-- `y ↦ c * y⁻²` is surjective on a smooth proper geometrically connected commutative
group scheme. -/
instance surjective_squareInvTranslate (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    Surjective (squareInvTranslate G c).left := by
  have h1 : Surjective (GroupScheme.multiplication G (-2)).hom.hom.left := by
    obtain ⟨-, -, h⟩ := multiplicationIsogeny _ G inferInstance inferInstance inferInstance
      (-2) (by norm_num)
    exact h
  rw [squareInvTranslate, Over.comp_left]
  infer_instance

end Generic

/-- The cube `(L ⊗ L) ⊗ L` of the Library's triple-translate construction is the tensor
power `tensorPow L 3 = L ⊗ (L ⊗ (L ⊗ 𝒪))`. -/
def cubeLBTensorPowIso {X : Scheme.{u}} (L : LineBundle X) :
    tensorObj (tensorObj L.obj L.obj) L.obj ≅ tensorPow L.obj 3 :=
  tensorAssociator L.obj L.obj L.obj ≪≫
    tensorMapIso (Iso.refl _) (tensorMapIso (Iso.refl _) (tensorPowOneIso L.obj).symm)

/-- The cube of an ample line bundle on an abelian variety over an algebraically closed
field separates rational points and tangent vectors, assuming the two generic invariance
statements. -/
theorem algClosedFieldAmpleCubeSeparation_of_generic
    (hpt : AmpleGenericTranslationVanishingStatement.{u})
    (htan : AmpleGenericTangentVanishingStatement.{u}) :
    AlgClosedFieldAmpleCubeSeparationStatement.{u} := by
  intro K _ _ A L hL
  let G : Grp (Over (Spec (CommRingCat.of K))) := A.toGrp
  have : IsCommMonObj G.X := inferInstanceAs (IsCommMonObj A.X)
  have : Smooth G.X.hom := inferInstanceAs (Smooth A.X.hom)
  have : IsProper G.X.hom := inferInstanceAs (IsProper A.X.hom)
  have : GeometricallyConnected G.X.hom := inferInstanceAs (GeometricallyConnected A.X.hom)
  have : IrreducibleSpace G.X.left := irreducibleSpace_of_smooth_of_isProper G
  have hsq : SquareFor G L := fun a b ↦
    fieldTheoremOfTheSquare K G inferInstance inferInstance inferInstance L a b
  obtain ⟨s, z, hz, hsz⟩ := exists_section_not_vanishesAlong_of_isAmple A L hL
  have hs : ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, ¬ VanishesAlong L y.left s :=
    ⟨Over.homMk z hz, hsz⟩
  have hN : (squareLB G L).IsAmple := ampleTensor _ L L (squareLB G L) ⟨Iso.refl _⟩ hL hL
  have hNbpf : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      ∃ σ : GlobalSections (squareLB G L).obj, ¬ VanishesAlong (squareLB G L) y.left σ :=
    exists_squareSection_not_vanishesAlong G L hsq s hs
  suffices hcube : SeparatesPointsAndTangents A.X.hom (cubeLB G L) from
    hcube.of_iso (cubeLBTensorPowIso L)
  refine ⟨fun x hx ↦ ?_, fun x y hx hy hxy ↦ ?_, fun x hx t ht ↦ ?_⟩
  · -- base-point freeness
    exact exists_cubeSection_not_vanishesAlong G L hsq s hs (Over.homMk x hx)
  · -- separation of rational points
    by_contra hcon
    push Not at hcon
    let x₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X := Over.homMk x hx
    let x₁ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X := Over.homMk y hy
    have hsep : ∀ σ : GlobalSections (cubeLB G L).obj,
        VanishesAlong (cubeLB G L) x₀.left σ → VanishesAlong (cubeLB G L) x₁.left σ :=
      fun σ hσ ↦ hcon σ hσ
    let f := squareInvTranslate G (x₀ * x₀ * x₁)
    have h1 := hpt K A (squareLB G L) hN hNbpf (x₀⁻¹ * x₁) (f.left ⁻¹ᵁ trivializationOpen L.obj s)
      (preimage_trivializationOpen_nonempty G L s hs f) (fun y' hy' σ hσ ↦ by
        rw [mem_preimage_trivializationOpen_iff, comp_squareInvTranslate] at hy'
        have hy'' : ¬ VanishesAlong L ((y' * x₀⁻¹ * (y' * x₀⁻¹))⁻¹ * x₁).left s := by
          convert hy' using 3
          simp only [zpow_neg, zpow_two, mul_inv_rev, inv_inv, mul_comm, mul_assoc,
            mul_left_comm]
        have h0 : VanishesAlong (squareLB G L) ((y' * x₀⁻¹) * x₀).left σ := by
          rwa [inv_mul_cancel_right]
        have h2 := vanishesAlong_square_of_not_separates s hsq x₀ x₁ hsep (y' * x₀⁻¹) hy'' σ h0
        convert h2 using 2
        simp only [mul_comm, mul_assoc])
    apply hxy
    have h3 : x₀ = x₁ := by
      rw [inv_mul_eq_one] at h1
      exact h1
    exact congrArg (fun p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X ↦ p.left) h3
  · -- separation of tangent vectors
    by_contra hcon
    push Not at hcon
    let x₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X := Over.homMk x hx
    have ht₀ : IsNonzeroTangentVectorAt G.X.hom x₀.left t := ht
    have hsep : ∀ σ : GlobalSections (cubeLB G L).obj,
        VanishesAlong (cubeLB G L) x₀.left σ → VanishesAlong (cubeLB G L) t σ :=
      fun σ hσ ↦ hcon σ hσ
    let f := squareInvTranslate G (x₀ * x₀ * x₀)
    refine htan K A (squareLB G L) hN hNbpf (t ≫ (translation G x₀⁻¹).left)
      (isNonzeroTangentVectorAt_translate x₀ ht₀) (f.left ⁻¹ᵁ trivializationOpen L.obj s)
      (preimage_trivializationOpen_nonempty G L s hs f) (fun y' hy' σ hσ ↦ ?_)
    rw [mem_preimage_trivializationOpen_iff, comp_squareInvTranslate] at hy'
    have hy'' : ¬ VanishesAlong L ((y' * x₀⁻¹ * (y' * x₀⁻¹))⁻¹ * x₀).left s := by
      convert hy' using 3
      simp only [zpow_neg, zpow_two, mul_inv_rev, inv_inv, mul_comm, mul_assoc, mul_left_comm]
    have h0 : VanishesAlong (squareLB G L) ((y' * x₀⁻¹) * x₀).left σ := by
      rwa [inv_mul_cancel_right]
    have h2 := vanishesAlong_square_translate_tangent_of_not_separates s hsq x₀ ht₀.1 hsep
      (y' * x₀⁻¹) hy'' σ h0
    change VanishesAlong (squareLB G L) ((t ≫ (translation G x₀⁻¹).left) ≫
      (translation G y').left) σ
    rwa [Category.assoc, left_translation_comp]

end Langlands.AbelianScheme
