import Langlands.AlgebraicGeometry.StrictBirationalGroupLaw
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.StrictLaw
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Restriction to the full domain of multiplication in an open subscheme

The restricted representative has as its domain all pairs in the original domain whose two
factors and product lie in the open subscheme. A strictness witness supplies the required six
fibrewise densities by inclusion.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S X : Scheme.{u}} {f : X ⟶ S} (m : BirationalGroupLaw f) (V : X.Opens)

local notation "g" => (V.ι ≫ f)

/-- The inclusion of the square of the open subscheme in the original square. -/
private def squareInclusion (f : X ⟶ S) (V : X.Opens) :
    pullback (V.ι ≫ f) (V.ι ≫ f) ⟶ pullback f f :=
  pullback.map (V.ι ≫ f) (V.ι ≫ f) f f V.ι V.ι (𝟙 S)
    (Category.comp_id _) (Category.comp_id _)

private instance : IsOpenImmersion (squareInclusion f V) := by
  unfold squareInclusion
  infer_instance

private theorem squareInclusion_fst : squareInclusion f V ≫ pullback.fst f f =
    pullback.fst g g ≫ V.ι := by simp [squareInclusion]

private theorem squareInclusion_snd : squareInclusion f V ≫ pullback.snd f f =
    pullback.snd g g ≫ V.ι := by simp [squareInclusion]

private theorem squareInclusion_range : Set.range (squareInclusion f V) =
    pullback.fst f f ⁻¹' (V : Set X) ∩ pullback.snd f f ⁻¹' (V : Set X) := by
  unfold squareInclusion
  rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι]

/-- The open of the original domain where both inputs and the product lie in `V`. -/
private def restrictionOpen : m.domain.toScheme.Opens :=
  ((m.domain.ι ≫ pullback.fst f f) ⁻¹ᵁ V ⊓ (m.domain.ι ≫ pullback.snd f f) ⁻¹ᵁ V) ⊓
    m.mul ⁻¹ᵁ V

/-- The inclusion of this open in the square of `V`. -/
private def restrictedPair : (restrictionOpen m V).toScheme ⟶ pullback g g :=
  IsOpenImmersion.lift (squareInclusion f V) ((restrictionOpen m V).ι ≫ m.domain.ι) (by
    rw [squareInclusion_range]
    rintro _ ⟨a, rfl⟩
    exact a.2.1)

@[reassoc]
private theorem restrictedPair_comp : restrictedPair m V ≫ squareInclusion f V =
    (restrictionOpen m V).ι ≫ m.domain.ι := IsOpenImmersion.lift_fac _ _ _

private instance : IsOpenImmersion (restrictedPair m V) := by
  have : IsOpenImmersion (restrictedPair m V ≫ squareInclusion f V) := by
    rw [restrictedPair_comp]
    infer_instance
  exact IsOpenImmersion.of_comp (restrictedPair m V) (squareInclusion f V)

private abbrev restrictedDomain : (pullback g g).Opens := (restrictedPair m V).opensRange

private def toOriginal : (restrictedDomain m V).toScheme ⟶ m.domain.toScheme :=
  (restrictedPair m V).isoOpensRange.inv ≫ (restrictionOpen m V).ι

@[reassoc]
private theorem restrictedDomain_comp : (restrictedDomain m V).ι ≫ squareInclusion f V =
    toOriginal m V ≫ m.domain.ι := by
  rw [toOriginal, Category.assoc, ← restrictedPair_comp,
    Scheme.Hom.isoOpensRange_inv_comp_assoc]

@[reassoc]
private theorem restrictedDomain_fst : (restrictedDomain m V).ι ≫ pullback.fst g g ≫ V.ι =
    toOriginal m V ≫ m.domain.ι ≫ pullback.fst f f := by
  rw [← squareInclusion_fst, restrictedDomain_comp_assoc]

@[reassoc]
private theorem restrictedDomain_snd : (restrictedDomain m V).ι ≫ pullback.snd g g ≫ V.ι =
    toOriginal m V ≫ m.domain.ι ≫ pullback.snd f f := by
  rw [← squareInclusion_snd, restrictedDomain_comp_assoc]

private theorem range_toOriginal : Set.range (toOriginal m V) = restrictionOpen m V := by
  have hsurj : Function.Surjective (restrictedPair m V).isoOpensRange.inv :=
    (Scheme.homeoOfIso (restrictedPair m V).isoOpensRange.symm).surjective
  rw [toOriginal, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
    Set.image_univ, Scheme.Opens.range_ι]

private def restrictedMul : (restrictedDomain m V).toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (toOriginal m V ≫ m.mul) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    have ha : toOriginal m V a ∈ restrictionOpen m V := by
      change toOriginal m V a ∈ (restrictionOpen m V : Set _)
      rw [← range_toOriginal]
      exact ⟨a, rfl⟩
    exact ha.2)

@[reassoc]
private theorem restrictedMul_ι : restrictedMul m V ≫ V.ι = toOriginal m V ≫ m.mul :=
  IsOpenImmersion.lift_fac _ _ _

private theorem restrictedMul_comp : restrictedMul m V ≫ g =
    (restrictedDomain m V).ι ≫ pullback.fst g g ≫ g := by
  simp only [restrictedMul_ι_assoc, restrictedDomain_fst_assoc, m.mul_comp]

private theorem restrictedLeft_comp :
    leftTranslation g (restrictedDomain m V) (restrictedMul m V) (restrictedMul_comp m V) ≫
      squareInclusion f V = toOriginal m V ≫ leftT m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, squareInclusion_fst, leftTranslation, pullback.lift_fst_assoc,
      pullback.lift_fst, restrictedDomain_fst]
  · simp only [Category.assoc, squareInclusion_snd, leftTranslation, pullback.lift_snd_assoc,
      pullback.lift_snd, restrictedMul_ι]

private theorem restrictedRight_comp :
    rightTranslation g (restrictedDomain m V) (restrictedMul m V) (restrictedMul_comp m V) ≫
      squareInclusion f V = toOriginal m V ≫ rightT m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, squareInclusion_fst, rightTranslation, pullback.lift_fst_assoc,
      pullback.lift_fst, restrictedMul_ι]
  · simp only [Category.assoc, squareInclusion_snd, rightTranslation, pullback.lift_snd_assoc,
      pullback.lift_snd, restrictedDomain_snd]

private instance : IsOpenImmersion (toOriginal m V) := by
  unfold toOriginal
  infer_instance

private theorem transfer_density {q : pullback f f ⟶ X} {r : pullback g g ⟶ V.toScheme}
    (hr : squareInclusion f V ≫ q = r ≫ V.ι) {W : Set ↥(pullback f f)}
    {B : Set ↥(pullback g g)} (h : SquareFibreGenerizationDense f q V W)
    (hW : W ⊆ squareInclusion f V '' B) : FibreGenerizationDense r B := by
  intro p
  have hp : squareInclusion f V p ∈ Set.range (squareInclusion f V) := ⟨p, rfl⟩
  rw [squareInclusion_range] at hp
  obtain ⟨_, hw, hq, hspec⟩ := h (squareInclusion f V p) hp.1 hp.2
  obtain ⟨p', hp', rfl⟩ := hW hw
  refine ⟨p', hp', V.ι.isOpenEmbedding.injective ?_,
    (squareInclusion f V).isOpenEmbedding.toIsEmbedding.specializes_iff.mp hspec⟩
  simpa only [← Scheme.Hom.comp_apply, hr] using hq

private theorem image_subset_restricted {U : (pullback f f).Opens}
    (hU : m.domain.ι ⁻¹ᵁ U ≤ restrictionOpen m V)
    {old : m.domain.toScheme ⟶ pullback f f}
    {new : (restrictedDomain m V).toScheme ⟶ pullback g g}
    (hn : new ≫ squareInclusion f V = toOriginal m V ≫ old) :
    old '' (m.domain.ι ⁻¹ᵁ U : m.domain.toScheme.Opens) ⊆
      squareInclusion f V '' Set.range new := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ : a ∈ Set.range (toOriginal m V) := by
    rw [range_toOriginal]
    exact hU ha
  refine ⟨new b, ⟨b, rfl⟩, ?_⟩
  rw [← Scheme.Hom.comp_apply, hn, Scheme.Hom.comp_apply, hb]

/-- Strictness passes to the full restricted domain. Every original product whose two inputs and
output lie in `V` factors through that domain, including on arbitrary scheme-valued points. -/
theorem exists_strictRestriction (h : m.IsStrictOn V) :
    ∃ n : BirationalGroupLaw g, IsStrictDomain n ∧
      ∀ {T : Scheme.{u}} (a : T ⟶ m.domain.toScheme) (x y z : T ⟶ V.toScheme),
        a ≫ m.domain.ι ≫ pullback.fst f f = x ≫ V.ι →
        a ≫ m.domain.ι ≫ pullback.snd f f = y ≫ V.ι → a ≫ m.mul = z ≫ V.ι →
        ∃ b : T ⟶ n.domain.toScheme,
          b ≫ n.domain.ι ≫ pullback.fst g g = x ∧
          b ≫ n.domain.ι ≫ pullback.snd g g = y ∧ b ≫ n.mul = z := by
  obtain ⟨U, hUm, hUfst, hUsnd, hUmul, hDf, hDs, hLf, hLs, hRf, hRs⟩ := h
  have hU : m.domain.ι ⁻¹ᵁ U ≤ restrictionOpen m V := fun _ ha =>
    ⟨⟨hUfst ha, hUsnd ha⟩, hUmul ha⟩
  have hUD := image_subset_restricted m V hU (restrictedDomain_comp m V)
  rw [Scheme.Opens.range_ι] at hUD
  have hD : (U : Set ↥(pullback f f)) ⊆ squareInclusion f V ''
      (restrictedDomain m V : Set ↥(pullback g g)) := fun p hp =>
    hUD ⟨(⟨p, hUm hp⟩ : m.domain.toScheme), hp, rfl⟩
  have hL := image_subset_restricted m V hU (restrictedLeft_comp m V)
  have hR := image_subset_restricted m V hU (restrictedRight_comp m V)
  have domain_fst := transfer_density V (squareInclusion_fst (f := f) V) hDf hD
  have left_fst := transfer_density V (squareInclusion_fst (f := f) V) hLf hL
  have right_fst := transfer_density V (squareInclusion_fst (f := f) V) hRf hR
  have overBase {B : Set ↥(pullback g g)} (hB : FibreGenerizationDense (pullback.fst g g) B) :
      FibreGenerizationDense (pullback.fst g g ≫ g) B := by
    intro p
    obtain ⟨p', hp', heq, hspec⟩ := hB p
    exact ⟨p', hp', congrArg (fun y : V.toScheme => g y) heq, hspec⟩
  let n : BirationalGroupLaw g :=
    { domain := restrictedDomain m V
      mul := restrictedMul m V
      mul_comp := restrictedMul_comp m V
      domain_dense := overBase domain_fst
      isOpenImmersion_leftTranslation := by
        have : IsOpenImmersion (leftTranslation g (restrictedDomain m V) (restrictedMul m V)
            (restrictedMul_comp m V) ≫ squareInclusion f V) := by
          rw [restrictedLeft_comp]
          infer_instance
        exact IsOpenImmersion.of_comp _ (squareInclusion f V)
      leftTranslation_dense := overBase left_fst
      isOpenImmersion_rightTranslation := by
        have : IsOpenImmersion (rightTranslation g (restrictedDomain m V) (restrictedMul m V)
            (restrictedMul_comp m V) ≫ squareInclusion f V) := by
          rw [restrictedRight_comp]
          infer_instance
        exact IsOpenImmersion.of_comp _ (squareInclusion f V)
      rightTranslation_dense := overBase right_fst
      assoc := by
        intro T a b c d h₁ h₂ h₃ h₄ h₅
        rw [← cancel_mono V.ι]
        simp only [Category.assoc, restrictedMul_ι]
        rw [← Category.assoc b, ← Category.assoc d]
        apply m.assoc T (a ≫ toOriginal m V) (b ≫ toOriginal m V) (c ≫ toOriginal m V)
          (d ≫ toOriginal m V)
        · simpa only [Category.assoc, restrictedDomain_fst, restrictedDomain_snd] using
            (reassoc_of% h₁) V.ι
        · simpa only [Category.assoc, restrictedDomain_fst, restrictedMul_ι] using
            (reassoc_of% h₂) V.ι
        · simpa only [Category.assoc, restrictedDomain_snd] using (reassoc_of% h₃) V.ι
        · simpa only [Category.assoc, restrictedDomain_fst] using (reassoc_of% h₄) V.ι
        · simpa only [Category.assoc, restrictedDomain_snd, restrictedMul_ι] using
            (reassoc_of% h₅) V.ι }
  refine ⟨n, ⟨domain_fst, transfer_density V (squareInclusion_snd V) hDs hD,
    left_fst, transfer_density V (squareInclusion_snd V) hLs hL,
    right_fst, transfer_density V (squareInclusion_snd V) hRs hR⟩, ?_⟩
  intro T a x y z hx hy hz
  have ha : Set.range a ⊆ Set.range (restrictionOpen m V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (m.domain.ι ≫ pullback.fst f f) (a p) ∈ V
      rw [← Scheme.Hom.comp_apply, hx, Scheme.Hom.comp_apply]
      exact (x p).2
    · change (m.domain.ι ≫ pullback.snd f f) (a p) ∈ V
      rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
      exact (y p).2
    · change m.mul (a p) ∈ V
      rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]
      exact (z p).2
  let b : T ⟶ n.domain.toScheme := IsOpenImmersion.lift (restrictionOpen m V).ι a ha ≫
    (restrictedPair m V).isoOpensRange.hom
  have hb : b ≫ toOriginal m V = a := by simp [b, toOriginal]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [← cancel_mono V.ι]
    simp only [n, Category.assoc, restrictedDomain_fst]
    rw [← Category.assoc b, hb, hx]
  · rw [← cancel_mono V.ι]
    simp only [n, Category.assoc, restrictedDomain_snd]
    rw [← Category.assoc b, hb, hy]
  · rw [← cancel_mono V.ι]
    simp only [n, Category.assoc, restrictedMul_ι]
    rw [← Category.assoc b, hb, hz]

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
