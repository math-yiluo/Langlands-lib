import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Iterate
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Good
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.FinitePropagation
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorAssociativity
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # From pointwise twist killing to the section-killing interface -/

noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory hiding tensorObj
open BraidedCategory
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

lemma epi_cohomology_map {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (T : X.Modules ⥤ X.Modules) [T.PreservesZeroMorphisms]
    (hT : ∀ (S : ShortComplex X.Modules), S.ShortExact → (S.map T).ShortExact)
    {M M' : X.Modules} (φ : M ⟶ M') (i : ℕ)
    (hK : IsZero ((DerivedSections.relativeCohomology f (i + 1)).obj
      (T.obj (kernel φ))))
    (hC : IsZero ((DerivedSections.relativeCohomology f i).obj
      (T.obj (cokernel φ)))) :
    Epi ((DerivedSections.relativeCohomology f i).map (T.map φ)) := by
  let p := Abelian.factorThruImage φ
  let j := Abelian.image.ι φ
  have eK : kernel φ ≅ kernel p :=
    (kernelIsoOfEq (Abelian.image.fac φ)).symm ≪≫ kernelCompMono p j
  have eC : cokernel φ ≅ cokernel j :=
    (cokernelIsoOfEq (Abelian.image.fac φ)).symm ≪≫ cokernelEpiComp p j
  let S₁ := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let S₂ := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel j) }
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  have hp : Epi ((DerivedSections.relativeCohomology f i).map (T.map p)) := by
    exact (Langlands.Cohomology.DerivedPlus.rightDerived_exact₃
      (DerivedSections.relativeGlobalSections f) (hT S₁ hS₁) i (i + 1) rfl).epi_f
        ((hK.of_iso ((DerivedSections.relativeCohomology f (i + 1)).mapIso
          (T.mapIso eK.symm))).eq_of_tgt _ _)
  have hj : Epi ((DerivedSections.relativeCohomology f i).map (T.map j)) := by
    exact (Langlands.Cohomology.DerivedPlus.rightDerived_exact₂
      (DerivedSections.relativeGlobalSections f) (hT S₂ hS₂) i).epi_f
        ((hC.of_iso ((DerivedSections.relativeCohomology f i).mapIso
          (T.mapIso eC.symm))).eq_of_tgt _ _)
  rw [← Abelian.image.fac φ, T.map_comp, Functor.map_comp]
  infer_instance

section Monoidal
variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

/-- Move the last factor past the middle factor. -/
def moveLastIso (A B N : C) : (A ⊗ B) ⊗ N ≅ (A ⊗ N) ⊗ B :=
  (α_ A B N) ≪≫ tensorIso (Iso.refl A) (β_ B N) ≪≫ (α_ A N B).symm

lemma insert_moveLast (A B N : C) (s : 𝟙_ C ⟶ N) :
    ((ρ_ (A ⊗ B)).inv ≫ (𝟙 (A ⊗ B) ⊗ₘ s)) ≫ (moveLastIso A B N).hom =
      ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ s)) ⊗ₘ 𝟙 B := by
  have hα := associator_naturality (𝟙 A) (𝟙 B) s
  simp only [tensorHom_id, id_whiskerRight] at hα
  have hβ := braiding_naturality (𝟙 B) s
  have hα' := associator_inv_naturality (𝟙 A) s (𝟙 B)
  have hβ' : (𝟙 A ⊗ₘ (𝟙 B ⊗ₘ s)) ≫ (𝟙 A ⊗ₘ (β_ B N).hom) =
      (𝟙 A ⊗ₘ (β_ B (𝟙_ C)).hom) ≫ (𝟙 A ⊗ₘ (s ⊗ₘ 𝟙 B)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hβ]
  have hu : (ρ_ (A ⊗ B)).inv ≫ (α_ A B (𝟙_ C)).hom ≫
      (𝟙 A ⊗ₘ (β_ B (𝟙_ C)).hom) ≫ (α_ A (𝟙_ C) B).inv =
        (ρ_ A).inv ⊗ₘ 𝟙 B := by
    rw [braiding_tensorUnit_right]
    monoidal
  dsimp [moveLastIso]
  simp only [Category.assoc]
  rw [reassoc_of% hα]
  rw [reassoc_of% hβ', hα']
  rw [reassoc_of% hu]
  rw [tensorHom_comp_tensorHom, Category.id_comp]

omit [BraidedCategory C] in
lemma insert_naturality {A A' N : C} (g : A ⟶ A') (s : 𝟙_ C ⟶ N) :
    ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ s)) ≫ (g ⊗ₘ 𝟙 N) =
      g ≫ (ρ_ A').inv ≫ (𝟙 A' ⊗ₘ s) := by
  rw [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [reassoc_of% rightUnitor_inv_naturality]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp]

end Monoidal

lemma twistMul_monoidal (N : X.Modules) (s : GlobalSections N) (A : X.Modules) :
    twistMul N s A ≫ (localizedTensorIso X A N).inv =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ sectionHom N s) := by
  unfold twistMul
  rw [Category.assoc, localizedTensorIso_inv_naturality]
  have hu : (tensorRightUnitor A).inv ≫
      (localizedTensorIso X A (structureSheaf X)).inv = (ρ_ A).inv := by
    apply (cancel_mono (ρ_ A).hom).1
    rw [Category.assoc, ← tensorMonoidalRightUnitorComparison X A]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
    rw [tensorMonoidalRightUnitorComparison, Iso.inv_hom_id]
  rw [← Category.assoc, hu]

/-- The comparison isomorphism moving a last explicit tensor factor to the middle. -/
def explicitMoveLast (A B N : X.Modules) :
    tensorObj (tensorObj A B) N ≅ tensorObj (tensorObj A N) B :=
  (localizedTensorIso X (tensorObj A B) N).symm ≪≫
    MonoidalCategory.tensorIso (localizedTensorIso X A B).symm (Iso.refl N) ≪≫
      moveLastIso A B N ≪≫
        MonoidalCategory.tensorIso (localizedTensorIso X A N) (Iso.refl B) ≪≫
          localizedTensorIso X (tensorObj A N) B

lemma twistMul_explicitMoveLast (A B N : X.Modules) (s : GlobalSections N) :
    twistMul N s (tensorObj A B) ≫ (explicitMoveLast A B N).hom =
      tensorMap (twistMul N s A) (𝟙 B) := by
  simp only [explicitMoveLast, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom]
  rw [← Category.assoc (twistMul N s (tensorObj A B)), twistMul_monoidal]
  simp only [Category.assoc]
  erw [reassoc_of% insert_naturality]
  erw [reassoc_of% insert_moveLast]
  have hA : (ρ_ A).inv ≫ (𝟙 A ⊗ₘ sectionHom N s) ≫
      (localizedTensorIso X A N).hom = twistMul N s A := by
    erw [← Category.assoc, ← twistMul_monoidal, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  erw [← Category.assoc (((ρ_ A).inv ≫ (𝟙 A ⊗ₘ sectionHom N s)) ⊗ₘ 𝟙 B),
    tensorHom_comp_tensorHom, Category.id_comp, Category.assoc (ρ_ A).inv, hA]
  rw [localizedTensorIso_hom_naturality, Iso.inv_hom_id_assoc]

section SequenceComparison

variable (N : X.Modules) (s : GlobalSections N)
  (A : ℕ → X.Modules) (φ : ∀ k, A k ⟶ A (k + 1))
  (ψ : ∀ k, tensorObj (A k) N ⟶ A (k + 1))

/-- Comparison from iterated right twists to a given sequence. -/
def sequenceLift : ∀ k, (twistIter N k).obj (A 0) ⟶ A k
  | 0 => 𝟙 _
  | k + 1 => tensorMap (sequenceLift k) (𝟙 N) ≫ ψ k

lemma twistPow_sequenceLift
    (hψ : ∀ k, twistMul N s (A k) ≫ ψ k = φ k) (k : ℕ) :
    (twistPow N s k).app (A 0) ≫ sequenceLift N A ψ k =
      (Functor.ofSequence φ).map (homOfLE (Nat.zero_le k)) := by
  induction k with
  | zero =>
      change (𝟙 (A 0) ≫ 𝟙 (A 0)) = 𝟙 (A 0)
      exact Category.id_comp _
  | succ k ih =>
      have hF : (Functor.ofSequence φ).map (homOfLE (Nat.zero_le (k + 1))) =
          (Functor.ofSequence φ).map (homOfLE (Nat.zero_le k)) ≫ φ k := by
        rw [← Functor.ofSequence_map_homOfLE_succ φ k, ← Functor.map_comp]
        rfl
      rw [twistPow_succ_app, sequenceLift, Category.assoc]
      change (twistPow N s k).app (A 0) ≫
        twistMul N s ((twistIter N k).obj (A 0)) ≫
          tensorMap (sequenceLift N A ψ k) (𝟙 N) ≫ ψ k = _
      rw [reassoc_of% twistMul_naturality, hψ, ← Category.assoc, ih, hF]

end SequenceComparison

section Ray

variable (G N P : X.Modules) (s : GlobalSections N) (m : ℕ)

/-- The ray of coefficients in the section-killing interface. -/
def rayObj (k : ℕ) : X.Modules :=
  tensorObj (tensorObj G (tensorPow N (m + k))) P

/-- Multiplication on the original coefficient, followed by reassociation. -/
def rayStep (k : ℕ) : rayObj G N P m k ⟶ rayObj G N P m (k + 1) :=
  tensorMap (tensorMap (twistMul N s G) (𝟙 (tensorPow N (m + k)))) (𝟙 P) ≫
    tensorMap (tensorAssociator G N (tensorPow N (m + k))).hom (𝟙 P)

/-- Move a newly appended factor through the two fixed twists. -/
def rayAppend (k : ℕ) : tensorObj (rayObj G N P m k) N ⟶
    rayObj G N P m (k + 1) :=
  (explicitMoveLast (tensorObj G (tensorPow N (m + k))) P N).hom ≫
    tensorMap ((explicitMoveLast G (tensorPow N (m + k)) N).hom ≫
      (tensorAssociator G N (tensorPow N (m + k))).hom) (𝟙 P)

lemma twistMul_rayAppend (k : ℕ) :
    twistMul N s (rayObj G N P m k) ≫ rayAppend G N P m k =
      rayStep G N P s m k := by
  unfold rayAppend rayStep rayObj
  rw [← Category.assoc, twistMul_explicitMoveLast]
  simp only [tensorMap_comp, Category.id_comp]
  rw [← Category.assoc, twistMul_explicitMoveLast]

lemma epi_cohomology_rayStep {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K))
    (hN : IsLocallyFreeRankOne N) (hP : IsLocallyFreeRankOne P) (i k : ℕ)
    (hK : IsZero ((DerivedSections.relativeCohomology f (i + 1)).obj
      (tensorObj (tensorObj (kernel (twistMul N s G)) (tensorPow N (m + k))) P)))
    (hC : IsZero ((DerivedSections.relativeCohomology f i).obj
      (tensorObj (tensorObj (cokernel (twistMul N s G)) (tensorPow N (m + k))) P))) :
    Epi ((DerivedSections.relativeCohomology f i).map (rayStep G N P s m k)) := by
  let T := tensorBy (tensorPow N (m + k)) ⋙ tensorBy P
  have hT : ∀ S : ShortComplex X.Modules, S.ShortExact → (S.map T).ShortExact := by
    intro S hS
    exact shortExact_tensorBy (S.map (tensorBy (tensorPow N (m + k))))
      (shortExact_tensorBy S hS _ (rankOne_pow N hN (m + k))) P hP
  have := epi_cohomology_map f T hT (twistMul N s G) i hK hC
  change Epi ((DerivedSections.relativeCohomology f i).map
    (T.map (twistMul N s G) ≫
      ((tensorBy P).mapIso (tensorAssociator G N (tensorPow N (m + k)))).hom))
  rw [Functor.map_comp]
  infer_instance

end Ray

/-- Pointwise killing by section powers implies the published section-killing interface. -/
theorem sectionKilling_of_twistKilling (h : TwistKillingStatement.{u}) :
    SectionKillingStatement.{u} := by
  intro K _ X f hf N hN s hs P hP G hG hGf m i hi hK hC
  let : IsProper f := hf
  let : G.IsQuasicoherent := hG
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  let A := rayObj G N P m
  let φ := rayStep G N P s m
  let ψ := rayAppend G N P m
  let H := DerivedSections.relativeCohomology f (p + 1)
  let F := Functor.ofSequence φ ⋙ H
  let := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
    G (tensorPow N (m + 0)) (rankOne_pow N hN (m + 0))
  let : (A 0).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
      (tensorObj G (tensorPow N (m + 0))) P hP
  have hAf : HasFiniteAffineSections (A 0) :=
    (hGf.tensor_lineBundle (rankOne_pow N hN (m + 0))).tensor_lineBundle hP
  let : Module.Finite K (F.obj 0) :=
    (DerivedSections.hasFiniteCohomology_of_coherent f (A 0) hAf).1 (p + 1)
  apply SerrePropagation.finiteModule_surjective_sequence_eventually_isZero F
  · intro k
    change Function.Surjective
      (H.map ((Functor.ofSequence φ).map (homOfLE (Nat.le_succ k)))).hom
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (ModuleCat.epi_iff_surjective _).1
      (epi_cohomology_rayStep G N P s m f hN hP (p + 1) k (hK k) (hC k))
  · intro ξ
    obtain ⟨k, hk⟩ := h K X f hf N hN s hs (A 0) inferInstance p ξ
    refine ⟨k, ?_⟩
    have hc := twistPow_sequenceLift N s A φ ψ
      (twistMul_rayAppend G N P s m) k
    change (H.map ((Functor.ofSequence φ).map (homOfLE (Nat.zero_le k)))).hom ξ = 0
    rw [← hc, Functor.map_comp]
    change (H.map (sequenceLift N A ψ k)).hom
      ((H.map ((twistPow N s k).app (A 0))).hom ξ) = 0
    rw [hk, map_zero]


end Langlands.AlgebraicGeometry.Modules.SerreVanishing
