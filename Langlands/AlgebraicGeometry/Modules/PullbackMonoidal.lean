import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Invertibility of the fixed canonical comparison, with no preservation hypothesis. -/
instance pullbackTensorComparison_isIso : IsIso (pullbackTensorComparison f) :=
  pullbackTensorComparisonIsIso f

instance pullbackTensorComparisonApp_isIso (M N : Y.Modules) :
    IsIso (pullbackTensorComparisonApp f M N) :=
  inferInstanceAs (IsIso ((pullbackTensorComparison f).app (M, N)))

/-- The canonical comparison isomorphism for the explicitly sheafified tensor. -/
def pullbackTensorIso (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  asIso (pullbackTensorComparisonApp f M N)

instance localizedPullbackTensorComparisonApp_isIso (M N : Y.Modules) :
    IsIso (localizedPullbackTensorComparisonApp f M N) := by
  rw [localizedPullbackTensorComparisonApp_eq]
  infer_instance

/-- The canonical comparison isomorphism for the localized monoidal tensor. -/
def localizedPullbackTensorIso (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ≅
      (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N :=
  asIso (localizedPullbackTensorComparisonApp f M N)

/-- Transfer of the proved explicit left-unit law to the localized tensor. -/
lemma localizedPullbackTensorLeftUnitor (M : Y.Modules) :
    localizedPullbackTensorComparisonApp f (𝟙_ Y.Modules) M ≫
        (pullbackUnitIso f).hom ▷ (Scheme.Modules.pullback f).obj M ≫
        (λ_ ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (λ_ M).hom := by
  have hn := localizedTensorIso_hom_naturality (X := X)
    (M := (Scheme.Modules.pullback f).obj (structureSheaf Y)) (M' := structureSheaf X)
    (N := (Scheme.Modules.pullback f).obj M) (N' := (Scheme.Modules.pullback f).obj M)
    (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M))
  rw [← tensorHom_id]
  change localizedPullbackTensorComparisonApp f (structureSheaf Y) M ≫
    ((pullbackUnitIso f).hom ⊗ₘ 𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
      (λ_ ((Scheme.Modules.pullback f).obj M)).hom = _
  rw [localizedPullbackTensorComparisonApp_eq,
    ← tensorMonoidalLeftUnitorComparison X ((Scheme.Modules.pullback f).obj M)]
  simp only [Category.assoc]
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc,
    pullbackTensorLeftUnitor X Y f M, ← CategoryTheory.Functor.map_comp,
    tensorMonoidalLeftUnitorComparison]

/-- Transfer of the proved explicit right-unit law to the localized tensor. -/
lemma localizedPullbackTensorRightUnitor (M : Y.Modules) :
    localizedPullbackTensorComparisonApp f M (𝟙_ Y.Modules) ≫
        (Scheme.Modules.pullback f).obj M ◁ (pullbackUnitIso f).hom ≫
        (ρ_ ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (ρ_ M).hom := by
  have hn := localizedTensorIso_hom_naturality (X := X)
    (M := (Scheme.Modules.pullback f).obj M) (M' := (Scheme.Modules.pullback f).obj M)
    (N := (Scheme.Modules.pullback f).obj (structureSheaf Y)) (N' := structureSheaf X)
    (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackUnitIso f).hom
  rw [← id_tensorHom]
  change localizedPullbackTensorComparisonApp f M (structureSheaf Y) ≫
    (𝟙 ((Scheme.Modules.pullback f).obj M) ⊗ₘ (pullbackUnitIso f).hom) ≫
      (ρ_ ((Scheme.Modules.pullback f).obj M)).hom = _
  rw [localizedPullbackTensorComparisonApp_eq,
    ← tensorMonoidalRightUnitorComparison X ((Scheme.Modules.pullback f).obj M)]
  simp only [Category.assoc]
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc, pullbackTensorRightUnitor X Y f M,
    ← CategoryTheory.Functor.map_comp, tensorMonoidalRightUnitorComparison]

/-- Transfer of the proved explicit symmetry law to the localized tensor. -/
lemma localizedPullbackTensorSymmetry (M N : Y.Modules) :
    localizedPullbackTensorComparisonApp f M N ≫
        (β_ ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).hom =
      (Scheme.Modules.pullback f).map (β_ M N).hom ≫
        localizedPullbackTensorComparisonApp f N M := by
  apply (cancel_mono (localizedTensorIso X ((Scheme.Modules.pullback f).obj N)
    ((Scheme.Modules.pullback f).obj M)).hom).1
  simp only [localizedPullbackTensorComparisonApp_eq, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← tensorMonoidalSymmetryComparison X]
  simp only [Iso.inv_hom_id_assoc]
  rw [pullbackTensorSymmetry X Y f M N, ← CategoryTheory.Functor.map_comp_assoc,
    tensorMonoidalSymmetryComparison, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Oplax pullback with exactly the published canonical tensor and unit maps. -/
@[instance_reducible]
def pullbackOplaxMonoidal : (Scheme.Modules.pullback f).OplaxMonoidal where
  η := (pullbackUnitIso f).hom
  δ := localizedPullbackTensorComparisonApp f
  δ_natural_left {M M'} a N := by
    have h := (localizedPullbackTensorComparison f).naturality
      ((a, 𝟙 N) : (M, N) ⟶ (M', N))
    change (Scheme.Modules.pullback f).map (a ⊗ₘ 𝟙 N) ≫
      localizedPullbackTensorComparisonApp f M' N =
        localizedPullbackTensorComparisonApp f M N ≫
          ((Scheme.Modules.pullback f).map a ⊗ₘ (Scheme.Modules.pullback f).map (𝟙 N)) at h
    simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using h.symm
  δ_natural_right {N N'} M a := by
    have h := (localizedPullbackTensorComparison f).naturality
      ((𝟙 M, a) : (M, N) ⟶ (M, N'))
    change (Scheme.Modules.pullback f).map (𝟙 M ⊗ₘ a) ≫
      localizedPullbackTensorComparisonApp f M N' =
        localizedPullbackTensorComparisonApp f M N ≫
          ((Scheme.Modules.pullback f).map (𝟙 M) ⊗ₘ (Scheme.Modules.pullback f).map a) at h
    simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using h.symm
  oplax_associativity := localizedPullbackTensorAssociativity X Y f
  oplax_left_unitality M := by
    apply (cancel_mono (λ_ ((Scheme.Modules.pullback f).obj M)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [localizedPullbackTensorLeftUnitor, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  oplax_right_unitality M := by
    apply (cancel_mono (ρ_ ((Scheme.Modules.pullback f).obj M)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [localizedPullbackTensorRightUnitor, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Strong monoidal pullback obtained by inverting its fixed oplax comparisons. -/
instance pullbackMonoidal : (Scheme.Modules.pullback f).Monoidal := by
  letI := pullbackOplaxMonoidal f
  haveI : IsIso (CategoryTheory.Functor.OplaxMonoidal.η (Scheme.Modules.pullback f)) := by
    change IsIso (pullbackUnitIso f).hom
    infer_instance
  haveI (M N : Y.Modules) :
      IsIso (CategoryTheory.Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N) := by
    change IsIso (localizedPullbackTensorComparisonApp f M N)
    infer_instance
  exact CategoryTheory.Functor.Monoidal.ofOplaxMonoidal (Scheme.Modules.pullback f)

@[simp] lemma pullbackMonoidal_η :
    CategoryTheory.Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) = (pullbackUnitIso f).hom := by
  rfl

@[simp] lemma pullbackMonoidal_δ (M N : Y.Modules) :
    CategoryTheory.Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N =
      localizedPullbackTensorComparisonApp f M N := by
  rfl

@[simp] lemma pullbackMonoidal_ε :
    CategoryTheory.Functor.LaxMonoidal.ε (Scheme.Modules.pullback f) = (pullbackUnitIso f).inv := by
  change inv (pullbackUnitIso f).hom = (pullbackUnitIso f).inv
  apply IsIso.inv_eq_of_hom_inv_id
  exact (pullbackUnitIso f).hom_inv_id

@[simp] lemma pullbackMonoidal_μ (M N : Y.Modules) :
    CategoryTheory.Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) M N =
      (localizedPullbackTensorIso f M N).inv := by
  rfl

/-- Pullback preserves the symmetry of the module-sheaf tensor product. -/
instance pullbackBraided : (Scheme.Modules.pullback f).Braided where
  toMonoidal := pullbackMonoidal f
  braided M N := by
    apply (cancel_epi (localizedPullbackTensorComparisonApp f M N)).1
    simp only [← pullbackMonoidal_δ, CategoryTheory.Functor.Monoidal.δ_μ_assoc]
    rw [pullbackMonoidal_δ, reassoc_of% localizedPullbackTensorSymmetry,
      ← pullbackMonoidal_δ]
    simp only [CategoryTheory.Functor.Monoidal.δ_μ, Category.comp_id]

end Langlands.Scheme.Modules
