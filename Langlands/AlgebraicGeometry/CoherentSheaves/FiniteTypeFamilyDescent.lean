import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsNoetherianReduction
import Langlands.AlgebraicGeometry.NoetherianApproximation.FlatnessSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentProof

/-! # Descent of actual coherent families to finite-type affine bases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.CoherentSheaves.FamilyDescent

open Langlands.AlgebraicGeometry.NoetherianApproximation
open Langlands.AlgebraicGeometry.Modules.NoetherianReduction

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- A flat finitely presented module on any Cartesian model of the relative space
of a test gives an actual family over that test. -/
def familyOfModel {B : Over S} {Y₀ : Scheme.{u}} {p₀ : Y₀ ⟶ B.left} {a₀ : Y₀ ⟶ X}
    (h : IsPullback p₀ a₀ B.hom f) (M₀ : Y₀.Modules) [M₀.IsFinitePresentation]
    (hflat : Modules.IsFlatOver p₀ M₀) : FamilyGroupoid f B :=
  haveI := Modules.isFinitePresentation_pullback h.isoPullback.inv M₀
  FamilyGroupoid.ofModule f B ((Scheme.Modules.pullback h.isoPullback.inv).obj M₀)
    (Modules.isFlatOver_pullback_of_isPullback
      (IsPullback.of_horiz_isIso ⟨by simp⟩ :
        IsPullback h.isoPullback.inv (pullback.fst B.hom f) p₀ (𝟙 _)) M₀ hflat)

/-- The underlying module of the family of a model. -/
lemma familyOfModel_obj {B : Over S} {Y₀ : Scheme.{u}} {p₀ : Y₀ ⟶ B.left} {a₀ : Y₀ ⟶ X}
    (h : IsPullback p₀ a₀ B.hom f) (M₀ : Y₀.Modules) [M₀.IsFinitePresentation]
    (hflat : Modules.IsFlatOver p₀ M₀) :
    (familyOfModel f h M₀ hflat).of.obj =
      (Scheme.Modules.pullback h.isoPullback.inv).obj M₀ := rfl

variable {k : Type u} [CommRing k] [IsNoetherianRing k]
  (g : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact g] [IsSeparated g] [LocallyOfFiniteType g]

/-- Every actual family over an affine test descends to an affine test of finite
type over the noetherian base ring, through an algebra map to the test ring. -/
theorem exists_finiteType_model {A : Type u} [CommRing A] [Algebra k A]
    (M : FamilyGroupoid g (Picard.affineBase k A)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : Algebra.FiniteType k B)
      (φ : B →ₐ[k] A) (M₀ : FamilyGroupoid g (Picard.affineBase k B)),
      Nonempty ((FamilyGroupoid.pullback g (Picard.affineBaseMap φ)).obj M₀ ≅ M) := by
  let ιA := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hpb : IsPullback (pullback.snd ιA g) (pullback.fst ιA g) g ιA :=
    (IsPullback.of_hasPullback ιA g).flip
  -- Descend finite presentation to a finitely generated subalgebra `T₄`.
  obtain ⟨T₄, hT₄, -, M₄, hM₄, hc⟩ :=
    finitePresentationModuleSubalgebraDescent g (pullback.snd ιA g) (pullback.fst ιA g) hpb
      M.of.obj M.of.property.1 (∅ : Finset A)
  have : IsNoetherianRing T₄ := Modules.NoetherianReduction.isNoetherianRing_of_fg hT₄
  have : Algebra.FiniteType k T₄ := (Subalgebra.fg_iff_finiteType T₄).mp hT₄
  obtain ⟨a₄, ha₄fst, ha₄snd, h₄⟩ := exists_isPullback_subalgebra hpb T₄
  obtain ⟨eM⟩ := hc a₄ ha₄fst ha₄snd
  let ι₄ := Spec.map (CommRingCat.ofHom (algebraMap k T₄))
  let q := pullback.snd g ι₄
  -- Descend relative flatness to a finitely generated `T₄`-subalgebra `T₅`.
  obtain ⟨T₅, hT₅, -, hfl⟩ := isFlatOverSubalgebraDescent q M₄ hM₄ a₄ (pullback.fst ιA g) h₄
    ((Modules.isFlatOver_iff_of_iso _ eM).mpr M.of.property.2) (∅ : Finset A)
  let : Algebra k T₅ := ((algebraMap T₄ T₅).comp (algebraMap k T₄)).toAlgebra
  have : IsScalarTower k T₄ T₅ := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.FiniteType T₄ T₅ := (Subalgebra.fg_iff_finiteType T₅).mp hT₅
  have : Algebra.FiniteType k T₅ := Algebra.FiniteType.trans (S := T₄) inferInstance inferInstance
  let φ : T₅ →ₐ[k] A :=
    { toRingHom := algebraMap T₅ A
      commutes' := fun r ↦ rfl }
  let ι₄₅ := Spec.map (CommRingCat.ofHom (algebraMap T₄ T₅))
  let fst₅ := pullback.fst q ι₄₅
  let p₅ := pullback.snd q ι₄₅
  have hcomp : ι₄₅ ≫ ι₄ = (Picard.affineBase k T₅).hom := by
    simp only [ι₄₅, ι₄, Picard.affineBase, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  have hbig : IsPullback p₅ (fst₅ ≫ pullback.fst g ι₄) (Picard.affineBase k T₅).hom g := by
    have h := (IsPullback.of_hasPullback q ι₄₅).paste_horiz (IsPullback.of_hasPullback g ι₄)
    rw [← hcomp]
    exact h.flip
  have := hM₄
  have hfp₅ : ((Scheme.Modules.pullback fst₅).obj M₄).IsFinitePresentation :=
    Modules.isFinitePresentation_pullback fst₅ M₄
  have hfl₅ : Modules.IsFlatOver p₅ ((Scheme.Modules.pullback fst₅).obj M₄) :=
    hfl fst₅ p₅ (IsPullback.of_hasPullback q ι₄₅)
  let M₀ : FamilyGroupoid g (Picard.affineBase k T₅) :=
    @familyOfModel _ _ g (Picard.affineBase k T₅) _ p₅ _ hbig
      ((Scheme.Modules.pullback fst₅).obj M₄) hfp₅ hfl₅
  have hmap : (Picard.relativeSpace g).map (Picard.affineBaseMap φ) ≫
      (hbig.isoPullback.inv ≫ fst₅) = a₄ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ha₄fst]
      have h1 : hbig.isoPullback.inv ≫ fst₅ ≫ pullback.fst g ι₄ =
          pullback.snd (Picard.affineBase k T₅).hom g :=
        hbig.isoPullback_inv_snd
      rw [h1]
      exact Picard.relativeSpace_map_snd g (Picard.affineBaseMap φ)
    · rw [Category.assoc, Category.assoc, ha₄snd]
      have h1 : fst₅ ≫ q = p₅ ≫ ι₄₅ := pullback.condition
      have h2 : hbig.isoPullback.inv ≫ p₅ = pullback.fst (Picard.affineBase k T₅).hom g :=
        hbig.isoPullback_inv_fst
      have h3 : (Picard.relativeSpace g).map (Picard.affineBaseMap φ) ≫
          pullback.fst (Picard.affineBase k T₅).hom g =
            pullback.fst ιA g ≫ (Picard.affineBaseMap φ).left :=
        (Picard.relativeProjection g).naturality (Picard.affineBaseMap φ)
      have h4 : (Picard.affineBaseMap φ).left ≫ ι₄₅ =
          Spec.map (CommRingCat.ofHom (algebraMap T₄ A)) := by
        simp only [Picard.affineBaseMap, Over.homMk_left, ι₄₅, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp]
        rfl
      rw [h1, ← Category.assoc hbig.isoPullback.inv, h2, ← Category.assoc, h3,
        Category.assoc, h4]
  refine ⟨T₅, inferInstance, inferInstance, inferInstance, φ, M₀,
    ⟨Core.isoMk (ObjectProperty.isoMk _ ?_)⟩⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app M₄ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact hmap)).app M₄ ≪≫ eM

end Langlands.AlgebraicGeometry.CoherentSheaves.FamilyDescent
