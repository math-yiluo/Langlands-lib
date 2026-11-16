import Langlands.AlgebraicGeometry.FiniteCoefficientMonomorphismStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType

/-! # Finite coefficient descent of monicity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.FiniteCoefficient

/-- Monicity descends by eventual equality of the two kernel-pair projections. -/
theorem exists_fg_mono
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Over (Spec (CommRingCat.of R))}
    [QuasiCompact X.hom] [LocallyOfFiniteType X.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y)
    [Mono ((Over.pullback (Spec.algebraMap R A)).map f).left] (s : Finset A) :
    ∃ T : Subalgebra R A, T.FG ∧ (s : Set A) ⊆ T ∧
      Mono ((Over.pullback (Spec.algebraMap R T)).map f).left := by
  let Z := pullback f f
  let p₁ : Z ⟶ X := pullback.fst f f
  let p₂ : Z ⟶ X := pullback.snd f f
  have hfqc : QuasiCompact f.left := by
    have : QuasiCompact (f.left ≫ Y.hom) := by
      rw [f.w]
      infer_instance
    exact QuasiCompact.of_comp f.left Y.hom
  let := hfqc
  have hZqc : QuasiCompact Z.hom := by
    have he : Z.hom =
        pullbackComparison (Over.forget (Spec (CommRingCat.of R))) f f ≫
          pullback.fst f.left f.left ≫ X.hom := by
      have hc := pullbackComparison_comp_fst
        (Over.forget (Spec (CommRingCat.of R))) f f
      change pullbackComparison (Over.forget (Spec (CommRingCat.of R))) f f ≫
        pullback.fst f.left f.left = p₁.left at hc
      calc
        Z.hom = p₁.left ≫ X.hom := p₁.w.symm
        _ = (pullbackComparison (Over.forget (Spec (CommRingCat.of R))) f f ≫
            pullback.fst f.left f.left) ≫ X.hom :=
          congrArg (fun k => k ≫ X.hom) hc.symm
        _ = _ := Category.assoc _ _ _
    rw [he]
    infer_instance
  let := hZqc
  let F := Over.pullback (Spec.algebraMap R A)
  have : Mono (F.map f) := Over.mono_of_mono_left _
  have hpair : F.map p₁ = F.map p₂ := by
    change F.map (pullback.fst f f) = F.map (pullback.snd f f)
    rw [← pullbackComparison_comp_fst F f f, ← pullbackComparison_comp_snd F f f,
      fst_eq_snd_of_mono_eq]
  have hfst : pullback.fst Z.hom (Spec.algebraMap R A) ≫ p₁.left =
      pullback.fst Z.hom (Spec.algebraMap R A) ≫ p₂.left := by
    have he := congrArg (fun k => k.left ≫ pullback.fst X.hom (Spec.algebraMap R A)) hpair
    simpa only [F, Over.pullback_map_left, pullback.lift_fst] using he
  obtain ⟨T, hT, hs, heq⟩ :=
    exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      Z.hom X.hom p₁.left p₂.left p₁.w p₂.w hfst s
  let Fₜ := Over.pullback (Spec.algebraMap R T)
  have hpairT : Fₜ.map p₁ = Fₜ.map p₂ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Fₜ, Over.pullback_map_left, pullback.lift_fst] using heq
    · exact (Fₜ.map p₁).w.trans (Fₜ.map p₂).w.symm
  have hproj : pullback.fst (Fₜ.map f) (Fₜ.map f) =
      pullback.snd (Fₜ.map f) (Fₜ.map f) := by
    apply (cancel_epi (pullbackComparison Fₜ f f)).mp
    simpa only [pullbackComparison_comp_fst, pullbackComparison_comp_snd] using hpairT
  have : Mono (Fₜ.map f) := by
    constructor
    intro W g h hgh
    calc
      g = pullback.lift g h hgh ≫ pullback.fst (Fₜ.map f) (Fₜ.map f) :=
        (pullback.lift_fst _ _ _).symm
      _ = pullback.lift g h hgh ≫ pullback.snd (Fₜ.map f) (Fₜ.map f) := by rw [hproj]
      _ = h := pullback.lift_snd _ _ _
  exact ⟨T, hT, hs, inferInstance⟩

/-- Exact monicity descent over arbitrary coefficient algebras. -/
theorem monomorphism : MonomorphismStatement.{u} := by
  intro R A _ _ _ X Y _ _ _ f hf s
  let := hf
  exact exists_fg_mono f s

end Langlands.AlgebraicGeometry.FiniteCoefficient
