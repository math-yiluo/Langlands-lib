import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCovering
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Localization of the finite full-domain site -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

private theorem hom_unique {B : PresentedAffinoidAlgebra K}
    {U V : Domain K B} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

private theorem over_hom_unique {U V : Over d} (f g : U ⟶ V) : f = g := by
  apply Over.OverMorphism.ext
  exact hom_unique f.left g.left

/-- Finite ambient covers lift through actual extension to the containing
domain's algebra, with no nonempty-cover assumption. -/
instance extendOverFunctor_isCocontinuous :
    d.extendOverFunctor.IsCocontinuous
      (finiteDomainTopology K d.algebra) ((finiteDomainTopology K A).over d) where
  cover_lift {U} {S} hS := by
    change IsFiniteCovering (Sieve.overEquiv _ S) at hS
    obtain ⟨I, hI, D, f, hf, hc⟩ := hS
    let V : I → Over d := fun i =>
      Over.mk (f i ≫ (d.extendOverFunctor.obj U).hom)
    let g : ∀ i, V i ⟶ d.extendOverFunctor.obj U := fun i => Over.homMk (f i)
    let E : I → Domain K d.algebra := fun i => d.relativeFunctor.obj (V i)
    let a : ∀ i, E i ⟶ U := fun i =>
      d.relativeFunctor.map (g i) ≫ d.localizationEquivalence.unitIso.inv.app U
    refine ⟨I, hI, E, a, ?_, ?_⟩
    · intro i
      change S (d.extendOverFunctor.map (a i))
      have hi : S (g i) := (Sieve.overEquiv_iff S (f i)).mp (hf i)
      have heq : d.extendOverFunctor.map (a i) =
          d.localizationEquivalence.counitIso.hom.app (V i) ≫ g i :=
        over_hom_unique d _ _
      rw [heq]
      exact S.downward_closed hi _
    · intro x hx
      obtain ⟨i, hi⟩ := hc (d.spectrumMap x) ⟨x, hx, rfl⟩
      refine ⟨i, ?_⟩
      change x ∈ (d.relative (D i) (f i ≫ (d.extendOverFunctor.obj U).hom)).locus
      rw [d.relative_locus_eq_preimage]
      exact hi

/-- Finite covers over the containing algebra extend to finite covers on
the ambient slice, retaining their actual bounded arrows. -/
instance relativeFunctor_isCocontinuous :
    d.relativeFunctor.IsCocontinuous
      ((finiteDomainTopology K A).over d) (finiteDomainTopology K d.algebra) where
  cover_lift {V} {S} hS := by
    obtain ⟨I, hI, D, f, hf, hc⟩ := hS
    let E : I → Over d := fun i => d.extendOverFunctor.obj (D i)
    let a : ∀ i, E i ⟶ V := fun i =>
      d.extendOverFunctor.map (f i) ≫ d.localizationEquivalence.counitIso.hom.app V
    change IsFiniteCovering (Sieve.overEquiv V (S.functorPullback d.relativeFunctor))
    refine ⟨I, hI, fun i => (E i).left, fun i => (a i).left, ?_, ?_⟩
    · intro i
      have hi : (S.functorPullback d.relativeFunctor) (a i) := by
        change S (d.relativeFunctor.map (a i))
        rw [hom_unique (d.relativeFunctor.map (a i))
          (d.localizationEquivalence.unitIso.inv.app (D i) ≫ f i)]
        exact S.downward_closed (hf i) _
      exact Sieve.image_mem_functorPushforward (Over.forget d) _ hi
    · intro x hx
      have hx' : x ∈ d.spectrumMap '' (d.relative V.left V.hom).locus := by
        rw [d.image_relative_locus]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      obtain ⟨i, hi⟩ := hc y hy
      exact ⟨i, y, hi, rfl⟩

instance localizationEquivalence_functor_isCocontinuous :
    d.localizationEquivalence.functor.IsCocontinuous
      (finiteDomainTopology K d.algebra) ((finiteDomainTopology K A).over d) :=
  d.extendOverFunctor_isCocontinuous

instance localizationEquivalence_inverse_isCocontinuous :
    d.localizationEquivalence.inverse.IsCocontinuous
      ((finiteDomainTopology K A).over d) (finiteDomainTopology K d.algebra) :=
  d.relativeFunctor_isCocontinuous

instance localizationEquivalence_inverse_isDenseSubsite :
    d.localizationEquivalence.inverse.IsDenseSubsite
      ((finiteDomainTopology K A).over d) (finiteDomainTopology K d.algebra) :=
  d.localizationEquivalence.isDenseSubsite_inverse_of_isCocontinuous
    (finiteDomainTopology K d.algebra) ((finiteDomainTopology K A).over d)

instance relativeFunctor_isDenseSubsite :
    d.relativeFunctor.IsDenseSubsite
      ((finiteDomainTopology K A).over d) (finiteDomainTopology K d.algebra) :=
  d.localizationEquivalence_inverse_isDenseSubsite

instance extendOverFunctor_isDenseSubsite :
    d.extendOverFunctor.IsDenseSubsite
      (finiteDomainTopology K d.algebra) ((finiteDomainTopology K A).over d) :=
  d.localizationEquivalence.isDenseSubsite_functor_of_isCocontinuous
    (finiteDomainTopology K d.algebra) ((finiteDomainTopology K A).over d)

/-- Sheaves on all full domains over the actual algebra of `d` are
equivalent to sheaves on the ambient finite-domain site localized at `d`. -/
def localizationSheafEquivalence (T : Type v) [Category.{w} T] :
    Sheaf (finiteDomainTopology K d.algebra) T ≌
      Sheaf ((finiteDomainTopology K A).over d) T :=
  d.localizationEquivalence.sheafCongr
    (finiteDomainTopology K d.algebra) ((finiteDomainTopology K A).over d) T

@[simp]
theorem localizationSheafEquivalence_functor_obj
    {T : Type v} [Category.{w} T]
    (F : Sheaf (finiteDomainTopology K d.algebra) T) :
    ((d.localizationSheafEquivalence T).functor.obj F).obj =
      d.relativeFunctor.op ⋙ F.obj := rfl

@[simp]
theorem localizationSheafEquivalence_inverse_obj
    {T : Type v} [Category.{w} T]
    (F : Sheaf ((finiteDomainTopology K A).over d) T) :
    ((d.localizationSheafEquivalence T).inverse.obj F).obj =
      d.extendOverFunctor.op ⋙ F.obj := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
