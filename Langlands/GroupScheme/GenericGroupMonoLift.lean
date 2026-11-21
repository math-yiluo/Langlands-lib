import Langlands.AlgebraicGeometry.EtaleConstantGenericSection
import Langlands.AlgebraicGeometry.IntegralDominantImage
import Langlands.AlgebraicGeometry.SmoothNormalDomainStalks
import Langlands.GroupScheme.IntegralModel.SchematicClosureProof
import Langlands.GroupScheme.ReducedBaseSmooth.Translation

/-! # Lifting a smooth group through a monomorphism from the generic fibre -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem exists_lift_of_open_unit {S : Scheme.{u}} {D H L : GroupScheme S}
    (i : H ⟶ L) [Mono i.hom.hom.left] (e : D ⟶ L)
    [Smooth D.X.hom] [GeometricallyConnected D.X.hom]
    {P : Over S} (o : P ⟶ D.X) [IsOpenImmersion o.left]
    (hunit : Set.range η[D.X].left ⊆ Set.range o.left)
    (l : P ⟶ H.X) (hl : l ≫ i.hom.hom = o ≫ e.hom.hom) :
    ∃ j : D ⟶ H, j ≫ i = e := by
  let p := (o ⊗ₘ o) ≫ μ[D.X]
  let r := (l ⊗ₘ l) ≫ μ[H.X]
  have : Smooth P.hom := by rw [← Over.w o]; infer_instance
  have : Smooth p.left := ReducedBaseSmooth.smooth_tensorHom_comp_mul D o
  have : Surjective p.left := by
    rw [surjective_iff, ← Set.range_eq_univ]
    exact ReducedBaseSmooth.range_tensorHom_comp_mul_eq_univ D o
      (fun _ => MorphismProperty.pullback_snd _ _ (inferInstance : Smooth D.X.hom))
      (fun _ => inferInstance) hunit
  have hc : r.left ≫ i.hom.hom.left = p.left ≫ e.hom.hom.left := by
    change (r ≫ i.hom.hom).left = (p ≫ e.hom.hom).left
    simp only [r, p, Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hl]
  have hcompat {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (P ⊗ P).left)
      (h : g₁ ≫ p.left = g₂ ≫ p.left) : g₁ ≫ r.left = g₂ ≫ r.left := by
    apply (cancel_mono i.hom.hom.left).mp
    simpa only [Category.assoc, hc] using
      congrArg (fun t => t ≫ e.hom.hom.left) h
  let d := EffectiveEpi.desc p.left r.left hcompat
  have hd : p.left ≫ d = r.left := EffectiveEpi.fac p.left r.left hcompat
  have hfac : d ≫ i.hom.hom.left = e.hom.hom.left := by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hd, hc]
  let a : D.X ⟶ H.X := Over.homMk d (by rw [← Over.w i.hom.hom,
    ← Category.assoc, hfac, Over.w])
  have ha : a ≫ i.hom.hom = e.hom.hom := Over.OverMorphism.ext hfac
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsMonHom (a ≫ i.hom.hom) := by rw [ha]; infer_instance
  have : IsMonHom a :=
    IntegralModel.SchematicClosureConstruction.isMonHom_of_comp_mono a i.hom.hom
  exact ⟨Grp.homMk a, Grp.hom_ext _ _ ha⟩

open Langlands.AlgebraicGeometry

/-- A homomorphism from a smooth geometrically connected group over an integrally closed
domain factors through a quasi-compact monomorphism locally of finite type if it has a
scheme-theoretic lift on the generic fibre. -/
def genericGroupMonoLift
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {D H L : GroupScheme (Spec R)} (i : H ⟶ L)
    [Mono i.hom.hom.left] [QuasiCompact i.hom.hom.left] [LocallyOfFiniteType i.hom.hom.left]
    (e : D ⟶ L) [Smooth D.X.hom] [GeometricallyConnected D.X.hom]
    (a : pullback D.X.hom (Spec.algebraMap R K) ⟶ H.X.left)
    (ha : a ≫ i.hom.hom.left = pullback.fst D.X.hom (Spec.algebraMap R K) ≫ e.hom.hom.left) :
    {j : D ⟶ H // j ≫ i = e} := by
  let d := Spec.algebraMap R K
  let j := pullback.fst D.X.hom d
  let C := pullback e.hom.hom.left i.hom.hom.left
  let f : C ⟶ D.X.left := pullback.fst e.hom.hom.left i.hom.hom.left
  let a' : pullback D.X.hom d ⟶ C := pullback.lift j a ha.symm
  have haj : a' ≫ f = j := pullback.lift_fst _ _ _
  have : IsDominant d := isDominant_fractionFieldMap R K
  have : IsDominant j := isDominant_genericPullbackFst R K D.X.hom
  have : IsDominant (a' ≫ f) := haj.symm ▸ (inferInstance : IsDominant j)
  have : QuasiCompact d := inferInstance
  have : QuasiCompact (a' ≫ f) := haj.symm ▸ (inferInstance : QuasiCompact j)
  have : QuasiCompact a' := QuasiCompact.of_comp a' f
  have : IsIntegral (pullback D.X.hom d) :=
    isIntegral_of_smooth_geometricallyConnected (pullback.snd D.X.hom d)
  have : IsIntegral D.X.left := isIntegral_of_smooth_geometricallyConnected D.X.hom
  have hnormal : HasNormalStalks D.X.left := smoothNormalDomainStalks R D.X.hom inferInstance
  let U := integralDominantImageOpen a' f hnormal
  let P : Over (Spec R) := Over.mk (U.ι ≫ D.X.hom)
  let o : P ⟶ D.X := Over.homMk U.ι rfl
  let s : Spec R ⟶ C := pullback.lift η[D.X].left η[H.X].left (by
    simp only [← Over.comp_left, IsMonHom.one_hom])
  have hs : s ≫ f = η[D.X].left := pullback.lift_fst _ _ _
  let b : Spec (CommRingCat.of K) ⟶ pullback D.X.hom d :=
    pullback.lift (d ≫ η[D.X].left) (𝟙 _) (by
      rw [Category.assoc, Over.w]
      exact (Category.comp_id d).trans (Category.id_comp d).symm)
  have hb : b ≫ a' = d ≫ s := by
    have : Mono f := inferInstance
    apply (cancel_mono f).mp
    rw [Category.assoc, haj, Category.assoc, hs]
    exact pullback.lift_fst _ _ _
  have hunit : Set.range η[D.X].left ⊆ Set.range o.left := by
    change Set.range η[D.X].left ⊆ Set.range U.ι
    rw [Scheme.Opens.range_ι, ← hs]
    exact range_comp_subset_integralDominantImageOpen a' f s d b hb hnormal
  let l₀ := integralDominantImageOpenLift a' f hnormal ≫
    pullback.snd e.hom.hom.left i.hom.hom.left
  have hl₀ : l₀ ≫ i.hom.hom.left = U.ι ≫ e.hom.hom.left := by
    calc
      l₀ ≫ i.hom.hom.left =
          (integralDominantImageOpenLift a' f hnormal ≫ f) ≫ e.hom.hom.left := by
        simp only [l₀, f, Category.assoc, pullback.condition]
      _ = _ := by rw [integralDominantImageOpenLift_comp]
  let l : P ⟶ H.X := Over.homMk l₀ (by
    rw [← Over.w i.hom.hom, ← Category.assoc, hl₀, Category.assoc, Over.w]
    rfl)
  have : IsOpenImmersion o.left := inferInstanceAs (IsOpenImmersion U.ι)
  let h := exists_lift_of_open_unit i e o hunit l (Over.OverMorphism.ext hl₀)
  exact ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
