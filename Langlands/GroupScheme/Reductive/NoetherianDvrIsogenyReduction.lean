import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Langlands.GroupScheme.Reductive.FibrewiseIsogenyReduction
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.IsogenyStability

/-! # Detecting isogenies over a noetherian affine base by DVR base changes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- Over a noetherian affine base, finiteness of an affine morphism locally of
finite type is detected by its base changes to spectra of domain DVRs. -/
theorem isFinite_of_dvr_baseChanges
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsAffineHom f] [LocallyOfFiniteType f]
    (hf : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A)),
      IsFinite (pullback.snd f b)) :
    IsFinite f := by
  have : UniversallyClosed f :=
    universallyClosed_of_forall_isDiscreteValuationRing_hasLift f fun S hS => by
      let := hS
      let v := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))
      let p := pullback.snd f S.i₂
      have : IsFinite p := hf S.R S.i₂
      have hp : ValuativeCriterion.Existence p := by
        have hp' : UniversallyClosed p := inferInstance
        rw [UniversallyClosed.eq_valuativeCriterion] at hp'
        exact hp'.1
      let T : ValuativeCommSq p :=
        { R := S.R
          K := S.K
          i₁ := pullback.lift S.i₁ v S.commSq.w
          i₂ := 𝟙 _
          commSq := ⟨by
            change pullback.lift S.i₁ v S.commSq.w ≫ pullback.snd f S.i₂ = v ≫ 𝟙 _
            rw [pullback.lift_snd, Category.comp_id]⟩ }
      obtain ⟨l, hl₁, hl₂⟩ := (hp T).exists_lift
      refine ⟨⟨⟨l ≫ pullback.fst f S.i₂, ?_, ?_⟩⟩⟩
      · rw [← Category.assoc, hl₁]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, pullback.condition, ← Category.assoc, hl₂]
        simp [T]
  have : IsProper f := {}
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Every base change of the specified homomorphism to a domain DVR is an
isogeny. No Henselian or residue-field hypothesis is imposed on these DVRs. -/
def IsDvrwiseIsogeny (f : G ⟶ H) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (b : Spec (CommRingCat.of R) ⟶ S), IsIsogeny ((baseChange b).map f)

/-- An isogeny is an isogeny after every DVR base change. -/
theorem IsIsogeny.isDvrwiseIsogeny {f : G ⟶ H} (hf : IsIsogeny f) :
    IsDvrwiseIsogeny f := by
  intro R _ _ _ b
  exact hf.baseChange b

/-- DVRwise isogenies have finite kernels over a noetherian affine base. -/
theorem finite_kernel_of_dvrwiseIsogeny
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) (hf : IsDvrwiseIsogeny f) :
    IsFinite (kernel f).X.hom := by
  have hcomp : (kernelι f).hom.hom.left ≫ G.X.hom = (kernel f).X.hom :=
    Over.w (kernelι f).hom.hom
  have : IsAffineHom (kernel f).X.hom := by
    rw [← hcomp]
    infer_instance
  have : LocallyOfFiniteType (kernel f).X.hom := by
    rw [← hcomp]
    infer_instance
  apply Langlands.AlgebraicGeometry.isFinite_of_dvr_baseChanges
  intro R _ _ _ b
  have hfin : IsFinite (kernel ((baseChange b).map f)).X.hom :=
    MorphismProperty.of_isPullback
      (kernel_isPullback_scheme ((baseChange b).map f)) (hf R b).1
  let e := kernelBaseChangeIso b f
  have : IsIso e.hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Grp.forget _ ⋙ Over.forget _).map e.hom))
  have : IsFinite
      (e.hom.hom.hom.left ≫ (kernel ((baseChange b).map f)).X.hom) := by
    let := hfin
    infer_instance
  change IsFinite ((baseChange b).obj (kernel f)).X.hom
  simpa only [Over.w] using this

/-- Over a noetherian affine base, the DVRwise condition supplies the missing
finiteness in the fibrewise isogeny criterion for smooth affine groups. -/
theorem isogeny_of_fibrewise_and_dvrwise
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) (hf : IsFibrewiseIsogeny f) (hDvr : IsDvrwiseIsogeny f) :
    IsIsogeny f :=
  (isogeny_iff_finite_kernel_of_isogeny_fibres f hf).mpr
    (finite_kernel_of_dvrwiseIsogeny f hDvr)

end Langlands.GroupScheme
