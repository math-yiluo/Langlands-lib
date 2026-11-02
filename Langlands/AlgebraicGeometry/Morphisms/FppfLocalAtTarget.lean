import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Properties of morphisms local on the target in the fppf topology

A property of morphisms of schemes that is Zariski local on the target, stable under base change,
and descends along surjective flat morphisms locally of finite presentation is local on the
target for the fppf precoverage. Consequently it can be checked after base change to the members
of an fppf covering sieve.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FppfLocal

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
  [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]

/-- A property that is Zariski local on the target, stable under base change and descends along
fppf coverings is local on the target for the fppf precoverage. The proof descends along the
single morphism from the disjoint union of a cover, and checks the base change to the disjoint
union on its open cover by the summands. -/
theorem isLocalAtTarget_fppfPrecoverage : P.IsLocalAtTarget Scheme.fppfPrecoverage := by
  have : Precoverage.Small.{u} Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Precoverage.Small.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine .mk_of_small (fun _ hf _ ↦ P.pullback_snd _ _ hf) fun {X Y f} 𝒰 h ↦ ?_
  let 𝒱 : Y.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  let g : ∐ 𝒱.X ⟶ Y := Sigma.desc 𝒱.f
  have hflat : Flat g := IsZariskiLocalAtSource.sigmaDesc fun i ↦ (𝒱.map_prop i).1
  have hlfp : LocallyOfFinitePresentation g :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦ (𝒱.map_prop i).2
  have hsurj : Surjective g := by
    constructor
    intro y
    obtain ⟨i, x, rfl⟩ := 𝒱.exists_eq y
    exact ⟨Sigma.ι 𝒱.X i x, by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) ⟨⟨hsurj, hflat⟩, hlfp⟩ ?_
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover 𝒱.X) fun i ↦ ?_
  change P (pullback.snd (pullback.snd f g) (Sigma.ι 𝒱.X i))
  have hbig := ((IsPullback.of_hasPullback (pullback.snd f g) (Sigma.ι 𝒱.X i)).flip.paste_vert
    (IsPullback.of_hasPullback f g).flip).flip
  have hi : Sigma.ι 𝒱.X i ≫ g = 𝒰.f i := Sigma.ι_comp_desc _ _
  rw [hi] at hbig
  rw [← hbig.isoPullback_hom_snd, P.cancel_left_of_respectsIso]
  exact h i

/-- A property of morphisms as above holds for `p : V ⟶ T` once it holds for some base change
of `p` along every member of an fppf covering sieve of `T`. -/
theorem of_fppfTopology_sieve {V T : Scheme.{u}} (p : V ⟶ T) (J : Sieve T)
    (hJ : J ∈ Scheme.fppfTopology T)
    (h : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ T), J f →
      ∃ (W : Scheme.{u}) (fst : W ⟶ V) (snd : W ⟶ Y), IsPullback fst snd p f ∧ P snd) :
    P p := by
  have := isLocalAtTarget_fppfPrecoverage P
  have : Precoverage.HasIsos Scheme.fppfPrecoverage.{u} :=
    ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  have : Precoverage.HasPullbacks Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Precoverage.HasPullbacks
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  obtain ⟨R, hR, hRJ⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition).1 hJ
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR fun {Y f} _ hf ↦ ?_
  obtain ⟨W, fst, snd, hW, hP⟩ := h f (hRJ _ f hf)
  rw [← hW.isoPullback_hom_snd, P.cancel_left_of_respectsIso] at hP
  exact hP

end Langlands.AlgebraicGeometry.FppfLocal
