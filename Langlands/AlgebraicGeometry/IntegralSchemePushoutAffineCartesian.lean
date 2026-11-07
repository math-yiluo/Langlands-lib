import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.LocalRing.Pullback

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

variable {R S T : CommRingCat.{u}}

/-- A compatible-pair square with a surjective first map is also a ring pushout. -/
theorem isPushout_pullbackProjections (f : R ⟶ T) (g : S ⟶ T)
    (hf : Function.Surjective f) :
    IsPushout (CommRingCat.ofHom (f.hom.pullbackFst g.hom))
      (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)) f g := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk f g
      (CommRingCat.hom_ext (RingHom.pullback_comm_sq _ _)))
  apply PushoutCocone.isColimitAux'
  intro c
  have hk : RingHom.ker f.hom ≤ RingHom.ker c.inl.hom := by
    intro r hr
    have hx : f.hom r = g.hom 0 := by
      simpa only [map_zero] using (RingHom.mem_ker.mp hr)
    have hc := ConcreteCategory.congr_hom c.condition
      (⟨(r, 0), hx⟩ : f.hom.pullback g.hom)
    change c.inl.hom r = c.inr.hom 0 at hc
    exact RingHom.mem_ker.mpr (by simpa only [map_zero] using hc)
  let l : T ⟶ c.pt :=
    CommRingCat.ofHom (f.hom.liftOfSurjective hf ⟨c.inl.hom, hk⟩)
  have hl (r : R) : l (f r) = c.inl r :=
    RingHom.liftOfSurjective_comp_apply f.hom hf ⟨c.inl.hom, hk⟩ r
  refine ⟨l, ?_, ?_, ?_⟩
  · ext r
    exact hl r
  · ext s
    obtain ⟨r, hr⟩ := hf (g s)
    have hx : f.hom r = g.hom s := hr
    have hc := ConcreteCategory.congr_hom c.condition
      (⟨(r, s), hx⟩ : f.hom.pullback g.hom)
    change c.inl r = c.inr s at hc
    change l (g s) = c.inr s
    rw [← hr, hl]
    exact hc
  · intro m hm _
    ext t
    obtain ⟨r, rfl⟩ := hf t
    exact (ConcreteCategory.congr_hom hm r).trans (hl r).symm

/-- The canonical affine pinching square is cartesian. -/
theorem isPullback_specMap_pullback (f : R ⟶ T) (g : S ⟶ T)
    (hf : Function.Surjective f) :
    IsPullback (Spec.map f) (Spec.map g)
      (Spec.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
      (Spec.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_pullbackProjections f g hf)

/-- The literal affine cocone, bundled with its cartesian square. -/
noncomputable def affineCartesianCocone (f : R ⟶ T) (g : S ⟶ T)
    (hf : Function.Surjective f) :
    {c : PushoutCocone (Spec.map f) (Spec.map g) //
      IsPullback (Spec.map f) (Spec.map g) c.inl c.inr} :=
  ⟨PushoutCocone.mk
    (Spec.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
    (Spec.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.pullback_comm_sq _ _))),
    isPullback_specMap_pullback f g hf⟩

end Langlands.AlgebraicGeometry.IntegralSchemePushout
