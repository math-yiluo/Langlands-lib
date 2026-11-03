import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Actual intersections of two full represented affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

namespace AffinoidPushout

/-- Compatible points lift to a point of the actual quotient. This asserts
surjectivity onto compatible pairs, with no general injectivity claim. -/
theorem exists_point (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
    (x : BanachSpectrum B) (y : BanachSpectrum C)
    (hxy : BanachSpectrum.comap f.toBoundedRingHom x =
      BanachSpectrum.comap g.toBoundedRingHom y) :
    ∃ z : BanachSpectrum (algebra f g),
      BanachSpectrum.comap (leftMap f g).toBoundedRingHom z = x ∧
      BanachSpectrum.comap (rightMap f g).toBoundedRingHom z = y := by
  obtain ⟨L, hLF, hLU, hLC, hLA, α, β, hαβ, hα, hβ⟩ :=
    pointAmalgamation K A B C f g x y hxy
  let := hLF
  let := hLU
  let := hLC
  let := hLA
  let θ := lift f g L α β hαβ
  refine ⟨BanachSpectrum.comap θ.toBoundedRingHom (BanachSpectrum.fieldPoint L), ?_, ?_⟩
  · apply BanachSpectrum.ext
    intro b
    change ‖θ (leftMap f g b)‖ = x b
    calc
      _ = ‖α b‖ := congrArg norm
        (congrArg (fun h : BoundedAlgHom K B L => h b) (lift_comp_leftMap f g L α β hαβ))
      _ = x b := hα b
  · apply BanachSpectrum.ext
    intro c
    change ‖θ (rightMap f g c)‖ = y c
    calc
      _ = ‖β c‖ := congrArg norm
        (congrArg (fun h : BoundedAlgHom K C L => h c) (lift_comp_rightMap f g L α β hαβ))
      _ = y c := hβ c

end AffinoidPushout

namespace Domain

private theorem hom_unique {U V : Domain K A} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

variable (U V : Domain K A)

/-- The actual pushout structural map represents the literal intersection
against every presented affinoid test. -/
theorem represents_inter :
    Represents K
      ((AffinoidPushout.leftMap U.baseMap V.baseMap).comp U.baseMap)
      (U.locus ∩ V.locus) := by
  let Q := AffinoidPushout.algebra U.baseMap V.baseMap
  let l := AffinoidPushout.leftMap U.baseMap V.baseMap
  let r := AffinoidPushout.rightMap U.baseMap V.baseMap
  have hcomm : l.comp U.baseMap = r.comp V.baseMap :=
    AffinoidPushout.condition U.baseMap V.baseMap
  have heq (z : BanachSpectrum Q) :
      U.spectrumMap (BanachSpectrum.comap l.toBoundedRingHom z) =
        V.spectrumMap (BanachSpectrum.comap r.toBoundedRingHom z) := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun h : BoundedAlgHom K A Q => z (h a)) hcomm
  refine ⟨U.represents.1.inter V.represents.1, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      change U.spectrumMap (BanachSpectrum.comap l.toBoundedRingHom z) ∈ U.locus ∩ V.locus
      refine ⟨U.represents.hasImageIn _, ?_⟩
      rw [heq]
      exact V.represents.hasImageIn _
    · rintro ⟨hxU, hxV⟩
      obtain ⟨u, hu⟩ := U.represents.2.1.symm ▸ hxU
      obtain ⟨v, hv⟩ := V.represents.2.1.symm ▸ hxV
      obtain ⟨z, hzu, _⟩ := AffinoidPushout.exists_point U.baseMap V.baseMap u v
        (hu.trans hv.symm)
      refine ⟨z, ?_⟩
      change U.spectrumMap (BanachSpectrum.comap l.toBoundedRingHom z) = x
      rw [hzu]
      exact hu
  · intro R φ hφ
    obtain ⟨α, hα, hαuniq⟩ := U.represents.2.2 R φ (fun z => (hφ z).1)
    obtain ⟨β, hβ, hβuniq⟩ := V.represents.2.2 R φ (fun z => (hφ z).2)
    have hcompat : α.comp U.baseMap = β.comp V.baseMap := hα.trans hβ.symm
    let θ := AffinoidPushout.lift U.baseMap V.baseMap R α β hcompat
    have hθl : θ.comp l = α := AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _
    have hθr : θ.comp r = β := AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _
    refine ⟨θ, ?_, ?_⟩
    · change θ.comp (l.comp U.baseMap) = φ
      rw [← BoundedAlgHom.comp_assoc, hθl, hα]
    · intro ψ hψ
      apply AffinoidPushout.hom_ext U.baseMap V.baseMap R
      · rw [hθl]
        apply hαuniq
        change ψ.comp (l.comp U.baseMap) = φ
        exact hψ
      · rw [hθr]
        apply hβuniq
        change ψ.comp (r.comp V.baseMap) = φ
        rw [← hcomm]
        exact hψ

/-- The full intersection uses the constructed appended weighted quotient. -/
def inter : Domain K A where
  algebra := AffinoidPushout.algebra U.baseMap V.baseMap
  baseMap := (AffinoidPushout.leftMap U.baseMap V.baseMap).comp U.baseMap
  locus := U.locus ∩ V.locus
  represents := U.represents_inter V

@[simp]
theorem inter_algebra : (U.inter V).algebra =
    AffinoidPushout.algebra U.baseMap V.baseMap := rfl

@[simp]
theorem inter_locus : (U.inter V).locus = U.locus ∩ V.locus := rfl

/-- The first projection is the original first quotient leg. -/
def interLeft : U.inter V ⟶ U where
  restriction := AffinoidPushout.leftMap U.baseMap V.baseMap
  comp_baseMap := rfl

/-- The second projection is the original second quotient leg. -/
def interRight : U.inter V ⟶ V where
  restriction := AffinoidPushout.rightMap U.baseMap V.baseMap
  comp_baseMap := (AffinoidPushout.condition U.baseMap V.baseMap).symm

/-- Every pair of actual inclusions factors through the literal intersection. -/
def interLift {U V W : Domain K A} (f : W ⟶ U) (g : W ⟶ V) : W ⟶ U.inter V :=
  inclusionOfSubset W (U.inter V) fun _ hx => ⟨f.subset hx, g.subset hx⟩

@[simp]
theorem interLift_left {U V W : Domain K A} (f : W ⟶ U) (g : W ⟶ V) :
    interLift f g ≫ U.interLeft V = f := hom_unique _ _

@[simp]
theorem interLift_right {U V W : Domain K A} (f : W ⟶ U) (g : W ⟶ V) :
    interLift f g ≫ U.interRight V = g := hom_unique _ _

/-- Intersections give the actual pullback over any containing full domain. -/
def interPullbackCone {U V W : Domain K A} (f : U ⟶ W) (g : V ⟶ W) :
    PullbackCone f g :=
  PullbackCone.mk (U.interLeft V) (U.interRight V) (hom_unique _ _)

/-- Full-test factorization constructs the limit lifts, retaining both quotient legs. -/
def interPullbackConeIsLimit {U V W : Domain K A} (f : U ⟶ W) (g : V ⟶ W) :
    IsLimit (interPullbackCone f g) :=
  PullbackCone.IsLimit.mk _ (fun S => interLift S.fst S.snd)
    (fun _ => hom_unique _ _) (fun _ => hom_unique _ _)
    (fun _ _ _ _ => hom_unique _ _)

end Domain
end Langlands.Analytic.PresentedAffinoidAlgebra
