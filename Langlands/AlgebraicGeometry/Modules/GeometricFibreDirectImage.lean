import Langlands.AlgebraicGeometry.Modules.FibreCohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology

/-! # Direct images of line bundles with geometric fibre cohomology in degree zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Along any pullback square of `f` along `b : Spec R ⟶ S`, the relative cohomology of the
pulled-back module agrees with that along Mathlib's chosen fibre product. -/
theorem nonempty_relativeCohomology_iso_chosenPullback {S X X' : Scheme.{u}}
    {R : CommRingCat.{u}} {f : X ⟶ S} {b : Spec R ⟶ S} {q : X' ⟶ X} {f' : X' ⟶ Spec R}
    (h : IsPullback q f' f b) (M : X.Modules) (n : ℕ) :
    Nonempty ((relativeCohomology f' n).obj ((Scheme.Modules.pullback q).obj M) ≅
      (relativeCohomology (pullback.snd f b) n).obj
        ((Scheme.Modules.pullback (pullback.fst f b)).obj M)) := by
  obtain ⟨e, he₁, he₂⟩ : ∃ e : X' ≅ pullback f b,
      e.hom ≫ pullback.fst f b = q ∧ e.hom ≫ pullback.snd f b = f' :=
    ⟨h.isoPullback, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩
  subst he₁ he₂
  exact ⟨(relativeCohomology _ n).mapIso
      ((Scheme.Modules.pullbackComp e.hom (pullback.fst f b)).app M).symm ≪≫
    relativeCohomologyPullbackIso e (pullback.snd f b) _ n⟩

/-- If the chosen geometric fibres of `f` have the cohomology of `L` concentrated in degree
zero, of dimension `r`, then every affine Cartesian chart of `f` satisfies
`GeometricFibreCohomologyDegreeZero` for the pulled-back line bundle. -/
theorem geometricFibreCohomologyDegreeZero_of_isPullback {S X : Scheme.{u}} {f : X ⟶ S}
    {L : LineBundle X} {r : ℕ}
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (b : Spec (CommRingCat.of k) ⟶ S),
      (∀ i : ℕ, 0 < i → IsZero ((relativeCohomology (pullback.snd f b) i).obj
          ((Scheme.Modules.pullback (pullback.fst f b)).obj L.obj))) ∧
        Module.finrank k ((relativeCohomology (pullback.snd f b) 0).obj
          ((Scheme.Modules.pullback (pullback.fst f b)).obj L.obj)) = r)
    {R : CommRingCat.{u}} {x : Spec R ⟶ S} {XR : Scheme.{u}} {p : XR ⟶ X}
    {fR : XR ⟶ Spec R} (hx : IsPullback p fR f x) :
    GeometricFibreCohomologyDegreeZero fR ((LineBundle.pullback p).obj L) r := by
  intro k _ _ φ X' p' f' hp'
  have hq := hp'.paste_horiz hx
  obtain ⟨hz, hr⟩ := hfib k (Spec.map φ ≫ x)
  let e : ∀ n : ℕ, (relativeCohomology f' n).obj
      ((Scheme.Modules.pullback p').obj ((LineBundle.pullback p).obj L).obj) ≅
      (relativeCohomology (pullback.snd f (Spec.map φ ≫ x)) n).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map φ ≫ x))).obj L.obj) := fun n =>
    (relativeCohomology f' n).mapIso ((Scheme.Modules.pullbackComp p' p).app L.obj) ≪≫
      (nonempty_relativeCohomology_iso_chosenPullback hq L.obj n).some
  refine ⟨fun i hi => (hz i hi).of_iso (e i), ?_⟩
  rw [← hr]
  exact (e 0).toLinearEquiv.finrank_eq

/-- Cohomology and base change for a line bundle `L` on a smooth proper `f : X ⟶ S` over an
arbitrary base: if on every chosen geometric fibre the cohomology of `L` vanishes in positive
degrees and has an `r`-dimensional space of sections, then `f_* L` is locally free of rank `r`
and its canonical base-change morphism is invertible along every Cartesian square. -/
theorem pushforward_isLocallyFreeOfRank_and_isIso_of_geometricFibres {S X : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [IsProper f] (L : LineBundle X) (r : ℕ)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (b : Spec (CommRingCat.of k) ⟶ S),
      (∀ i : ℕ, 0 < i → IsZero ((relativeCohomology (pullback.snd f b) i).obj
          ((Scheme.Modules.pullback (pullback.fst f b)).obj L.obj))) ∧
        Module.finrank k ((relativeCohomology (pullback.snd f b) 0).obj
          ((Scheme.Modules.pullback (pullback.fst f b)).obj L.obj)) = r) :
    Langlands.Scheme.Modules.IsLocallyFreeOfRank ((Scheme.Modules.pushforward f).obj L.obj) r ∧
      ∀ {S' X' : Scheme.{u}} (b : S' ⟶ S) (f' : X' ⟶ S') (p : X' ⟶ X)
        (h : IsPullback p f' f b), IsIso (pushforwardBaseChange b f f' p h.w L.obj) := by
  refine pushforward_isLocallyFreeOfRank_and_isIso_pushforwardBaseChange f L r
    (fun R x XR p fR hx => ?_)
  have : Smooth fR :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth) hx inferInstance
  have : IsProper fR :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hx inferInstance
  exact sections_of_geometricFibreCohomologyDegreeZero fR ((LineBundle.pullback p).obj L)
    (geometricFibreCohomologyDegreeZero_of_isPullback hfib hx)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
