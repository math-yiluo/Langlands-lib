import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageReductionStatement
import Langlands.AlgebraicGeometry.Modules.GeometricFibreDirectImage

/-! # The cubic direct image from the cohomology of its algebraically closed fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- On every chosen geometric fibre, the pulled-back cubic bundle has the cohomology given by
`CubicFibreCohomologyStatement` for the pulled-back datum. -/
theorem Datum.cubicBundle_chosenGeometricFibre (H : CubicFibreCohomologyStatement.{u})
    (hd : 0 < d) (a : Datum P S g d n) (k : Type u) [Field k] [IsAlgClosed k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    (∀ i : ℕ, 0 < i → IsZero ((relativeCohomology (pullback.snd a.abelian.X.hom b) i).obj
        ((Scheme.Modules.pullback (pullback.fst a.abelian.X.hom b)).obj a.cubicBundle.obj))) ∧
      Module.finrank k ((relativeCohomology (pullback.snd a.abelian.X.hom b) 0).obj
        ((Scheme.Modules.pullback (pullback.fst a.abelian.X.hom b)).obj a.cubicBundle.obj)) =
        6 ^ g * d := by
  obtain ⟨hz, hr⟩ := H P k g d n hd (a.pullback b)
  let e : ∀ i : ℕ, (relativeCohomology (pullback.snd a.abelian.X.hom b) i).obj
      ((Scheme.Modules.pullback (pullback.fst a.abelian.X.hom b)).obj a.cubicBundle.obj) ≅
      (relativeCohomology (a.pullback b).abelian.X.hom i).obj (a.pullback b).cubicBundle.obj :=
    fun i => ((relativeCohomology (a.pullback b).abelian.X.hom i).mapIso
      ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso b))).symm
  refine ⟨fun i hi => (hz i hi).of_iso (e i), ?_⟩
  rw [← hr]
  exact (e 0).toLinearEquiv.finrank_eq

/-- The cohomology of the cubic diagonal bundle over algebraically closed fields gives the
prescribed rank and canonical arbitrary base change of its direct image. -/
theorem cubicDirectImageReduction : CubicDirectImageReductionStatement.{u} := by
  intro H P S _ g d n hd a
  obtain ⟨hfree, hbc⟩ := pushforward_isLocallyFreeOfRank_and_isIso_of_geometricFibres
    a.abelian.X.hom a.cubicBundle (6 ^ g * d)
    (fun k _ _ b => a.cubicBundle_chosenGeometricFibre H hd k b)
  refine ⟨hfree, fun S' b => ?_⟩
  have := hbc b (a.pullback b).abelian.X.hom (pullback.fst a.abelian.X.hom b)
    (IsPullback.of_hasPullback a.abelian.X.hom b)
  exact IsIso.comp_isIso' this (Iso.isIso_hom ((Scheme.Modules.pushforward _).mapIso
    ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso b)).symm))

end Langlands.AbelianScheme.PolarizedFiniteLevel
