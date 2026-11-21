import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOnePresentation
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.BoundedHomogeneousEquations
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.HilbertClassifying

/-! # A uniform equation cutoff for a fixed Hilbert-polynomial piece -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

open Langlands.AlgebraicGeometry ProjectiveSpace

/-- The tensor powers of the restricted projective twist used in the published Hilbert
family's geometric section-rank test. -/
abbrev hilbertTwistPower (m : ℕ) {T : Scheme.{u}}
    {s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))}
    (J : (pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s).IdealSheafData)
    (k : ℕ) : J.subscheme.Modules :=
  Nat.rec (motive := fun _ => J.subscheme.Modules) (𝟙_ J.subscheme.Modules)
    (fun _ M => M ⊗ (Scheme.Modules.pullback (J.subschemeι ≫ pullback.fst _ s)).obj
      (Langlands.AlgebraicGeometry.twistOne (ULift.{u} ℤ) m)) k

/-- The affine test for the piece of the Hilbert scheme indexed by `θ`, with its actual
projective twist. Each geometric fibre satisfies the rank formula eventually. -/
def HasGeometricFibreHilbertPolynomial (m : ℕ) {B : Type u} [CommRing B]
    {s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))}
    (J : (pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s).IdealSheafData)
    (θ : Polynomial ℚ) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (sk : B →+* K),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ((Scheme.Modules.geomFibreH0Finrank (J.subschemeι ≫ pullback.snd _ s)
        (hilbertTwistPower m J k) K sk : ℕ) : ℚ) = θ.eval (k : ℚ)

/-- Embedded flat, locally finitely presented families of fixed Hilbert polynomial over
spectra of local rings in the given universe have a common homogeneous equation cutoff.
The bound depends only on the ambient dimension and polynomial (in that universe). -/
theorem exists_uniformBoundedHomogeneousEquations_of_hilbertPolynomial
    (m : ℕ) (θ : Polynomial ℚ) :
    ∃ D : ℕ, ∀ (B : Type u) [CommRing B] [IsLocalRing B]
      (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
      (J : (pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s).IdealSheafData),
      Flat (J.subschemeι ≫ pullback.snd _ s) →
      LocallyOfFinitePresentation (J.subschemeι ≫ pullback.snd _ s) →
      HasGeometricFibreHilbertPolynomial m J θ →
      HasBoundedHomogeneousEquations
        (J.comap ((polynomialIsoSpec B m).hom ≫ (isoPullbackSpec m s).hom)) D := by
  let f := projectiveSpaceToSpec (ULift.{u} ℤ) m
  obtain ⟨H, πH, W, -, -, huniv, U, -, -, hpiece⟩ :=
    HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily.{u} (ULift.{u} ℤ) f
      (Langlands.AlgebraicGeometry.twistOne (ULift.{u} ℤ) m) inferInstance inferInstance (twistOne_isInvertible _ _)
      (twistOne_closedImmersionBySections _ _)
  let O := U θ
  let W' := (W.comap (isoPullbackSpec m πH).hom).comap (map m O.ι)
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsProper (O.ι ≫ πH) := (hpiece θ).1.isProper
  have : IsLocallyNoetherian O.toScheme := LocallyOfFiniteType.isLocallyNoetherian (O.ι ≫ πH)
  have : CompactSpace O.toScheme := QuasiCompact.compactSpace_of_compactSpace (O.ι ≫ πH)
  have : IsNoetherian O.toScheme := ⟨⟩
  obtain ⟨D, hD⟩ := exists_uniformBoundedHomogeneousEquations m W'
  refine ⟨D, fun B _ _ s J hflat hlfp hθ => ?_⟩
  obtain ⟨v, ⟨hv, hvW⟩, -⟩ := (huniv _ s).2 J hflat hlfp
  have hvO := ((hpiece θ).2 B s v hv J hvW).mpr hθ
  let x := IsOpenImmersion.lift O.ι v (by simpa only [Scheme.Opens.range_ι] using hvO)
  have hx : x ≫ O.ι = v := IsOpenImmersion.lift_fac _ _ _
  have hcomap : W'.comap ((polynomialIsoSpec B m).hom ≫ map m x) =
      J.comap ((polynomialIsoSpec B m).hom ≫ (isoPullbackSpec m s).hom) := by
    simp only [W', ← Scheme.IdealSheafData.comap_comp, Category.assoc]
    rw [← Category.assoc (map m x) (map m O.ι), ← map_comp, hx,
      map_isoPullbackSpec_hom m v πH s hv]
    rw [← Category.assoc, Scheme.IdealSheafData.comap_comp, hvW]
  rw [← hcomap]
  exact hD B x

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
