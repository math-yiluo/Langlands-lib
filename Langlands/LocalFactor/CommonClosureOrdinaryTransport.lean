import Langlands.LocalFactor.CommonClosureSpectralTransport
import Langlands.VirtualRepresentation.ExactRestriction

/-! # Actual ordinary spectral transport to the standalone extension -/

noncomputable section

universe uF uE uV

namespace Langlands.LocalFactor.CommonClosureSpectral.Transport

open CommonClosure Weil.Local LocalClassField VirtualRepresentation

variable {p : ℕ} [Fact p.Prime]
  (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The standalone spectral coordinate is the relative-residue-degree power of
that of the base field. -/
theorem spectralParameter_residueDegree (s : ℂ) :
    spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
      (CommonClosureWeilDeligne.Transport.standalone_residueCardinality_pos E) s =
    spectralParameter (baseCardinality F) (baseCardinality_pos F) s ^
      extensionResidueDegree F E f := by
  apply Units.ext
  simp only [spectralParameter, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [extensionResidueCardinality F E f, Nat.cast_pow, Real.log_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast, baseCardinality]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- Pullback of the actual base-degree spectral character equals the intrinsic
standalone character, with no supplied character comparison. -/
theorem character_comp (s : ℂ) :
    (character F (extensionFiniteIntermediate F E f) s).comp
      (extensionImageWeilEquiv F E f : localWeilGroup E →ₜ* _) =
    SpectralTwist.character (localDegree E)
      (E.canonicalTopologicalData.residueCardinality : ℝ)
      (CommonClosureWeilDeligne.Transport.standalone_residueCardinality_pos E) s := by
  ext w : 1
  change (spectralParameter (baseCardinality F) (baseCardinality_pos F) s) ^
      localDegreeInt F (extensionImageWeilEquiv F E f w : localWeilGroup F) =
    (spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
      (CommonClosureWeilDeligne.Transport.standalone_residueCardinality_pos E) s) ^
      localDegreeInt E w
  rw [extensionImageWeilEquiv_degree, spectralParameter_residueDegree F E f,
    ← zpow_natCast, ← zpow_mul]

/-- The existing continuous exact quotient for the actual standalone Weil group,
with an independent vector-space universe. -/
abbrev StandaloneVirtual :=
  SpectralTwist.ContinuousVirtual.{uE, uV} (G := localWeilGroup E)

/-- Restriction through the actual topological Weil equivalence gives an
integer-linear equivalence of the actual exact virtual groups. -/
def virtualEquiv :
    Virtual.{uF, uV} F (extensionFiniteIntermediate F E f) ≃ₗ[ℤ]
      StandaloneVirtual.{uE, max uF uV} E :=
  ExactGrothendieckGroup.continuousRestrictEquivalence (extensionImageWeilEquiv F E f)

@[simp]
theorem virtualEquiv_ofRepresentation
    (A : {A : FiniteRepresentation.{0, uF, max uF uV} ℂ
      (weilSubgroup F (extensionFiniteIntermediate F E f)) // A.IsContinuous}) :
    virtualEquiv F E f (ExactGrothendieckGroup.ofRepresentation _ A) =
      ExactGrothendieckGroup.ofRepresentation _
        ⟨FiniteRepresentation.restrict (extensionImageWeilEquiv F E f).toMonoidHom A.val,
          FiniteRepresentation.isContinuous_restrict
            (extensionImageWeilEquiv F E f).toMonoidHom
            (extensionImageWeilEquiv F E f).continuous A.property⟩ :=
  ExactGrothendieckGroup.restrict_ofRepresentation _ _ _ _ A

/-- The constructed equivalence preserves genuine virtual dimension. -/
theorem degree_virtualEquiv
    (x : Virtual.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    ExactGrothendieckGroup.degree _ (virtualEquiv F E f x) =
      degree F (extensionFiniteIntermediate F E f) x :=
  ExactGrothendieckGroup.degree_continuousRestrict _ x

/-- Spectral twisting commutes with actual standalone transport on the exact
quotient, at the unchanged complex spectral coordinate. -/
theorem virtualEquiv_twist (s : ℂ)
    (x : Virtual.{uF, uV} F (extensionFiniteIntermediate F E f)) :
    virtualEquiv F E f (virtualTwist F (extensionFiniteIntermediate F E f) s x) =
      SpectralTwist.virtual (localDegree E)
        (E.canonicalTopologicalData.residueCardinality : ℝ)
        (CommonClosureWeilDeligne.Transport.standalone_residueCardinality_pos E) s
        (virtualEquiv F E f x) := by
  have h : (virtualEquiv F E f).toLinearMap.comp
      (virtualTwist F (extensionFiniteIntermediate F E f) s).toLinearMap =
    (SpectralTwist.virtual (localDegree E)
      (E.canonicalTopologicalData.residueCardinality : ℝ)
      (CommonClosureWeilDeligne.Transport.standalone_residueCardinality_pos E) s).toLinearMap.comp
        (virtualEquiv F E f).toLinearMap := by
    apply ExactGrothendieckGroup.hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change virtualEquiv F E f
        (SpectralTwist.virtual _ _ _ s (ExactGrothendieckGroup.ofRepresentation _ A)) =
        SpectralTwist.virtual _ _ _ s
          (virtualEquiv F E f (ExactGrothendieckGroup.ofRepresentation _ A))
      rw [SpectralTwist.virtual_ofRepresentation, virtualEquiv_ofRepresentation,
        virtualEquiv_ofRepresentation, SpectralTwist.virtual_ofRepresentation]
      apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
      refine { toLinearEquiv := LinearEquiv.refl ℂ A.val, isIntertwining' := ?_ }
      intro w
      ext v
      change ((character F (extensionFiniteIntermediate F E f) s
        (extensionImageWeilEquiv F E f w) : ℂ) •
          (A.val.representation (extensionImageWeilEquiv F E f w) v)) =
        ((SpectralTwist.character (localDegree E)
          (E.canonicalTopologicalData.residueCardinality : ℝ)
          (CommonClosureWeilDeligne.Transport.standalone_residueCardinality_pos E) s w : ℂ) •
            (A.val.representation (extensionImageWeilEquiv F E f w) v))
      have hc := DFunLike.congr_fun (character_comp F E f s) w
      exact congrArg (fun z : ℂˣ => (z : ℂ) •
        (A.val.representation (extensionImageWeilEquiv F E f w) v)) hc
  exact LinearMap.congr_fun h x

end Langlands.LocalFactor.CommonClosureSpectral.Transport
