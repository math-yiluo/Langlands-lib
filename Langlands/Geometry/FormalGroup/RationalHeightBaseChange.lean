import Langlands.Geometry.FormalGroup.RationalHeightIso
import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyIsoTransport

/-! # Base change of local rational height presentations -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {U : Opens (PrimeSpectrum R)}

/-- The actual map from an inverse-image open to its original open. -/
def coefficientOpenPoint (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R))
    (x : (coefficientOpenMap φ).obj U) : U :=
  ⟨coefficientSpectrumMap φ x, x.property⟩

namespace Hom

/-- On an open coefficient square, the pulled-back integral map retains its kernel rank. -/
theorem HasHeight.openBaseChange (φ : R →ₐ[O] S) {q h : ℕ}
    {f : OpenIntegralHom M N U} (hf : f.HasHeight q h) :
    (Hom.openBaseChange φ U f).HasHeight q h :=
  (hf.map (coefficientSectionMap φ U)).isoTransport _ _

/-- Pullback on an open sends an actual scalar endomorphism to the same scalar endomorphism. -/
@[simp]
theorem openBaseChange_scalarHom (φ : R →ₐ[O] S) (M : ModuleLaw O R σ) (a : O) :
    openBaseChange φ U ((M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).scalarHom a) =
      ((M.map φ).overAlgebra ((coefficientStructurePresheaf S).obj
        (op ((coefficientOpenMap φ).obj U)))).scalarHom a := by
  change openBaseChange φ U (a • id _) = a • id _
  rw [map_smul]
  exact congrArg (a • ·) (mapSquareLinear_hom_id _ _ _ _ _)

end Hom

namespace RationalSection

private theorem transportIso_ofIntegral (a : Iso M M') (b : Iso N N')
    (f : OpenIntegralHom M N U) :
    transportIso a b U (ofIntegral U f : RationalSection F M N U) =
      ofIntegral U (Hom.isoTransport
        (a.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
        (b.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U)))) f) := by
  change comp (ofIntegral U _) (comp (ofIntegral U f) (ofIntegral U _)) = _
  rw [comp_ofIntegral, comp_ofIntegral]
  rfl

namespace HeightPresentation

variable {π : O} {q : ℕ} {z : RationalSection F M N U}

/-- Pull back the actual numerator and keep both rank exponents and the denominator power. -/
def baseChange (P : HeightPresentation π q z) (φ : R →ₐ[O] S) :
    HeightPresentation π q (RationalSection.baseChange φ U z) where
  exponent := P.exponent
  representative := Hom.openBaseChange φ U P.representative
  numeratorHeight := P.numeratorHeight
  denominatorHeight := P.denominatorHeight
  numerator := P.numerator.openBaseChange φ
  denominator := by
    have h := P.denominator.openBaseChange φ
    simpa only [Hom.openBaseChange_scalarHom] using h
  represents := by
    have h := congrArg (RationalSection.baseChange φ U) P.represents
    simpa only [map_smul, baseChange_ofIntegral φ U] using h

@[simp]
theorem index_baseChange (P : HeightPresentation π q z) (φ : R →ₐ[O] S) :
    (P.baseChange φ).index = P.index := rfl

/-- Integral conjugation uses the same numerator and denominator heights. -/
def transportIso (P : HeightPresentation π q z) (a : Iso M M') (b : Iso N N') :
    HeightPresentation π q (RationalSection.transportIso a b U z) where
  exponent := P.exponent
  representative := Hom.isoTransport
    (a.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
    (b.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))))
    P.representative
  numeratorHeight := P.numeratorHeight
  denominatorHeight := P.denominatorHeight
  numerator := P.numerator.isoTransport _ _
  denominator := by
    let aU := a.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U)))
    exact Hom.hasHeight_of_isoSquare _ _ aU aU
      (aU.hom.comp_scalarHom _).symm P.denominator
  represents := by
    have h := congrArg (RationalSection.transportIso a b U) P.represents
    simpa only [map_smul, transportIso_ofIntegral] using h

@[simp]
theorem index_transportIso (P : HeightPresentation π q z) (a : Iso M M') (b : Iso N N') :
    (P.transportIso a b).index = P.index := rfl

end HeightPresentation

namespace HasHeightFunction

variable {π : O} {q : ℕ} {z : RationalSection F M N U} {h : U → ℤ}

/-- Under arbitrary coefficient extension the verified height is pulled back on spectra. -/
theorem baseChange (hz : HasHeightFunction π q z h) (φ : R →ₐ[O] S) :
    HasHeightFunction π q (RationalSection.baseChange φ U z) (h ∘ coefficientOpenPoint φ U) := by
  intro x
  obtain ⟨V, hx, i, P, hP⟩ := hz (coefficientOpenPoint φ U x)
  have e := (restrict_baseChange φ i z).symm
  refine ⟨(coefficientOpenMap φ).obj V, hx, (coefficientOpenMap φ).map i, e ▸ P.baseChange φ, ?_⟩
  intro y
  rw [HeightPresentation.index_cast, HeightPresentation.index_baseChange]
  exact hP (coefficientOpenPoint φ V y)

/-- Conjugating by integral isomorphisms preserves the verified height. -/
theorem transportIso (hz : HasHeightFunction π q z h) (a : Iso M M') (b : Iso N N') :
    HasHeightFunction π q (RationalSection.transportIso a b U z) h := by
  intro x
  obtain ⟨V, hx, i, P, hP⟩ := hz x
  have e := (restrict_transportIso a b i z).symm
  refine ⟨V, hx, i, e ▸ P.transportIso a b, ?_⟩
  intro y
  rw [HeightPresentation.index_cast, HeightPresentation.index_transportIso]
  exact hP y

end HasHeightFunction
end RationalSection

end Langlands.FormalGroup.ModuleLaw
