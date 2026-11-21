import Langlands.Geometry.FormalGroup.FieldScalarIsogenyPresentation
import Langlands.Geometry.FormalGroup.RationalHeightProof
import Langlands.Geometry.FormalGroup.RationalHeightBaseChange
import Langlands.Geometry.FormalGroup.RationalHeightIso

/-! # Signed height of an invertible tensor over an arbitrary affine base -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.QuasiIsogeny

open TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {R S : Type v} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable (e : QuasiIsogeny F M N) {π : O}

/-- An integral map clearing a uniformizer denominator is an actual isogeny over the base. -/
theorem isIsogeny_of_clearsDenominator_overRing (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) {n : ℕ} {f : Hom M N}
    (hf : (algebraMap O F π) ^ n • e.hom = RationalHom.ofHom f) : f.IsIsogeny := by
  obtain ⟨m, g, hg⟩ := RationalHom.exists_uniformizerPower_ofHom hπ e.inv
  exact (e.scalarComposites hπ hM hN hf hg).elim (Hom.isIsogeny_of_scalarComposites_overRing hM hN)

/-- Choose an actual isogeny numerator of an invertible tensor over any coefficient ring. -/
def scalarIsogenyPresentationOverRing (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    RationalHom.ScalarIsogenyPresentation π e.hom :=
  let p := RationalHom.exists_uniformizerPower_ofHom hπ e.hom
  let hp := p.choose_spec.choose_spec
  ⟨p.choose, p.choose_spec.choose, e.isIsogeny_of_clearsDenominator_overRing hπ hM hN hp, hp⟩

/-- The section of the invertible tensor is an actual local quasi-isogeny on the affine base. -/
def toLocalQuasiIsogeny (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) : LocalQuasiIsogeny F π M N ⊤ :=
  (e.scalarIsogenyPresentationOverRing hπ hM hN).toLocalQuasiIsogeny
    (by simpa only [map_zero] using (IsFractionRing.injective O F).ne hπ.ne_zero) hM hN

section Height

variable [Finite (IsLocalRing.ResidueField O)]

local notation "q" => Nat.card (IsLocalRing.ResidueField O)

/-- There is a unique height for the actual section of an invertible tensor. -/
theorem existsUnique_heightFunction (hπ : Irreducible π) {d j : ℕ}
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j) :
    ∃! k : (⊤ : Opens (PrimeSpectrum R)) → ℤ,
      RationalSection.HasHeightFunction π q (RationalSection.ofGlobal e.hom) k :=
  rationalHeightExistenceUniqueness O F R π hπ σ τ M N d j hM hN ⊤
    (e.toLocalQuasiIsogeny hπ hM.piDivisible hN.piDivisible)

/-- The canonical signed height function computed from the actual local kernel ranks. -/
def heightFunction (hπ : Irreducible π) {d j : ℕ}
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j) :
    (⊤ : Opens (PrimeSpectrum R)) → ℤ :=
  (e.existsUnique_heightFunction hπ hM hN).exists.choose

/-- The chosen function is locally the actual difference of rank exponents. -/
theorem hasHeightFunction (hπ : Irreducible π) {d j : ℕ}
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j) :
    RationalSection.HasHeightFunction π q (RationalSection.ofGlobal e.hom)
      (e.heightFunction hπ hM hN) :=
  (e.existsUnique_heightFunction hπ hM hN).exists.choose_spec

/-- The rank presentation characterizes the canonical function, including over disconnected bases. -/
theorem heightFunction_eq (hπ : Irreducible π) {d j : ℕ}
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j)
    {k : (⊤ : Opens (PrimeSpectrum R)) → ℤ}
    (hk : RationalSection.HasHeightFunction π q (RationalSection.ofGlobal e.hom) k) :
    e.heightFunction hπ hM hN = k :=
  (e.existsUnique_heightFunction hπ hM hN).unique (e.hasHeightFunction hπ hM hN) hk

/-- Coefficient extension of the section pulls the height function back on spectra. -/
theorem heightFunction_eq_of_map (hπ : Irreducible π) {d j : ℕ}
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j) (φ : R →ₐ[O] S)
    (e' : QuasiIsogeny F (M.map φ) (N.map φ))
    (he : e'.hom = RationalHom.map φ e.hom) :
    e'.heightFunction hπ (hM.map φ) (hN.map φ) =
      e.heightFunction hπ hM hN ∘ coefficientOpenPoint φ ⊤ := by
  apply e'.heightFunction_eq hπ (hM.map φ) (hN.map φ)
  have hh := (e.hasHeightFunction hπ hM hN).baseChange φ
  have hc : RationalSection.baseChange φ ⊤ (RationalSection.ofGlobal e.hom) =
      RationalSection.ofGlobal (RationalHom.map φ e.hom) :=
    RationalSection.baseChange_ofGlobalOn φ ⊤ e.hom
  rw [he]
  exact hc ▸ hh

/-- Integral isomorphisms at both ends preserve the canonical function. -/
theorem heightFunction_eq_of_isoTransport (hπ : Irreducible π) {d j : ℕ}
    (hM : M.HasPiHeight π q d) (hN : N.HasPiHeight π q j)
    (a : Iso M M') (b : Iso N N') (e' : QuasiIsogeny F M' N')
    (he : e'.hom = RationalHom.isoTransport a b e.hom) :
    e'.heightFunction hπ (a.hasPiHeight π hM) (b.hasPiHeight π hN) =
      e.heightFunction hπ hM hN := by
  apply e'.heightFunction_eq hπ (a.hasPiHeight π hM) (b.hasPiHeight π hN)
  exact he.symm ▸ ((e.hasHeightFunction hπ hM hN).ofGlobal_isoTransport a b)

end Height

end Langlands.FormalGroup.ModuleLaw.QuasiIsogeny
