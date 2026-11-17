import Langlands.Geometry.FormalGroup.RationalSectionGlobal

/-! # Actual integral-isomorphism transport of local quasi-isogenies -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower
variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}

namespace Hom

/-- Transport an actual integral isogeny using the actual isomorphism of its arrow. -/
theorem IsIsogeny.transportIso {f : Hom M N} (hf : f.IsIsogeny)
    (a : Iso M M') (b : Iso N N') : (b.hom.comp (f.comp a.inv)).IsIsogeny := by
  apply isIsogeny_of_isoSquare f (b.hom.comp (f.comp a.inv)) a b
  · rw [comp_assoc, comp_assoc, a.inv_hom, comp_id]
  · exact hf

end Hom

namespace RationalSection

/-- Conjugate an actual rational section by integral isomorphisms. -/
def transportIso (a : Iso M M') (b : Iso N N') (U : Opens (PrimeSpectrum R)) :
    RationalSection F M N U →ₗ[F] RationalSection F M' N' U where
  toFun z := comp (ofHom b.hom U) (comp z (ofHom a.inv U))
  map_add' z w := by simp only [add_comp, comp_add]
  map_smul' c z := by simp only [smul_comp, comp_smul, RingHom.id_apply]

@[simp]
theorem restrict_transportIso (a : Iso M M') (b : Iso N N')
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) (z : RationalSection F M N U) :
    restrict i (transportIso a b U z) = transportIso a b V (restrict i z) := by
  change restrict i (comp (ofHom b.hom U) (comp z (ofHom a.inv U))) = _
  rw [restrict_comp_hom, restrict_comp_hom, restrict_ofHom, restrict_ofHom]
  rfl

@[simp]
theorem transportIso_symm_transportIso (a : Iso M M') (b : Iso N N')
    (U : Opens (PrimeSpectrum R)) (z : RationalSection F M N U) :
    transportIso a.symm b.symm U (transportIso a b U z) = z := by
  change comp (ofHom b.inv U)
    (comp (comp (ofHom b.hom U) (comp z (ofHom a.inv U))) (ofHom a.hom U)) = z
  simp only [← comp_assoc, comp_ofHom, b.inv_hom, ofHom_id, id_comp]
  rw [comp_assoc, comp_ofHom, a.inv_hom, ofHom_id, comp_id]

/-- Actual integral isomorphisms induce a linear equivalence of rational-section modules. -/
def transportIsoEquiv (a : Iso M M') (b : Iso N N') (U : Opens (PrimeSpectrum R)) :
    RationalSection F M N U ≃ₗ[F] RationalSection F M' N' U :=
  { transportIso a b U with
    invFun := transportIso a.symm b.symm U
    left_inv := transportIso_symm_transportIso a b U
    right_inv := transportIso_symm_transportIso a.symm b.symm U }

/-- Transport the actual local numerator with the same witnessing neighbourhood and exponent. -/
theorem IsLocallyScalarIsogeny.transportIso {π : O} {U : Opens (PrimeSpectrum R)}
    {z : RationalSection F M N U} (hz : IsLocallyScalarIsogeny π z)
    (a : Iso M M') (b : Iso N N') : IsLocallyScalarIsogeny π (transportIso a b U z) := by
  intro x hx
  obtain ⟨V, hxV, i, n, f, hf, heq⟩ := hz x hx
  let φ : R →ₐ[O] ((coefficientStructurePresheaf R).obj (op V)) :=
    IsScalarTower.toAlgHom O R _
  refine ⟨V, hxV, i, n, (b.map φ).hom.comp (f.comp (a.map φ).inv),
    hf.transportIso (a.map φ) (b.map φ), ?_⟩
  rw [restrict_transportIso]
  change (algebraMap O F π) ^ n •
    comp (RationalSection.ofHom b.hom V)
      (comp (RationalSection.restrict i z) (RationalSection.ofHom a.inv V)) = _
  rw [← comp_smul, ← smul_comp, heq]
  change comp (RationalSection.ofIntegral V (b.hom.map φ))
    (comp (RationalSection.ofIntegral V f) (RationalSection.ofIntegral V (a.inv.map φ))) = _
  rw [comp_ofIntegral, comp_ofIntegral]
  rfl

/-- Integral-isomorphism transport preserves and reflects the local isogeny condition. -/
theorem isLocallyScalarIsogeny_transportIso_iff {π : O} {U : Opens (PrimeSpectrum R)}
    (a : Iso M M') (b : Iso N N') (z : RationalSection F M N U) :
    IsLocallyScalarIsogeny π (transportIso a b U z) ↔ IsLocallyScalarIsogeny π z := by
  constructor
  · intro h
    simpa only [transportIso_symm_transportIso] using h.transportIso a.symm b.symm
  · exact fun h => h.transportIso a b

end RationalSection

namespace LocalQuasiIsogeny

/-- The actual identity local quasi-isogeny on an arbitrary open set. -/
def idOn (π : O) (hπ : algebraMap O F π ≠ 0) (M : ModuleLaw O R σ)
    (hM : M.IsPiDivisible π) (U : Opens (PrimeSpectrum R)) :
    LocalQuasiIsogeny F π M M U where
  scalar_ne_zero := hπ
  source_divisible := hM
  target_divisible := hM
  val := RationalSection.id M U
  isLocal := RationalSection.IsLocallyScalarIsogeny.id π M U

/-- Transport an actual local quasi-isogeny along actual global integral isomorphisms. -/
def transportIso {π : O} {U : Opens (PrimeSpectrum R)}
    (z : LocalQuasiIsogeny F π M N U) (a : Iso M M') (b : Iso N N') :
    LocalQuasiIsogeny F π M' N' U where
  scalar_ne_zero := z.scalar_ne_zero
  source_divisible := a.isPiDivisible π z.source_divisible
  target_divisible := b.isPiDivisible π z.target_divisible
  val := RationalSection.transportIso a b U z.val
  isLocal := z.isLocal.transportIso a b

@[simp]
theorem restrict_idOn (π : O) (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π)
    {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) :
    (idOn π hπ M hM U).restrict i = idOn π hπ M hM V := by
  apply ext
  exact RationalSection.restrict_id_section i

@[simp]
theorem restrict_transportIso {π : O} {U V : Opens (PrimeSpectrum R)}
    (z : LocalQuasiIsogeny F π M N U) (a : Iso M M') (b : Iso N N') (i : V ⟶ U) :
    (z.transportIso a b).restrict i = (z.restrict i).transportIso a b := by
  apply ext
  exact RationalSection.restrict_transportIso a b i z.val

@[simp]
theorem transportIso_symm_transportIso {π : O} {U : Opens (PrimeSpectrum R)}
    (z : LocalQuasiIsogeny F π M N U) (a : Iso M M') (b : Iso N N') :
    (z.transportIso a b).transportIso a.symm b.symm = z := by
  apply ext
  exact RationalSection.transportIso_symm_transportIso a b U z.val

/-- An actual equivalence of local quasi-isogenies induced by integral isomorphisms. -/
def transportIsoEquiv {π : O} (a : Iso M M') (b : Iso N N')
    (U : Opens (PrimeSpectrum R)) : LocalQuasiIsogeny F π M N U ≃ LocalQuasiIsogeny F π M' N' U where
  toFun z := z.transportIso a b
  invFun z := z.transportIso a.symm b.symm
  left_inv z := transportIso_symm_transportIso z a b
  right_inv z := transportIso_symm_transportIso z a.symm b.symm

end LocalQuasiIsogeny
end Langlands.FormalGroup.ModuleLaw
