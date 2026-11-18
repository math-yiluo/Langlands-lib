import Langlands.Geometry.FormalGroup.RationalSectionCoefficientCoherence
import Langlands.Geometry.FormalGroup.RationalSectionIsoTransport

/-! # Coefficient coherence for local quasi-isogenies and invertible sections -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory TopologicalSpace AlgebraicGeometry

variable {O : Type u} [CommRing O]
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O T]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {U : Opens (PrimeSpectrum R)}

/-- The natural comparison of successive and composite inverse-image functors on opens. -/
def coefficientOpenMapCompIso (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T) :
    coefficientOpenMap φ ⋙ coefficientOpenMap ψ ≅ coefficientOpenMap (ψ.comp φ) :=
  NatIso.ofComponents (fun V => eqToIso (coefficientOpenMap_comp_obj φ ψ V))
    (fun _ => Subsingleton.elim _ _)

@[simp]
theorem coefficientOpenMapCompIso_hom_app (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T)
    (V : Opens (PrimeSpectrum R)) :
    (coefficientOpenMapCompIso φ ψ).hom.app V = eqToHom (coefficientOpenMap_comp_obj φ ψ V) :=
  rfl

namespace RationalSection

/-- Coefficient pullback commutes with conjugation by the two integral comparisons. -/
theorem baseChange_transportIso (φ : R →ₐ[O] S) (a : Iso M M') (b : Iso N N')
    (z : RationalSection F M N U) :
    baseChange φ U (transportIso a b U z) =
      transportIso (a.map φ) (b.map φ) ((coefficientOpenMap φ).obj U) (baseChange φ U z) := by
  change baseChange φ U (comp (ofHom b.hom U) (comp z (ofHom a.inv U))) =
    comp (ofHom (b.hom.map φ) _) (comp (baseChange φ U z) (ofHom (a.inv.map φ) _))
  simp only [baseChange_comp, baseChange_ofHom]

end RationalSection

namespace LocalQuasiIsogeny

variable {π : O}

@[simp]
theorem baseChange_idOn (φ : R →ₐ[O] S) (hπ : algebraMap O F π ≠ 0)
    (hM : M.IsPiDivisible π) :
    (idOn π hπ M hM U).baseChange φ =
      idOn π hπ (M.map φ) (hM.map φ) ((coefficientOpenMap φ).obj U) := by
  apply ext
  exact RationalSection.baseChange_id φ U

theorem baseChange_transportIso (z : LocalQuasiIsogeny F π M N U)
    (φ : R →ₐ[O] S) (a : Iso M M') (b : Iso N N') :
    (z.transportIso a b).baseChange φ = (z.baseChange φ).transportIso (a.map φ) (b.map φ) := by
  apply ext
  exact RationalSection.baseChange_transportIso φ a b z.val

/-- Pullback by the identity coefficient map, followed by the canonical comparisons. -/
theorem baseChange_identity_transport (z : LocalQuasiIsogeny F π M N U) :
    (z.baseChange (AlgHom.id O R)).transportIso (mapIdIso M) (mapIdIso N) = z := by
  apply ext
  exact RationalSection.baseChange_identity_transport U z.val

/-- Successive coefficient pullbacks agree with pullback by the composite coefficient map. -/
theorem baseChange_composite_transport (z : LocalQuasiIsogeny F π M N U)
    (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T) :
    ((z.baseChange φ).baseChange ψ).transportIso (mapCompIso M φ ψ) (mapCompIso N φ ψ) =
      (z.baseChange (ψ.comp φ)).restrict ((coefficientOpenMapCompIso φ ψ).hom.app U) := by
  apply ext
  exact RationalSection.baseChange_composite_transport φ ψ U z.val

end LocalQuasiIsogeny

namespace RationalSectionIso

theorem baseChange_transportIso (e : RationalSectionIso F M N U)
    (φ : R →ₐ[O] S) (a : Iso M M') (b : Iso N N') :
    (e.transportIso a b).baseChange φ = (e.baseChange φ).transportIso (a.map φ) (b.map φ) := by
  apply ext
  exact RationalSection.baseChange_transportIso φ a b e.hom

/-- Pullback by the identity coefficient map, followed by the canonical comparisons. -/
theorem baseChange_identity_transport (e : RationalSectionIso F M N U) :
    (e.baseChange (AlgHom.id O R)).transportIso (mapIdIso M) (mapIdIso N) = e := by
  apply ext
  exact RationalSection.baseChange_identity_transport U e.hom

/-- Successive coefficient pullbacks agree with pullback by the composite coefficient map. -/
theorem baseChange_composite_transport (e : RationalSectionIso F M N U)
    (φ : R →ₐ[O] S) (ψ : S →ₐ[O] T) :
    ((e.baseChange φ).baseChange ψ).transportIso (mapCompIso M φ ψ) (mapCompIso N φ ψ) =
      (e.baseChange (ψ.comp φ)).restrict ((coefficientOpenMapCompIso φ ψ).hom.app U) := by
  apply ext
  exact RationalSection.baseChange_composite_transport φ ψ U e.hom

end RationalSectionIso
end Langlands.FormalGroup.ModuleLaw
