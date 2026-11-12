import Langlands.ClassFieldTheory.Local.CommonClosureCandidateTransport

/-! # Conjugation transport on prescribed intermediate Weil groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.LocalClassField.CommonClosureTransport

open Weil Weil.Local LocalFactor.RankOne

universe u v

variable {p : ℕ} [Fact p.Prime]

/-- Over an algebra structure induced by a field isomorphism the norm is its inverse. -/
theorem norm_extensionAlgebra_equiv
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    (f : F.Carrier ≃ₐ[Padic p] E.Carrier) (x : E.Carrier) :
    letI := extensionAlgebra F E f.toAlgHom
    Algebra.norm F.Carrier x = f.symm x := by
  let := extensionAlgebra F E f.toAlgHom
  let e : E.Carrier ≃ₐ[F.Carrier] F.Carrier :=
    AlgEquiv.ofRingEquiv (f := f.symm.toRingEquiv) (fun x => f.symm_apply_apply x)
  have h := Algebra.norm_eq_of_algEquiv e x
  rw [Algebra.norm_self] at h
  exact h.symm

/-- The norm comparison for an isomorphism is the inverse field isomorphism. -/
theorem reciprocityUnits_compatible_closure_equiv
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    (f : F.Carrier ≃ₐ[Padic p] E.Carrier)
    (θ : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure E.Carrier)
    (hθ : ∀ x : F.Carrier, θ (algebraMap F.Carrier _ x) =
      algebraMap E.Carrier _ (f x))
    (c : localWeilGroup E → localWeilGroup F)
    (hc : ∀ (y : localWeilGroup E) (x : AlgebraicClosure F.Carrier),
      θ (AlgEquiv.toAlgHom (localProjection F (c y)) x) =
        AlgEquiv.toAlgHom (localProjection E y) (θ x))
    (eF : ReciprocityCandidate F)
    (hF : GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF)
    (eE : ReciprocityCandidate E)
    (hE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (y : localWeilGroup E) :
    reciprocityUnits F eF (c y) =
      Units.map f.symm.toRingEquiv.toMonoidHom (reciprocityUnits E eE y) := by
  rw [reciprocityUnits_compatible_closure F E f.toAlgHom θ hθ c hc eF hF eE hE y]
  apply Units.ext
  exact norm_extensionAlgebra_equiv F E f _

variable (F : PadicField.{u} p) (E : FiniteIntermediateExtension F.Carrier)

local instance conjugationBaseCharZero : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
local instance conjugationSourceAlgebra : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra

/-- The conjugation isomorphism on actual intermediate fields over the specified p-adic base. -/
def intermediateConjugationEquiv (σ : Field.absoluteGaloisGroup F.Carrier) :
    letI := ((E.conj σ).asPadicField (p := p)).algebra
    E.field ≃ₐ[Padic p] (E.conj σ).field := by
  letI := ((E.conj σ).asPadicField (p := p)).algebra
  refine { toRingEquiv := (IntermediateField.equivMap E.field (AlgEquiv.toAlgHom σ)).toRingEquiv
           commutes' := ?_ }
  intro x
  apply Subtype.ext
  exact σ.commutes (algebraMap (Padic p) F.Carrier x)

/-- Actual conjugation in the ambient Weil group in standalone coordinates. -/
def intermediateWeilConjugation (w : localWeilGroup F) :
    localWeilGroup (E.asPadicField (p := p)) →ₜ*
      localWeilGroup ((E.conj (localProjection F w)).asPadicField (p := p)) := by
  change localWeilGroup (E.asPadicField (p := p)) →ₜ*
    localWeilGroup ((E.conj (Weil.projection (localResidueDegree F) w)).asPadicField (p := p))
  exact ((intermediateWeilEquiv F
    (E.conj (Weil.projection (localResidueDegree F) w))).symm : _ →ₜ* _).comp
      ((E.weilConjugation (localResidueDegree F) w).comp
        (intermediateWeilEquiv F E : _ →ₜ* _))

/-- The standalone conjugation has the expected ambient projection. -/
theorem intermediateWeilConjugation_projection (w : localWeilGroup F)
    (y : localWeilGroup (E.asPadicField (p := p))) :
    intermediateGaloisMap F (E.conj (localProjection F w))
      (localProjection ((E.conj (localProjection F w)).asPadicField (p := p))
        (intermediateWeilConjugation F E w y)) =
      localProjection F w *
        intermediateGaloisMap F E (localProjection (E.asPadicField (p := p)) y) *
          (localProjection F w)⁻¹ := by
  change intermediateGaloisMap F (E.conj (localProjection F w))
    (localProjection ((E.conj (localProjection F w)).asPadicField (p := p))
      ((intermediateWeilEquiv F (E.conj (localProjection F w))).symm
        (E.weilConjugation (localResidueDegree F) w (intermediateWeilEquiv F E y)))) = _
  rw [intermediateWeilEquiv_symm_projection]
  rfl

/-- Geometric reciprocity carries actual Weil conjugation to field conjugation. -/
theorem reciprocityUnits_intermediateWeilConjugation (w : localWeilGroup F)
    (eE : ReciprocityCandidate (E.asPadicField (p := p)))
    (hE : GeometricWeilReciprocityRelation (E.asPadicField (p := p))
      (CommonClosure.canonicalData F E) eE)
    (eL : ReciprocityCandidate ((E.conj (localProjection F w)).asPadicField (p := p)))
    (hL : GeometricWeilReciprocityRelation
      ((E.conj (localProjection F w)).asPadicField (p := p))
      (CommonClosure.canonicalData F (E.conj (localProjection F w))) eL)
    (y : localWeilGroup (E.asPadicField (p := p))) :
    reciprocityUnits ((E.conj (localProjection F w)).asPadicField (p := p)) eL
      (intermediateWeilConjugation F E w y) =
      E.unitsConjugation (localProjection F w)
        (reciprocityUnits (E.asPadicField (p := p)) eE y) := by
  let σ : Gal(AlgebraicClosure F.Carrier/F.Carrier) := localProjection F w
  let L := E.conj σ
  let := (L.asPadicField (p := p)).algebra
  let f := (intermediateConjugationEquiv F E σ).symm
  let θ : AlgebraicClosure L.field ≃+* AlgebraicClosure E.field :=
    ((intermediateClosureEquiv F L).toRingEquiv.trans σ.symm.toRingEquiv).trans
      (intermediateClosureEquiv F E).symm.toRingEquiv
  have hθ' (x : AlgebraicClosure L.field) :
      intermediateClosureEquiv F E (θ x) = σ.symm (intermediateClosureEquiv F L x) :=
    (intermediateClosureEquiv F E).apply_symm_apply _
  have hθ (x : L.field) :
      θ (algebraMap L.field _ x) = algebraMap E.field _ (f x) := by
    apply (intermediateClosureEquiv F E).injective
    rw [hθ', intermediateClosureEquiv_algebraMap, intermediateClosureEquiv_algebraMap]
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (congrArg Subtype.val ((intermediateConjugationEquiv F E σ).apply_symm_apply x)).symm
  have hc (y : localWeilGroup (E.asPadicField (p := p))) (x : AlgebraicClosure L.field) :
      θ (AlgEquiv.toAlgHom (localProjection (L.asPadicField (p := p))
        (intermediateWeilConjugation F E w y)) x) =
        AlgEquiv.toAlgHom (localProjection (E.asPadicField (p := p)) y) (θ x) := by
    apply (intermediateClosureEquiv F E).injective
    rw [hθ', ← intermediateClosureEquiv_galoisMap,
      ← intermediateClosureEquiv_galoisMap, intermediateWeilConjugation_projection, hθ']
    change σ.symm (σ (AlgEquiv.toAlgHom (intermediateGaloisMap F E
      (localProjection (E.asPadicField (p := p)) y))
        (σ.symm (intermediateClosureEquiv F L x)))) = _
    rw [AlgEquiv.symm_apply_apply]
  exact reciprocityUnits_compatible_closure_equiv (L.asPadicField (p := p))
    (E.asPadicField (p := p)) f θ hθ (intermediateWeilConjugation F E w) hc eL hL eE hE y

end Langlands.LocalClassField.CommonClosureTransport
