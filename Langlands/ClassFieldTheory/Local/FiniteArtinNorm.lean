import Langlands.ClassFieldTheory.Local.FiniteGaloisArtinRestriction
import Langlands.ClassFieldTheory.Local.CommonClosureReciprocityConstruction

/-! # Finite Artin symbols and norms through arbitrary intermediate fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.LocalClassField.FiniteQuotientTransport

open Weil.Local LocalFactor.RankOne ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]
  [Algebra D (AlgebraicClosure F.Carrier)]
  [IsScalarTower F.Carrier D (AlgebraicClosure F.Carrier)]

/-- The finite restriction of a geometric Weil projection is the inverse-unit
carry symbol of its reciprocity value. -/
theorem closureFiniteRestriction_reciprocityUnits
    (e : ReciprocityCandidate F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData e)
    (w : localWeilGroup F) :
    Abelianization.of (closureFiniteRestriction F D (localProjection F w)) =
      FiniteArtinSymbol.abelianizedArtinSymbol F D (reciprocityUnits F e w)⁻¹ := by
  let := F.canonicalTopologicalData.topology
  have h := closureFiniteAbelianRestriction_geometric F D F.canonicalTopologicalData
    (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e)
    he.2 (reciprocityUnits F e w)
  change closureFiniteAbelianRestriction F D
    (WeilQuotients.toGroupAbelianization (localResidueDegree F)
      (e.symm (e (WeilQuotients.projection (localResidueDegree F) w)))) = _ at h
  rw [e.symm_apply_apply] at h
  change closureFiniteAbelianRestriction F D
    (absoluteAbelianizationProjection F.Carrier (localProjection F w)) = _ at h
  rw [closureFiniteAbelianRestriction_projection] at h
  exact h

end Langlands.LocalClassField.FiniteQuotientTransport

namespace Langlands.ClassFieldTheory.Local.FiniteArtinSymbol

open LocalClassField LocalClassField.FiniteQuotientTransport Weil.Local LocalFactor.RankOne

variable {p : ℕ} [Fact p.Prime]
  (F E : PadicField.{u} p) (D : Type u) [Field D]
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [Algebra F.Carrier D] [Algebra E.Carrier D] [IsScalarTower F.Carrier E.Carrier D]
  [FiniteDimensional F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier D] [FiniteDimensional E.Carrier D]
  [IsGalois F.Carrier D] [IsGalois E.Carrier D]

/-- Commutativity of the finite arithmetic Artin square for the determinant
norm and the actual restriction-of-scalars map. -/
def ArtinNormCompatibility : Prop :=
  (Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)).comp
      (abelianizedArtinSymbol E D) =
    (abelianizedArtinSymbol F D).comp (normUnits F.Carrier E.Carrier)

/-- The arithmetic finite Artin symbol sends the actual determinant norm to
restriction of scalars on Galois abelianizations. The middle field need not
be normal over the base field. -/
theorem abelianizedArtinSymbol_norm (a : E.Carrierˣ) :
    Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)
        (abelianizedArtinSymbol E D a) =
      abelianizedArtinSymbol F D (normUnits F.Carrier E.Carrier a) := by
  let f : F.Carrier →ₐ[Padic p] E.Carrier :=
    IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier
  let θ := extensionClosureEquiv F E f
  let j : D →ₐ[E.Carrier] AlgebraicClosure E.Carrier := IsAlgClosed.lift
  let : Algebra D (AlgebraicClosure E.Carrier) := j.toRingHom.toAlgebra
  let : IsScalarTower E.Carrier D (AlgebraicClosure E.Carrier) :=
    IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  let k : D →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    { toRingHom := θ.symm.toRingHom.comp j.toRingHom
      commutes' := by
        intro x
        apply θ.injective
        change θ (θ.symm (j (algebraMap F.Carrier D x))) =
          θ (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)
        rw [θ.apply_symm_apply]
        change j (algebraMap F.Carrier D x) =
          extensionClosureLift F E f (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)
        rw [extensionClosureLift_algebraMap, IsScalarTower.algebraMap_apply F.Carrier E.Carrier D,
          j.commutes]
        rfl }
  let : Algebra D (AlgebraicClosure F.Carrier) := k.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier D (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq (fun x => (k.commutes x).symm)
  have hk (x : D) : θ (k x) = j x := θ.apply_symm_apply _
  have hres (τ : Field.absoluteGaloisGroup E.Carrier) :
      closureFiniteRestriction F D (extensionGaloisMap F E f τ) =
        (closureFiniteRestriction E D τ).restrictScalars F.Carrier := by
    apply AlgEquiv.ext
    intro x
    apply k.injective
    apply θ.injective
    calc
      θ (k (closureFiniteRestriction F D (extensionGaloisMap F E f τ) x)) =
          θ (AlgEquiv.toAlgHom (extensionGaloisMap F E f τ) (k x)) :=
        congrArg θ (AlgEquiv.restrictNormal_commutes (extensionGaloisMap F E f τ) D x)
      _ = AlgEquiv.toAlgHom τ (θ (k x)) := extensionClosureLift_galoisMap F E f τ (k x)
      _ = AlgEquiv.toAlgHom τ (j x) := congrArg (AlgEquiv.toAlgHom τ) (hk x)
      _ = j (closureFiniteRestriction E D τ x) :=
        (AlgEquiv.restrictNormal_commutes τ D x).symm
      _ = θ (k ((closureFiniteRestriction E D τ).restrictScalars F.Carrier x)) :=
        (hk _).symm
  let eF := canonicalStandaloneReciprocity F
  let eE := canonicalStandaloneReciprocity E
  have heF := canonicalStandaloneReciprocity_geometric F
  have heE := canonicalStandaloneReciprocity_geometric E
  let := E.canonicalTopologicalData.topology
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (eE.symm a⁻¹)
  have hval : reciprocityUnits E eE y = a⁻¹ := by
    change eE (WeilQuotients.projection (localResidueDegree E) y) = _
    change (QuotientGroup.mk y : WeilQuotients.Abelianization (localResidueDegree E)) =
      eE.symm a⁻¹ at hy
    rw [show WeilQuotients.projection (localResidueDegree E) y = eE.symm a⁻¹ from hy,
      eE.apply_symm_apply]
  have hnorm := reciprocityUnits_extensionWeilMap F E f eF heF eE heE y
  have halg : extensionAlgebra F E f = (inferInstance : Algebra F.Carrier E.Carrier) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [halg] at hnorm
  change reciprocityUnits F eF (extensionWeilMap F E f y) =
    normUnits F.Carrier E.Carrier (reciprocityUnits E eE y) at hnorm
  have hF := closureFiniteRestriction_reciprocityUnits F D eF heF
    (extensionWeilMap F E f y)
  simp only [localProjection_extensionWeilMap, hres, hnorm, hval, map_inv, inv_inv] at hF
  have hE := closureFiniteRestriction_reciprocityUnits E D eE heE y
  simp only [hval, inv_inv] at hE
  calc
    _ = Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)
        (Abelianization.of (closureFiniteRestriction E D (localProjection E y))) :=
      congrArg (Abelianization.map (AlgEquiv.restrictScalarsHom F.Carrier)) hE.symm
    _ = _ := hF

/-- Finite arithmetic Artin symbols satisfy the actual norm square in a
compatible p-adic tower, without normality of the middle extension. -/
theorem artinNormCompatibility : ArtinNormCompatibility F E D := by
  ext a
  exact abelianizedArtinSymbol_norm F E D a

end Langlands.ClassFieldTheory.Local.FiniteArtinSymbol
