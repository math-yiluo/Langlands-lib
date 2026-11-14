import Langlands.Geometry.Building.RelativeDerivativeRootPairing
import Langlands.GroupScheme.Reductive.RootDatumRationalBase
import Langlands.LinearAlgebra.RootPairingBaseComparison

/-! # Actual integral Cartan matrices and arbitrary full derivative bases -/

noncomputable section

universe u uA

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)
  {A : Type uA} [AddTorsor (TranslationSpace i) A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
  (hderiv : derivativeRoots Ψ = Set.range (rootForm i))

/-- The full relative roots index all apartment derivatives through evaluation. -/
def relativeDerivativeRootIndexEquiv : relativeRoots i ≃ derivativeRoots Ψ :=
  Equiv.ofBijective
    (fun α => ⟨rootForm i α, hderiv.symm ▸ Set.mem_range_self α⟩)
    ⟨by
      intro α β h
      apply (RelativeRootSystem.rootEmbedding i hS).injective
      apply relativeRootForm_injective i hS
      change relativeRootForm i ⟨toRat α.val, _⟩ =
        relativeRootForm i ⟨toRat β.val, _⟩
      rw [relativeRootForm_toRat, relativeRootForm_toRat]
      exact congrArg Subtype.val h,
      by
      intro a
      obtain ⟨α, hα⟩ : ∃ α : relativeRoots i, rootForm i α = a.val := by
        rw [← Set.mem_range, ← hderiv]
        exact a.property
      exact ⟨α, Subtype.ext hα⟩⟩

@[simp] theorem relativeDerivativeRootIndexEquiv_val (α : relativeRoots i) :
    (relativeDerivativeRootIndexEquiv i hS hderiv α).val = rootForm i α :=
  rfl

/-- The rational span equivalence preserves every full root vector. -/
theorem relativeDerivativeRootEquiv_rootVector (α : relativeRoots i) :
    relativeDerivativeRootEquiv i hS hΨ hderiv (RelativeRootSystem.rootVector i α) =
      hΨ.rationalDerivativePairing.root (relativeDerivativeRootIndexEquiv i hS hderiv α) := by
  apply Subtype.ext
  rw [relativeDerivativeRootEquiv_coe,
    IsAffineRootSystemWithRankZero.rationalDerivativePairing_coe_root,
    relativeDerivativeRootIndexEquiv_val]
  exact relativeRootForm_toRat i α

variable [Mono i.hom.hom.left]

local instance (D : RelativeRootReflectionData i)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hS hfinite).IsRootSystem :=
  D.rootPairing_isRootSystem hS hfinite

local instance (D : RelativeRootReflectionData i)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hS hfinite).IsCrystallographic :=
  D.rootPairing_isCrystallographic hS hfinite

/-- Full-root transport identifies the assembled actual pairing and the
rational derivative pairing, including their coroots. -/
def relativeDerivativePairingEquiv (D : RelativeRootReflectionData i)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hS hfinite).Equiv hΨ.rationalDerivativePairing := by
  letI := hΨ.finite_derivativeRoots.to_subtype
  exact RootPairing.Equiv.mk' _ _
    (relativeDerivativeRootEquiv i hS hΨ hderiv)
    (relativeDerivativeRootIndexEquiv i hS hderiv)
    (relativeDerivativeRootEquiv_rootVector i hS hΨ hderiv)

variable {J : Type*}
  {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
  (hP : IsRootDatumOf i P) (hfinite : (relativeRoots i).Finite) [P.IsReduced]

/-- Compare a supplied integral simple support with any full derivative base.
The Weyl comparison permits the two bases to be chosen independently. -/
def integralDerivativeBaseEquiv (b : P.Base) (B : hΨ.rationalDerivativePairing.Base) :
    b.support ≃ B.support := by
  letI := hfinite.fintype
  letI := hΨ.finite_derivativeRoots.fintype
  exact (hP.rationalBaseSupportEquiv hS hfinite b).trans
    (Langlands.LinearAlgebra.RootPairingBaseComparison.rootTransportBaseEquiv
      (hP.relativeRootReflectionData.rootPairing hS hfinite)
      hΨ.rationalDerivativePairing (hP.rationalBase hS hfinite b) B
      (relativeDerivativeRootEquiv i hS hΨ hderiv)
      (relativeDerivativeRootIndexEquiv i hS hderiv)
      (relativeDerivativeRootEquiv_rootVector i hS hΨ hderiv))

/-- The comparison with any derivative base preserves the original integer
Cartan matrix, with the root and coroot index order unchanged. -/
theorem cartanMatrix_integralDerivativeBaseEquiv
    (b : P.Base) (B : hΨ.rationalDerivativePairing.Base) (a c : b.support) :
    B.cartanMatrix (integralDerivativeBaseEquiv i hS hΨ hderiv hP hfinite b B a)
      (integralDerivativeBaseEquiv i hS hΨ hderiv hP hfinite b B c) =
      b.cartanMatrix a c := by
  let := hfinite.fintype
  let := hΨ.finite_derivativeRoots.fintype
  exact (Langlands.LinearAlgebra.RootPairingBaseComparison.cartanMatrix_rootTransportBaseEquiv
      (hP.relativeRootReflectionData.rootPairing hS hfinite)
      hΨ.rationalDerivativePairing (hP.rationalBase hS hfinite b) B
      (relativeDerivativeRootEquiv i hS hΨ hderiv)
      (relativeDerivativeRootIndexEquiv i hS hderiv)
      (relativeDerivativeRootEquiv_rootVector i hS hΨ hderiv)
      (hP.rationalBaseSupportEquiv hS hfinite b a)
      (hP.rationalBaseSupportEquiv hS hfinite b c)).trans
    (hP.cartanMatrix_rationalBaseSupportEquiv hS hfinite b a c)

end Langlands.Geometry.Building
