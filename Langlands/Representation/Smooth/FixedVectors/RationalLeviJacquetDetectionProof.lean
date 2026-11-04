import Langlands.Representation.Smooth.FixedVectors.RationalLeviJacquetDetectionStatement
import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof
import Langlands.Representation.Smooth.FixedVectors.RationalNormKernelDetectionProof
import Langlands.Representation.Smooth.FixedVectors.GroupEquivalenceGenerationProof
import Langlands.Representation.Tensor.SmoothSubquotients

/-! # Proof of fixed-vector detection through actual rational Levi points -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands

open GroupScheme Aubert.General.RationalPointFamily

universe u uV

/-- The intrinsic rational norm-kernel detector applies to a literal normalized
Jacquet subquotient through the canonical standard-Levi point homeomorphism. -/
theorem rationalLeviJacquetFixedVectorDetection :
    RationalLeviJacquetFixedVectorDetectionStatement.{u, uV} := by
  intro hfinite F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro T i ν I L hL
  let := hL.isAffineHom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  intro _ _ _ _ _ _ Nbar hN hMN hM hcompact K K0 hK hK0 hfactor g hcon
    A D hfin hgen hDA E hEirr hEsub hcoeff
  let M := levi i ν I
  let J := Aubert.General.normalizedJacquetFunctor (unipotent i ν I) M hN hMN
  let JA := J.obj A
  let JD := J.obj D
  let e := leviRationalPointHomeomorph i ν I
  let KL : Subgroup (rationalPoints L) :=
    (K.toSubgroup.comap M.subtype).comap e.toMonoidHom
  have hKback : KL.comap e.symm.toMonoidHom = K.toSubgroup.comap M.subtype := by
    ext m
    change e (e.symm m) ∈ K.toSubgroup.comap M.subtype ↔
      m ∈ K.toSubgroup.comap M.subtype
    rw [e.apply_symm_apply]
  obtain ⟨_, hgenJA, hJDA, hlift⟩ := normalizedJacquetFixedVectorBridge
    (rationalPoints G) (unipotent i ν I) M Nbar hN hMN hM hcompact
    K K0 hK hK0 hfactor g hcon A D hfin hgen hDA
  have hEJA : SmoothRep.IsSubquotient E JA :=
    smoothSubquotientTransitivity ℂ M JA JD E hEsub hJDA
  have hgenL : ∀ S : Subrepresentation (SmoothRep.pullback e JA).representation,
      fixedVectors (SmoothRep.pullback e JA).representation KL ≤ S.toSubmodule →
        S = ⊤ := by
    apply (fixedVectors_generate_comp_mulEquiv_iff JA.representation e.toMulEquiv KL).mpr
    change ∀ S : Subrepresentation JA.representation,
      fixedVectors JA.representation (KL.comap e.symm.toMonoidHom) ≤ S.toSubmodule → S = ⊤
    rwa [hKback]
  have hELirr : (SmoothRep.pullback e E).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff E.representation e).mpr hEirr
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hKL : IsCompact (KL : Set (rationalPoints L)) :=
    e.toHomeomorph.isCompact_preimage.mpr hKM
  obtain ⟨v, hv, hv0⟩ := rationalNormKernelFixedVectorDetection hfinite F L hL
    (SmoothRep.pullback e JA) (SmoothRep.pullback e E) KL hKL hELirr hgenL hcoeff
    (hEJA.pullback e)
  have hvM : v ∈ fixedVectors E.representation (K.toSubgroup.comap M.subtype) := by
    change v ∈ fixedVectors (E.representation.comp e.toMonoidHom) KL at hv
    rw [fixedVectors_comp_mulEquiv E.representation e.toMulEquiv KL] at hv
    change v ∈ fixedVectors E.representation (KL.comap e.symm.toMonoidHom) at hv
    rwa [hKback] at hv
  exact hlift (NormalizedJacquetBridge.nonzero_fixed_subquotient KM hKM hEsub
    ⟨v, hvM, hv0⟩)

end Langlands
