import Langlands.BruhatTits.SpecialCompact.GeneralLinearStandardLeviIntegralPointsStatement
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # The matrix realization of the inherited integral points in a standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

set_option maxHeartbeats 800000 in
/-- The ambient matrix identification preserves the literal intersection
with the standard integral points. -/
theorem generalLinearStandardLeviIntegralPoints :
    GeneralLinearStandardLeviIntegralPointsStatement.{u} := by
  intro F _ _ N
  let R := CommRingCat.of F
  let T := splitTorus.commGroupScheme (Spec R) (ULift (Fin N))
  let i := GeneralLinear.diagonalTorus (Fin N) R
  let G := GeneralLinear.groupScheme (Fin N) R
  let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
  let e := GeneralLinear.rationalPointsEquiv N R
  change ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν → _
  intro ν hν J ζ hζ
  let w := GeneralLinear.cocharacterCoordEquiv (Fin N) F ζ
  let L := standardLeviPoints i ν J
  let f := algebraMap 𝒪[F] F
  change L.map e.toMonoidHom = GeneralLinear.blockLeviSubgroup F w ∧
    (K ⊓ L).map e.toMonoidHom =
      (GeneralLinear.blockLeviSubgroup 𝒪[F] w).map (Matrix.GeneralLinearGroup.map f)
  obtain ⟨_, hcompare⟩ := standardCocharacter F G
    (isConnectedReductive_generalLinear F (Fin N)) T i
    (GeneralLinear.isMaximalSplitTorus_diagonalTorus F) ν hν J hζ.1
  have hζw : CommGroupScheme.groupHom ζ ≫ i =
      GeneralLinear.diagonalCocharacter (Fin N) R w := by
    simpa only [w, GeneralLinear.cocharacterOfWeights, LinearEquiv.symm_apply_apply] using
      GeneralLinear.cocharacterOfWeights_comp_diagonalTorus F w
  have hLevi : standardLevi i ν J = GeneralLinear.blockLevi (Fin N) R w := by
    rw [(hcompare ζ hζ).2.1, hζw, GeneralLinear.centralizer_diagonalCocharacter]
  have hmatrix (g : rationalPoints G) : g ∈ L ↔ e g ∈ GeneralLinear.blockLeviSubgroup F w := by
    change g ∈ (standardLevi i ν J).carrier _ ↔ _
    rw [hLevi]
    exact (GeneralLinear.glRingEquiv_mem_blockLeviSubgroup_iff w
      (GeneralLinear.globalSectionsEquiv R)).symm
  constructor
  · ext g
    rw [Subgroup.mem_map_equiv, hmatrix, MulEquiv.apply_symm_apply]
  · ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ K ∧ x ∈ L at hx
      obtain ⟨y, hy⟩ := (GeneralLinear.mem_standardIntegralModel_integralPoints_iff 𝒪[F] F x).mp hx.1
      refine ⟨y, ?_, hy⟩
      intro a b hab
      apply IsFractionRing.injective 𝒪[F] F
      rw [map_zero]
      change (Matrix.GeneralLinearGroup.map f y) a b = 0
      rw [hy]
      exact (hmatrix x).mp hx.2 a b hab
    · rintro ⟨y, hy, rfl⟩
      let x := e.symm (Matrix.GeneralLinearGroup.map f y)
      have hx : e x = Matrix.GeneralLinearGroup.map f y := e.apply_symm_apply _
      refine ⟨x, ⟨?_, ?_⟩, hx⟩
      · exact (GeneralLinear.mem_standardIntegralModel_integralPoints_iff 𝒪[F] F x).mpr ⟨y, hx.symm⟩
      · apply (hmatrix x).mpr
        rw [hx]
        exact GeneralLinear.map_mem_blockLeviSubgroup w f hy

end Langlands.BruhatTits.SpecialCompact
