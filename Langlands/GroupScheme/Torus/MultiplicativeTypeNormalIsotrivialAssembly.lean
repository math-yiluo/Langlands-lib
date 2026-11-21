import Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialStatement
import Langlands.GroupScheme.Torus.RelativeCharacterLocalConstancyProof
import Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement

/-! # Normal-base isotriviality from the normal-base local-system theorem -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A finite étale trivialization of the actual characters gives a finite étale
diagonalization of the group, both locally and over an irreducible normal base. -/
theorem multiplicativeTypeNormalIsotrivial_of_localSystem
    (hNormal : Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement.{u}) :
    MultiplicativeTypeNormalIsotrivialStatement.{u} := by
  intro S hS H hH
  obtain ⟨hLocal, hGlobal⟩ :=
    hNormal S hS hH.characters (relativeCharacterLocalConstancy S H hH)
  constructor
  · intro s
    obtain ⟨U, hs, U', p, hpFinite, hpEtale, hpSurj, M, hM, ⟨e⟩⟩ := hLocal s
    refine ⟨U, hs, U', p, hpFinite, hpEtale, hpSurj, ?_⟩
    apply (relativeCharacterConstancy U' _ (hH.baseChange (p ≫ U.ι))).2
    exact ⟨M, hM, ⟨(Cartier.charactersBaseChangeIso hH.commGroupScheme (p ≫ U.ι)).symm ≪≫ e⟩⟩
  · intro hIrred
    obtain ⟨S', p, hpFinite, hpEtale, hpSurj, M, hM, ⟨e⟩⟩ := hGlobal hIrred
    refine ⟨S', p, hpFinite, hpEtale, hpSurj, ?_⟩
    apply (relativeCharacterConstancy S' _ (hH.baseChange p)).2
    exact ⟨M, hM, ⟨(Cartier.charactersBaseChangeIso hH.commGroupScheme p).symm ≪≫ e⟩⟩

end Langlands.GroupScheme
