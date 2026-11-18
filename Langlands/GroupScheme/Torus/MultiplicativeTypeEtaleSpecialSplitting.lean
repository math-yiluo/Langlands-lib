import Langlands.CommutativeAlgebra.EtaleResidueExtensions
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Descent.Data

/-! # Splitting a multiplicative-type residue fibre at an etale point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.ExtensionReduction

variable (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
  (p : PrimeSpectrum R)

/-- An actual etale coefficient algebra and point above a specified prime
at which the middle residue group has a full diagonalizable presentation. -/
structure EtaleSpecialSplitting where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra R ring]
  [etale : Algebra.Etale R ring]
  point : PrimeSpectrum ring
  point_over : Spec.algebraMap R ring point = p
  characters : Type u
  [characterGroup : AddCommGroup characters]
  [finiteCharacters : AddGroup.FG characters]
  iso : (baseChange (Spec.algebraMap ring point.asIdeal.ResidueField)).obj
      ((baseChange (Spec.algebraMap R ring)).obj G) ≅
    (Diagonalizable.groupScheme (CommRingCat.of point.asIdeal.ResidueField) characters).toGrp

attribute [instance] EtaleSpecialSplitting.commRing EtaleSpecialSplitting.algebra
  EtaleSpecialSplitting.etale EtaleSpecialSplitting.characterGroup
  EtaleSpecialSplitting.finiteCharacters

/-- A multiplicative-type residue fibre splits at a point of an actual etale
algebra, without requiring a strict henselization. -/
theorem nonempty_etaleSpecialSplitting
    (hG : IsMultiplicativeType
      ((baseChange (Spec.algebraMap R p.asIdeal.ResidueField)).obj G)) :
    Nonempty (EtaleSpecialSplitting R G p) := by
  let k := p.asIdeal.ResidueField
  obtain ⟨K, hK, aK, hfin, hgal, M, hM, hfg, ⟨e⟩⟩ :=
    multiplicativeTypeFiniteGaloisSplitting k
      ((baseChange (Spec.algebraMap R k)).obj G) hG
  let := hK
  let := aK
  let := hfin
  let := hgal
  let := hM
  let := hfg
  let : Algebra R K := ((algebraMap k K).comp (algebraMap R k)).toAlgebra
  have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨A, hA, aA, het, q, eq, hq, hcomp⟩ :=
    Langlands.CommutativeAlgebra.exists_etale_residue_extension R p.asIdeal K
  let := hA
  let := aA
  let := het
  let b := Spec.algebraMap R A
  let sp := Spec.algebraMap A q.asIdeal.ResidueField
  let rk := Spec.algebraMap R k
  let kk := Spec.algebraMap k K
  let rK := Spec.algebraMap R K
  have hkk : kk ≫ rk = rK := by
    dsimp [kk, rk, rK, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let eK : (baseChange rK).obj G ≅ (Diagonalizable.groupScheme (CommRingCat.of K) M).toGrp :=
    (Descent.pullbackComparison rk kk rK hkk G).symm ≪≫ e
  let a : Spec (CommRingCat.of q.asIdeal.ResidueField) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom eq.symm.toRingHom)
  have ha : a ≫ rK = sp ≫ b := by
    dsimp [a, rK, sp, b, Spec.algebraMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    change eq.symm (algebraMap R K r) =
      algebraMap A q.asIdeal.ResidueField (algebraMap R A r)
    exact eq.injective (by simpa only [RingEquiv.apply_symm_apply] using (hcomp r).symm)
  let eQ : (baseChange (sp ≫ b)).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of q.asIdeal.ResidueField) M).toGrp :=
    (Descent.pullbackComparison rK a (sp ≫ b) ha G).symm ≪≫
      (baseChange a).mapIso eK ≪≫ Diagonalizable.baseChangeIso a M
  refine ⟨{
    ring := A
    point := q
    point_over := ?_
    characters := M
    iso := (baseChangeCompIso b sp G).symm ≪≫ eQ }⟩
  apply PrimeSpectrum.ext
  exact hq

/-- Choose the actual etale special-fibre splitting data. -/
def etaleSpecialSplitting
    (hG : IsMultiplicativeType
      ((baseChange (Spec.algebraMap R p.asIdeal.ResidueField)).obj G)) :
    EtaleSpecialSplitting R G p :=
  Classical.choice (nonempty_etaleSpecialSplitting R G p hG)

/-- Over a noetherian original ring, the chosen etale algebra is noetherian. -/
theorem EtaleSpecialSplitting.noetherian [IsNoetherianRing R]
    (E : EtaleSpecialSplitting R G p) : IsNoetherianRing E.ring :=
  Algebra.FiniteType.isNoetherianRing R E.ring

end Langlands.GroupScheme.ExtensionReduction
