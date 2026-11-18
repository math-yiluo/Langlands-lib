import Langlands.GroupScheme.Reductive.LocalSplitGeometricIsoStatement
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistenceProof
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumComparison
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Geometric-fibre determination from the local Isomorphism Theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- The local Isomorphism Theorem implies geometric-fibre determination for
reductive groups with fibrewise maximal split tori. -/
theorem localSplitReductiveGeometricIso_of_isomorphismTheorem
    (hIso : LocalSplitIsomorphismTheoremStatement.{u}) :
    LocalSplitReductiveGeometricIsoStatement.{u} := by
  intro R _ _ G H hG hH hTG hTH Ω _ _ _ ⟨f⟩
  classical
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  obtain ⟨T, i, ⟨I, hI, ⟨e⟩⟩, hi, hmax⟩ := hTG
  obtain ⟨T', i', ⟨I', hI', ⟨e'⟩⟩, hi', hmax'⟩ := hTH
  let : Fintype I := Fintype.ofFinite I
  let : Fintype I' := Fintype.ofFinite I'
  have hmaxI : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme _ I) (e.inv ≫ i) := by
    intro s
    exact (isMaximalTorus_baseChange_inv_comp_iff
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)
      (T' := splitTorus.commGroupScheme _ I) e i).mpr (hmax s)
  have hmaxI' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme _ I') (e'.inv ≫ i') := by
    intro s
    exact (isMaximalTorus_baseChange_inv_comp_iff
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)
      (T' := splitTorus.commGroupScheme _ I') e' i').mpr (hmax' s)
  have hclosed := hi.iso_comp e.symm
  have hclosed' := hi'.iso_comp e'.symm
  obtain ⟨J, P, hP⟩ := localSplitFibrewiseRootDatumExistenceProof
    R G hG I (e.inv ≫ i) hclosed hmaxI
  obtain ⟨J', Q, hQ⟩ := localSplitFibrewiseRootDatumExistenceProof
    R H hH I' (e'.inv ≫ i') hclosed' hmaxI'
  have hPQ := hP.nonempty_equiv_of_reductive_fieldIso hQ hG hH Ω
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G (e.inv ≫ i) hmaxI Ω)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H (e'.inv ≫ i') hmaxI' Ω) f
  exact hIso R G H hG hH I I' (e.inv ≫ i) (e'.inv ≫ i')
    hclosed hclosed' hmaxI hmaxI' J J' P Q hP hQ hPQ

/-- Split reductive groups over a local ring are determined up to isomorphism
by one geometric fibre. -/
theorem localSplitReductiveGeometricIso : LocalSplitReductiveGeometricIsoStatement.{u} :=
  localSplitReductiveGeometricIso_of_isomorphismTheorem localSplitIsomorphismTheorem

end Langlands.GroupScheme
