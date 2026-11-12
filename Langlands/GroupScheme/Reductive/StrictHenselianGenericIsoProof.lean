import Langlands.GroupScheme.Reductive.StrictHenselianGenericIsoStatement
import Langlands.GroupScheme.Torus.StrictHenselianMaximal
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumComparison
import Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismProof

/-! # Proof: generic-fibre determination over strictly Henselian local domains -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- A reductive group over a strictly Henselian local ring contains a closed coordinate split
torus `splitTorus I ⟶ G` that is maximal on every residue-field fibre. The abstract split torus of
`strictHenselianSplitMaximalTorus` is replaced by its coordinate model. -/
theorem exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G) :
    ∃ (I : Type u) (_ : Fintype I) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i ∧
        IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i := by
  obtain ⟨T, i, ⟨I, hI, ⟨e⟩⟩, hi, hmax⟩ := strictHenselianSplitMaximalTorus R G hG
  let : Fintype I := Fintype.ofFinite I
  refine ⟨I, inferInstance, e.inv ≫ i, hi.iso_comp e.symm, fun s => ?_⟩
  exact (isMaximalTorus_baseChange_inv_comp_iff
    ((Spec (CommRingCat.of R)).fromSpecResidueField s)
    (T' := splitTorus.commGroupScheme _ I) e i).mpr (hmax s)

/-- **Generic-fibre determination over strictly Henselian local domains.** Reductive groups over
a strictly Henselian local domain whose fraction-field fibres are isomorphic are isomorphic. -/
theorem strictHenselianGenericIso : StrictHenselianGenericIsoStatement.{u} := by
  intro R _ _ _ _ K _ _ _ G H hG hH ⟨f⟩
  classical
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  obtain ⟨I, _, i, hi, hmax⟩ := exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian R G hG
  obtain ⟨I', _, i', hi', hmax'⟩ :=
    exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian R H hH
  obtain ⟨J, P, hP⟩ := localSplitFibrewiseRootDatumExistence R G hG I i hi hmax
  obtain ⟨J', Q, hQ⟩ := localSplitFibrewiseRootDatumExistence R H hH I' i' hi' hmax'
  have hPQ := hP.nonempty_equiv_of_reductive_fieldIso hQ hG hH K
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax K)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H i' hmax' K) f
  exact localSplitReducedIsomorphismTheorem R G H hG hH I I' i i' hi hi' hmax hmax' J J' P Q
    hP hQ hPQ

end Langlands.GroupScheme
