import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalExistence
import Langlands.GroupScheme.RelativeLevi.EtaleDynamicCover

/-! # Relative radical data with uniqueness from pointwise dynamic presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P : GroupScheme S}

/-- Construct an actual relative radical together with uniqueness of its
all-test range from pointwise etale dynamic presentations. -/
def radicalWithUniquenessOfPointwiseDynamic
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (f : T ⟶ S), Etale f ∧
      (∃ t : T, f.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (baseChange f).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((baseChange f).map iP)) :
    Σ U : GroupScheme S, {r : U ⟶ P //
      IsRelativeUnipotentRadical r ∧
        ∀ (U' : GroupScheme S) (r' : U' ⟶ P), IsRelativeUnipotentRadical r' →
          SubgroupFunctor.range r' = SubgroupFunctor.range r} := by
  let d := etaleDynamicCoverOfPointwise iP hlocal
  let R := radicalOfEtaleDynamicCover hdynamic hG iP d.val d.property
  refine ⟨R.1, R.2.val, R.2.property, ?_⟩
  intro U' r' hr'
  exact radical_range_eq_of_etale_dynamicCover hdynamic hG iP d.val d.property
    r' R.2.val hr' R.2.property

end Langlands.GroupScheme.RelativeLevi
