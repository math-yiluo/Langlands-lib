import Langlands.GroupScheme.Reductive.GaloisRadicalDescent
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusAssembly

/-! # Actual split geometric radicals and sectioned solvable torus quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual split geometric radical, without an existence premise. -/
structure SplitGeometricUnipotentRadical
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) where
  source : GroupScheme (Spec (CommRingCat.of k))
  inclusion : source ⟶ G
  isGeometricUnipotentRadical : LeviSubgroup.IsGeometricUnipotentRadical inclusion
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent source

/-- Over a perfect field, descend the geometric radical from the algebraic
closure and apply the proved perfect-field splitness theorem. -/
def perfectFieldSplitGeometricUnipotentRadical
    {k : Type u} [Field k] [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    SplitGeometricUnipotentRadical G :=
  Classical.choice (by
    let b := toAlgebraicClosure k
    let : IsGalois k (AlgebraicClosure k) := ⟨⟩
    let : Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
      inferInstanceAs (Smooth (pullback.snd G.X.hom b))
    let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
    let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
      G.connectedSpace_baseChange_of_smooth_affine b
    obtain ⟨U, i, hi⟩ :=
      unipotentRadicalExistence (AlgebraicClosure k) ((GroupScheme.baseChange b).obj G)
    let d := hi.galoisRadicalDescent
    have hgeom : LeviSubgroup.IsGeometricUnipotentRadical d.inclusion := by
      refine ⟨d.isRadical, ?_⟩
      change IsUnipotentRadical
        ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).map d.inclusion)
      rw [d.recovers]
      exact hi.precomp_iso d.comparison
    let : Smooth d.source.X.hom := d.isRadical.smooth
    let : IsClosedImmersion d.inclusion.hom.hom.left := d.isRadical.isClosedSubgroup
    let : IsAffineHom d.source.X.hom := by
      rw [← Over.w d.inclusion.hom.hom]
      infer_instance
    exact ⟨{
      source := d.source
      inclusion := d.inclusion
      isGeometricUnipotentRadical := hgeom
      isSplitUnipotent :=
        perfectFieldUnipotentSplit k d.source d.isRadical.connectedSpace
          d.isRadical.isUnipotent
    }⟩)

/-- An actual split geometric radical with the sectioned torus quotient of
that same inclusion. -/
structure SplitGeometricRadicalSectionedTorusQuotient
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    extends SplitGeometricUnipotentRadical G where
  quotientData : SectionedGeometricRadicalTorusQuotient inclusion

/-- The only remaining inputs are the absolute solvable quotient and
stable-vector statements; radical existence and perfect-field splitness are
discharged by published proofs. -/
def perfectFieldSectionedSolvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u})
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k] [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsSolvableGroupScheme G) :
    SplitGeometricRadicalSectionedTorusQuotient G := by
  let d := perfectFieldSplitGeometricUnipotentRadical G
  exact {
    toSplitGeometricUnipotentRadical := d
    quotientData :=
      d.isGeometricUnipotentRadical.sectionedTorusQuotient
        hquot hstable d.isSplitUnipotent hG
  }

namespace SplitGeometricRadicalSectionedTorusQuotient

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (d : SplitGeometricRadicalSectionedTorusQuotient G)

/-- The original quotient, viewed as a commutative group scheme. -/
def torus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  { d.quotientData.quotient with comm := d.quotientData.isTorus.isCommMonObj }

theorem torus_isTorus : IsTorus d.torus.toGrp :=
  d.quotientData.isTorus

end SplitGeometricRadicalSectionedTorusQuotient

end Langlands.GroupScheme
