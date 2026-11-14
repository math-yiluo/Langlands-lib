import Langlands.GroupScheme.NormalQuotientReductiveGluing
import Langlands.GroupScheme.Descent.RelativeSubgroups
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Effective descent of relative quasi-split group-and-torus data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Reductivity

variable {S U : Scheme.{u}} {G : GroupScheme S} [IsAffineHom G.X.hom]

/-- For an affine group scheme, reductivity reflects under fpqc base change. -/
theorem IsReductive.of_baseChange (p : U ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    (hG : IsReductive ((GroupScheme.baseChange p).obj G)) : IsReductive G := by
  have hκ : ∀ s : S,
      IsConnectedReductive ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G) := by
    intro s
    obtain ⟨x, rfl⟩ := p.surjective s
    let a := S.fromSpecResidueField (p x)
    let c := Spec.map (p.residueFieldMap x)
    let : Algebra (S.residueField (p x) : Type u) (U.residueField x : Type u) :=
      (p.residueFieldMap x).hom.toAlgebra
    have h := (hG.isConnectedReductive_residueFiber x).of_iso
      (baseChangeCompIso p (U.fromSpecResidueField x) G)
    rw [← p.SpecMap_residueFieldMap_fromSpecResidueField x] at h
    exact IsConnectedReductive.of_fieldExtension
      (k := (S.residueField (p x) : Type u)) (K := (U.residueField x : Type u))
      (h.of_iso (baseChangeCompIso a c G).symm)
  refine ⟨smooth_of_baseChange p G hG.smooth, inferInstance, fun s => ?_⟩
  have h := connectedReductiveFieldExtensionStatement
    (S.residueField s) (AlgebraicClosure (S.residueField s)) _ (hκ s)
  exact (h.of_iso
    (baseChangeCompIso (S.fromSpecResidueField s) (toAlgebraicClosure _) G)).isPseudoReductive

end Reductivity

namespace Descent

section Invariance

variable {S U : Scheme.{u}} {p : U ⟶ S} {G H : GroupScheme U}
  {D : Datum p G} (s : Solution D) (i : H ⟶ G)

/-- The solution comparison transports invariant subgroup ranges to the
canonical datum on its actual descended ambient group. -/
theorem Solution.invariantRange_inv
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map (i ≫ s.iso.inv) ≫
          (canonicalOverlap p s.obj).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd p)).map (i ≫ s.iso.inv)) := by
  have hc := s.compatible.inv s.iso
  change (GroupScheme.baseChange (fst p)).map s.iso.inv ≫
      (canonicalOverlap p s.obj).hom =
    D.overlap.hom ≫ (GroupScheme.baseChange (snd p)).map s.iso.inv at hc
  rw [Functor.map_comp, Category.assoc, hc, Functor.map_comp]
  exact (SubgroupFunctor.range_comp_iso_eq_iff
    ((GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom)
    ((GroupScheme.baseChange (snd p)).map i)
    ((GroupScheme.baseChange (snd p)).mapIso s.iso.symm)).2 h

end Invariance

/-- An actual affine ambient descent with recovered relative Borel and maximal
torus presentations, including their containment. -/
structure RelativeQuasiSplitTorusSolution
    {S U : Scheme.{u}} {p : U ⟶ S} {G B : GroupScheme U}
    {T : CommGroupScheme U} (D : Datum p G) (i : B ⟶ G) (t : T.toGrp ⟶ G) where
  group : Solution D
  groupAffine : IsAffine group.obj.X.left
  reductive : IsReductive group.obj
  borel : RelativeBorelDescentData (i ≫ group.iso.inv)
  torus : RelativeTorusDescentData (t ≫ group.iso.inv)
  torus_le_borel : SubgroupFunctor.range torus.inclusion ≤
    SubgroupFunctor.range borel.inclusion

/-- The constructed relative Borel makes the constructed group relatively quasi-split. -/
theorem RelativeQuasiSplitTorusSolution.quasiSplit
    {S U : Scheme.{u}} {p : U ⟶ S} {G B : GroupScheme U}
    {T : CommGroupScheme U} {D : Datum p G} {i : B ⟶ G} {t : T.toGrp ⟶ G}
    (s : RelativeQuasiSplitTorusSolution D i t) : IsRelativeQuasiSplit s.group.obj :=
  s.borel.quasiSplit s.reductive

section AffineConstruction

variable {S U : Scheme.{u}} [IsAffine S] [IsAffine U] {p : U ⟶ S}
  [Etale p] [Surjective p] {G B : GroupScheme U} {T : CommGroupScheme U}
  {i : B ⟶ G} {t : T.toGrp ⟶ G}

/-- Construct a relatively quasi-split affine descent from an actual reductive
group datum preserving supplied closed Borel and maximal-torus ranges. -/
def Datum.relativeQuasiSplitTorusSolution (D : Datum p G) (hG : IsReductive G)
    (hi : IsRelativeBorelSubgroup i) (hiClosed : IsClosedSubgroup i)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hincl : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hBInv : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i))
    (hTInv : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map t ≫ D.overlap.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map t)) :
    RelativeQuasiSplitTorusSolution D i t := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let s := D.affineSolution
  let : IsAffine s.obj.X.left := inferInstanceAs (IsAffine D.affineSolution.obj.X.left)
  let : IsAffineHom s.obj.X.hom := inferInstance
  have hred : IsReductive s.obj := IsReductive.of_baseChange p (hG.of_iso s.iso)
  let b := (hi.comp_iso s.iso.symm).descentOfOverlap
    (hiClosed.comp_iso s.iso.symm) (s.invariantRange_inv i hBInv)
  let a := hT.descentOfOverlap (ht.comp_iso s.iso.symm)
    (hmax.comp_iso s.iso.symm) (s.invariantRange_inv t hTInv)
  have hab : SubgroupFunctor.range (t ≫ s.iso.inv) ≤
      SubgroupFunctor.range (i ≫ s.iso.inv) :=
    (SubgroupFunctor.range_comp_iso_le_iff t i s.iso.symm).2 hincl
  exact
    { group := s
      groupAffine := inferInstance
      reductive := hred
      borel := b
      torus := a
      torus_le_borel := a.range_le b hab }

end AffineConstruction

end Descent

end Langlands.GroupScheme
