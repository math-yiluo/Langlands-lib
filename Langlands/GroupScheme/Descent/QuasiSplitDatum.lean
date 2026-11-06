import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Effective descent of actual group-and-Borel data -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section Transport

variable {k : Type u} [Field k]
  {B B' G : GroupScheme (Spec (CommRingCat.of k))}

/-- Changing the source presentation preserves the geometric Borel property. -/
theorem IsGeometricBorelSubgroup.iso_comp {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) (e : B' ≅ B) :
    IsGeometricBorelSubgroup (e.hom ≫ i) := by
  refine ⟨hi.1.iso_comp e, ?_⟩
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  change IsBorelSubgroup (F.map (e.hom ≫ i))
  rw [F.map_comp]
  exact hi.2.iso_comp (F.mapIso e)

end Transport

section IsomorphicBase

variable {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K]
  {B G : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

/-- Isomorphic change of algebraically closed base fields reflects Borels. -/
theorem IsBorelSubgroup.of_baseChange_of_isIso
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b]
    (hi : IsBorelSubgroup ((GroupScheme.baseChange b).map i)) :
    IsBorelSubgroup i := by
  let R := GroupScheme.baseChange (inv b)
  let e := baseChangeSectionNatIso b (inv b) (IsIso.inv_hom_id b)
  have h := ((hi.baseChange_of_isIso (inv b)).iso_comp (e.app B).symm).comp_iso
    (e.app G)
  change IsBorelSubgroup
    (((e.app B).inv ≫ R.map ((GroupScheme.baseChange b).map i)) ≫ (e.app G).hom) at h
  rw [Category.assoc] at h
  have hn := e.hom.naturality i
  change R.map ((GroupScheme.baseChange b).map i) ≫ (e.app G).hom =
    (e.app B).hom ≫ i at hn
  rw [hn, Iso.inv_hom_id_assoc] at h
  exact h

end IsomorphicBase

section AlgebraicExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]
  {B G : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}
  [IsAffineHom G.X.hom]

/-- A closed inclusion is geometric Borel if it becomes geometric Borel over an
algebraic field extension. -/
theorem IsGeometricBorelSubgroup.of_baseChange_of_algebraicExtension
    (hi : IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i) : IsGeometricBorelSubgroup i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let a := toAlgebraicClosure k
  let c := toAlgebraicClosure K
  let r := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K)))
  let e := IsAlgClosure.equiv k (AlgebraicClosure K) (AlgebraicClosure k)
  let d := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have : IsIso d := isIso_SpecMap_iff.mpr e.symm.bijective
  have hr : c ≫ b = r := by
    dsimp [b, c, r, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq k K (AlgebraicClosure K)]
  have hd : d ≫ a = r := by
    dsimp [a, d, r, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (RingHom.ext fun x => e.symm.commutes x)
  have hR : IsBorelSubgroup ((GroupScheme.baseChange r).map i) := by
    have h := (hi.2.iso_comp
      (Descent.pullbackComparison b c r hr B).symm).comp_iso
        (Descent.pullbackComparison b c r hr G)
    change IsBorelSubgroup
      (((Descent.pullbackComparison b c r hr B).inv ≫
        (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)) ≫
          (Descent.pullbackComparison b c r hr G).hom) at h
    rw [Category.assoc, Descent.pullbackComparison_naturality,
      Iso.inv_hom_id_assoc] at h
    exact h
  have hD : IsBorelSubgroup
      ((GroupScheme.baseChange d).map ((GroupScheme.baseChange a).map i)) := by
    have h := (hR.iso_comp (Descent.pullbackComparison a d r hd B)).comp_iso
      (Descent.pullbackComparison a d r hd G).symm
    change IsBorelSubgroup
      (((Descent.pullbackComparison a d r hd B).hom ≫
        (GroupScheme.baseChange r).map i) ≫
          (Descent.pullbackComparison a d r hd G).inv) at h
    rw [← Descent.pullbackComparison_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at h
    exact h
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
    (IsBorelSubgroup.of_baseChange_of_isIso d hD) hclosed

end AlgebraicExtension

namespace Descent

/-- Actual solutions of a group datum and a Borel datum, with the descended
inclusion and its exact recovery equation. -/
structure QuasiSplitSolution {k : Type u} [Field k]
    {S : Scheme.{u}} {p : S ⟶ Spec (CommRingCat.of k)}
    {G B : GroupScheme S} (D : Datum p G) (E : Datum p B) (i : B ⟶ G) where
  group : Solution D
  borel : Solution E
  inclusion : borel.obj ⟶ group.obj
  recovery : (GroupScheme.baseChange p).map inclusion ≫ group.iso.hom =
    borel.iso.hom ≫ i
  groupAffine : IsAffine group.obj.X.left
  borelAffine : IsAffine borel.obj.X.left
  reductive : IsConnectedReductive group.obj
  geometricBorel : IsGeometricBorelSubgroup inclusion

/-- The descended group is quasi-split, with the constructed descended Borel. -/
theorem QuasiSplitSolution.quasiSplit {k : Type u} [Field k]
    {S : Scheme.{u}} {p : S ⟶ Spec (CommRingCat.of k)}
    {G B : GroupScheme S} {D : Datum p G} {E : Datum p B} {i : B ⟶ G}
    (s : QuasiSplitSolution D E i) : IsQuasiSplit s.group.obj :=
  ⟨s.reductive, s.borel.obj, s.inclusion, s.geometricBorel⟩

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]
  {G B : GroupScheme (Spec (CommRingCat.of K))} {i : B ⟶ G}

/-- Effective descent of compatible actual group-and-geometric-Borel data over
an algebraic extension of fields. No solution is an input. -/
def Datum.quasiSplitSolution
    (D : Datum (Spec.map (CommRingCat.ofHom (algebraMap k K))) G)
    (E : Datum (Spec.map (CommRingCat.ofHom (algebraMap k K))) B)
    (hG : IsConnectedReductive G) (hi : IsGeometricBorelSubgroup i)
    (hf : Compatible E D i) : QuasiSplitSolution D E i := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hpSurjective, hpFlat, hpQuasiCompact⟩ := fieldExtension_fpqc k K
  let : Surjective p := hpSurjective
  let : Flat p := hpFlat
  let : QuasiCompact p := hpQuasiCompact
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  let : IsAffine B.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let s := D.affineSolution
  let t := E.affineSolution
  let f := t.descendHom s i hf
  have hrec : (GroupScheme.baseChange p).map f ≫ s.iso.hom = t.iso.hom ≫ i :=
    t.baseChange_descendHom s i hf
  have hred : IsConnectedReductive s.obj :=
    IsConnectedReductive.of_fieldExtension (hG.of_iso s.iso)
  let : IsAffine s.obj.X.left := inferInstanceAs (IsAffine D.affineSolution.obj.X.left)
  let : IsAffine t.obj.X.left := inferInstanceAs (IsAffine E.affineSolution.obj.X.left)
  let : IsAffineHom s.obj.X.hom := hred.isAffineHom
  have hf' : (GroupScheme.baseChange p).map f = t.iso.hom ≫ i ≫ s.iso.inv := by
    rw [← Category.assoc, ← hrec, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hgeo : IsGeometricBorelSubgroup ((GroupScheme.baseChange p).map f) := by
    rw [hf', ← Category.assoc]
    exact (hi.iso_comp t.iso).comp_iso s.iso.symm
  have hclosed : IsClosedSubgroup f :=
    IsClosedSubgroup.of_baseChange_of_isAffine p hgeo.1.isClosedSubgroup
  exact
    { group := s
      borel := t
      inclusion := f
      recovery := hrec
      groupAffine := inferInstance
      borelAffine := inferInstance
      reductive := hred
      geometricBorel :=
        IsGeometricBorelSubgroup.of_baseChange_of_algebraicExtension hgeo hclosed }

/-- An actual ambient datum preserving the Borel's all-test overlap range
constructs both compatible Borel data and their quasi-split descent. -/
def Datum.quasiSplitSolutionOfRangeEq
    (D : Datum (Spec.map (CommRingCat.ofHom (algebraMap k K))) G)
    (hG : IsConnectedReductive G) (hi : IsGeometricBorelSubgroup i)
    (hinv : SubgroupFunctor.range
        ((GroupScheme.baseChange
          (fst (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i ≫ D.overlap.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange
        (snd (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i)) :
    QuasiSplitSolution D (D.closedSubgroup hi.1.isClosedSubgroup hinv) i :=
  D.quasiSplitSolution (D.closedSubgroup hi.1.isClosedSubgroup hinv) hG hi
    (D.compatible_closedSubgroup hi.1.isClosedSubgroup hinv)

end FieldExtension

end Descent

end Langlands.GroupScheme
