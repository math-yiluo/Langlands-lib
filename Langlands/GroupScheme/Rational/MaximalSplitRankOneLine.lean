import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.VectorMatrixMap
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive

/-! # Equivariant lines through rational points of nonmultipliable root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open VectorGroup

section Line

variable {k : Type u} [Field k] {U : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)))
    (he : RelativeRoot.IsNaturalVectorCoordinates e) (v : Fin n → k)

/-- The column matrix of a coefficient vector. -/
def lineMatrix : Matrix (Fin n) (Fin 1) (CommRingCat.of k) :=
  Matrix.of fun r _ => v r

/-- The additive line `c ↦ c • v` in the supplied natural coordinates. -/
def lineHom : groupScheme (CommRingCat.of k) 1 ⟶ U :=
  matrixHom (lineMatrix v) ≫ (RelativeRoot.vectorGroupIso e he).inv

theorem lineHom_coordinates (Z : Over (Spec (CommRingCat.of k)))
    (x : Z ⟶ (groupScheme (CommRingCat.of k) 1).X) :
    (e Z (x ≫ (lineHom e he v).hom.hom)).toAdd =
      fun r => scalarMap Z (v r) * (coordinates (CommRingCat.of k) 1 Z x).toAdd 0 := by
  have h := RelativeRoot.coordinates_comp_vectorGroupIso_hom e he Z
    (x ≫ (lineHom e he v).hom.hom)
  rw [← h]
  have hcomp : x ≫ (lineHom e he v).hom.hom ≫
      (RelativeRoot.vectorGroupIso e he).hom.hom.hom = x ≫ (matrixHom (lineMatrix v)).hom.hom := by
    simp only [lineHom, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, hcomp, coordinates_matrixHom]
  funext r
  simp [lineMatrix, Matrix.mulVec, dotProduct]

theorem lineHom_scalarPoint (Z : Over (Spec (CommRingCat.of k))) (c : Γ(Z.left, ⊤)) :
    (e Z (scalarPoint (CommRingCat.of k) Z c ≫ (lineHom e he v).hom.hom)).toAdd =
      fun r => scalarMap Z (v r) * c := by
  rw [lineHom_coordinates, coordinates_scalarPoint]

/-- A line with a nonzero direction vector is a monomorphism. -/
theorem mono_lineHom (hv : v ≠ 0) : Mono (lineHom e he v).hom.hom := by
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hv
  constructor
  intro Z g h hgh
  apply points_ext
  intro l
  have hc := congrArg (fun x => (e Z x).toAdd r) hgh
  simp only [lineHom_coordinates] at hc
  have hu : IsUnit (scalarMap Z (v r)) := (IsUnit.mk0 _ hr).map _
  have hl : l = 0 := Subsingleton.elim _ _
  subst hl
  exact hu.mul_left_cancel hc

/-- The field coordinates of a rational point. -/
def pointVector (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) : Fin n → k :=
  fun r => (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((e _ x).toAdd r)

theorem scalarMap_base (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
    scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k))))
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c) = c := by
  simp [scalarMap]

/-- The line through a rational point takes the value of that point at `1`. -/
theorem lineHom_pointVector_one (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) :
    scalarPoint (CommRingCat.of k) (Over.mk (𝟙 _)) 1 ≫
        (lineHom e he (pointVector e x)).hom.hom = x := by
  apply (e _).injective
  apply Multiplicative.toAdd.injective
  rw [lineHom_scalarPoint]
  funext r
  rw [mul_one, pointVector, scalarMap_base]

theorem pointVector_ne_zero {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X} (hx : x ≠ 1) :
    pointVector e x ≠ 0 := by
  intro h0
  apply hx
  apply (e _).injective
  apply Multiplicative.toAdd.injective
  rw [map_one, toAdd_one]
  funext r
  have h := congrFun h0 r
  simp only [pointVector, Pi.zero_apply] at h
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).inv h
  simpa using h'

end Line

section Equivariant

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    {U : GroupScheme (Spec (CommRingCat.of k))} (j : U ⟶ G)
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j) {n : ℕ}
    {e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))}
    (hw : RelativeRoot.IsWeightVectorCoordinates (RelativeRoot.subgroupAction i a j hj) a e)
    (v : Fin n → k)

include hw

theorem subgroupAction_lineHom (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ S.X)
    (c : Γ(Z.left, ⊤)) :
    (RelativeRoot.subgroupAction i a j hj).act t
        (scalarPoint (CommRingCat.of k) Z c ≫ (lineHom e hw.1 v).hom.hom) =
      scalarPoint (CommRingCat.of k) Z (charValue a Z t * c) ≫ (lineHom e hw.1 v).hom.hom := by
  apply (e Z).injective
  apply Multiplicative.toAdd.injective
  rw [hw.2, lineHom_scalarPoint, lineHom_scalarPoint]
  funext r
  simp only [Pi.smul_apply, smul_eq_mul]
  change charValue a Z t * _ = _
  ring

/-- The line composed with the representing inclusion is torus-equivariant of weight `a`. -/
theorem isTorusEquivariant_lineHom :
    IsTorusEquivariant i (lineHom e hw.1 v ≫ j) a := by
  intro Z t c
  have h := congrArg (· ≫ j.hom.hom) (subgroupAction_lineHom i a j hj hw v Z t c)
  simp only at h
  rw [RelativeRoot.subgroupAction_act_comp] at h
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

end Equivariant

section RootLine

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- **Equivariant lines through root points.** For a nonzero character `a` of a split torus
without higher roots, every nontrivial rational point of the root subgroup of `a` lies on a
monic torus-equivariant additive line of weight `a`, at the parameter `1`. -/
theorem exists_line_through_rootPoint (hT : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : RelativeRoot.HasNoHigherRoots i a)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hu : u ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))) (hu1 : u ≠ 1) :
    ∃ x : groupScheme (CommRingCat.of k) 1 ⟶ G,
      IsTorusEquivariant i x a ∧ Mono x.hom.hom ∧
        SubgroupFunctor.range x ≤ RelativeRoot.subgroup i a ∧
        scalarPoint (CommRingCat.of k) (Over.mk (𝟙 _)) 1 ≫ x.hom.hom = u := by
  obtain ⟨n, e, hw⟩ := RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots hT i ha hhigh hj
  rw [← hj.2] at hu
  obtain ⟨u', rfl⟩ := SubgroupFunctor.mem_range.mp hu
  have hu1' : u' ≠ 1 := by
    rintro rfl
    exact hu1 (MonObj.one_comp _)
  let : Mono j.hom.hom := hj.1
  have : Mono (lineHom e hw.1 (pointVector e u')).hom.hom :=
    mono_lineHom e hw.1 _ (pointVector_ne_zero e hu1')
  refine ⟨lineHom e hw.1 (pointVector e u') ≫ j,
    isTorusEquivariant_lineHom i a j hj hw _, ?_, ?_, ?_⟩
  · rw [Grp.comp_hom_hom]
    infer_instance
  · rw [← hj.2]
    intro Z x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (lineHom e hw.1 (pointVector e u')).hom.hom,
      by rw [Category.assoc, Grp.comp_hom_hom]⟩
  · rw [Grp.comp_hom_hom, ← Category.assoc, lineHom_pointVector_one]

end RootLine

end Langlands.GroupScheme.MaximalSplitSubgroup
