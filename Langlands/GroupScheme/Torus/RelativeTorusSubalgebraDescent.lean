import Langlands.AlgebraicGeometry.FiberMapEqualityDescent
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberConstructibilityProof
import Langlands.GroupScheme.Torus.FibreSpreadingProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Relative tori over finitely generated intermediate algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set Topology TopologicalSpace
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
open Langlands.AlgebraicGeometry.FiberMapEqualityDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorus

/-- The relative torus property of a smooth affine group after base change
from a noetherian ring descends to a finitely generated intermediate algebra. -/
def IsTorusSubalgebraDescentStatement : Prop :=
  ∀ {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsTorus ((baseChange (Spec.algebraMap R A)).obj G) →
    ∃ B : Subalgebra R A, B.FG ∧ IsTorus ((baseChange (Spec.algebraMap R B)).obj G)

private theorem specAlgebraMap_comp {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (B : Subalgebra R A) :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  simp only [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

private theorem isTorus_residueFiber_of_baseChange {S S' : Scheme.{u}} {G : GroupScheme S}
    (b : S' ⟶ S) (h : IsTorus ((baseChange b).obj G)) (y : S') :
    GroupScheme.IsTorus (RelativeIdentityComponent.residueFiber G (b y)) :=
  @GroupScheme.IsTorus.of_baseChange (S.residueField (b y)) (S'.residueField y)
    inferInstance inferInstance (b.residueFieldMap y).hom.toAlgebra _
    (GroupScheme.IsTorus.of_iso (ExtensionReduction.residueFiberBaseChangeIso b G y)
      ((h.baseChange (S'.fromSpecResidueField y)).isTorus))

set_option maxHeartbeats 800000 in
/-- First descend the connectedness locus, then factor through an open
on which the model is a relative torus. -/
theorem isTorusSubalgebraDescent : IsTorusSubalgebraDescentStatement.{u} := by
  intro R A _ _ _ _ G _ _ hA
  let a := Spec.algebraMap R A
  let L := geometricallyConnectedFiberLocus G.X.hom
  have hL : IsConstructible L :=
    isConstructible_geometricallyConnectedFiberLocus_of_localConstructibility
      geometricallyConnectedFiberLocalConstructibility G.X.hom
  have hLA : a ⁻¹' L = univ := by
    rw [← geometricallyConnectedFiberLocus_baseChange (IsPullback.of_hasPullback G.X.hom a)]
    exact (geometricallyConnectedFiberLocus_eq_univ_iff _).mpr hA.geometricallyConnected
  obtain ⟨B, hB, -, hLB⟩ := exists_fg_subalgebra_preimage_eq_univ L hL hLA (∅ : Finset A)
  let H := (baseChange (Spec.algebraMap R B)).obj G
  let b := Spec.algebraMap B A
  let : Smooth H.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  let : IsAffineHom H.X.hom := MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  let : GeometricallyConnected H.X.hom := by
    apply (geometricallyConnectedFiberLocus_eq_univ_iff _).mp
    change geometricallyConnectedFiberLocus (pullback.snd G.X.hom (Spec.algebraMap R B)) = univ
    rw [geometricallyConnectedFiberLocus_baseChange (IsPullback.of_hasPullback _ _)]
    exact hLB
  have hconn (y : Spec (CommRingCat.of B)) :
      ConnectedSpace (RelativeIdentityComponent.residueFiber H y).X.left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := H.X.hom)) _ _
  have hHA : IsTorus ((baseChange b).obj H) :=
    IsTorus.of_iso (Descent.pullbackComparison (Spec.algebraMap R B) b a
      (specAlgebraMap_comp B) G) hA
  choose U hU hTU using fun x : Spec (CommRingCat.of A) =>
    torusFibreSpreading _ H hconn (b x) (isTorus_residueFiber_of_baseChange b hHA x)
  let D := ⋃ x, (U x : Set (Spec (CommRingCat.of B)))
  let : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp hB
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hD : IsConstructible D :=
    (NoetherianSpace.isCompact D).isConstructible (isOpen_iUnion fun x => (U x).isOpen)
  have hDA : b ⁻¹' D = univ := eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, hU x⟩
  obtain ⟨C, hC, -, hDC⟩ := exists_fg_subalgebra_preimage_eq_univ D hD hDA (∅ : Finset A)
  let q := Spec.algebraMap B C
  let V (x : Spec (CommRingCat.of A)) := q ⁻¹ᵁ U x
  let 𝒰 : (Spec (CommRingCat.of C)).OpenCover := Scheme.Cover.mkOfCovers
    (Spec (CommRingCat.of A)) (fun x => (V x).toScheme) (fun x => (V x).ι) (fun y => by
      have hq : q y ∈ D := Set.eq_univ_iff_forall.mp hDC y
      obtain ⟨x, hx⟩ := mem_iUnion.mp hq
      exact ⟨x, ⟨y, hx⟩, rfl⟩)
  have hHC : IsTorus ((baseChange q).obj H) := by
    apply IsTorus.of_openCover 𝒰
    intro x
    let v := q.resLE (U x) (V x) le_rfl
    exact IsTorus.of_iso
      ((baseChangeCompIso q (V x).ι H).symm ≪≫
        (Descent.pullbackComparison (U x).ι v ((V x).ι ≫ q)
          (q.resLE_comp_ι (U := U x) (V := V x) le_rfl) H).symm)
      ((hTU x).baseChange v)
  have hcomp : q ≫ Spec.algebraMap R B = Spec.algebraMap R (C.restrictScalars R) := by
    simp only [q, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hfin : Algebra.FiniteType R C :=
    Algebra.FiniteType.trans inferInstance ((Subalgebra.fg_iff_finiteType C).mp hC)
  exact ⟨C.restrictScalars R, (Subalgebra.fg_iff_finiteType _).mpr hfin,
    IsTorus.of_iso (Descent.pullbackComparison (Spec.algebraMap R B) q _ hcomp G).symm hHC⟩

end Langlands.GroupScheme.RelativeTorus
