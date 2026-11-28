import Langlands.Algebra.NilpotentAdjointEulerElement
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.CentralIsogeny.AlmostSimpleTransfer
import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.CommutingSemisimpleTorus
import Langlands.GroupScheme.Lie.SemisimpleJordanCentralizer
import Langlands.GroupScheme.Lie.SemisimpleLieAlgebraCharZeroProof
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.ZeroTangentTriviality
import Langlands.GroupScheme.Rational.AnisotropicTorusTangentEigenvalues
import Langlands.GroupScheme.Reductive.PerfectFieldProof

/-! # Connected closed subgroups of anisotropic semisimple groups in characteristic zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Lie Langlands.LinearAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private theorem jordanSemisimplePart_apply_eq_self
    {k : Type u} [Field k] [PerfectField k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : End k V) {v : V} (hv : D v = v) : jordanSemisimplePart D v = v := by
  let T := LinearMap.toSpanSingleton k V v
  have hT : D.comp T = T.comp (1 : End k k) := by
    apply LinearMap.ext
    intro a
    simp [T, hv]
  have hone : jordanSemisimplePart (1 : End k k) = 1 :=
    jordanSemisimplePart_eq_of_decomposition 1 0 1
      (by simp) Module.End.isSemisimple_id (Commute.zero_left _) (zero_add 1).symm
  have h := LinearMap.congr_fun (jordanSemisimplePart_intertwines T hT) 1
  simpa [T, hone] using h

section SemisimpleAmbient

variable {k : Type u} [Field k] [CharZero k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]

omit [CharZero k] [LocallyOfFiniteType G.X.hom] in
private local instance affineTangentLieRing : LieRing (Additive (lieKernel G k)) :=
  instAffineKernelLieRing (R := CommRingCat.of k) (A := k) G

omit [CharZero k] [LocallyOfFiniteType G.X.hom] in
private local instance affineTangentLieAlgebra : LieAlgebra k (Additive (lieKernel G k)) :=
  instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := k) G

omit [CharZero k] in
private theorem isNilpotent_ad_of_adjoint_tangent {d : ℕ} (c : FiniteCoordinates G d)
    (X : lieKernel G k) (hX : IsNilpotent ((adjointRepresentation c).tangentMatrix k X)) :
    IsNilpotent (LieAlgebra.ad k (Additive (lieKernel G k)) (Additive.ofMul X)) := by
  let e : Additive (lieKernel G k) ≃ₗ[k] (Fin d → k) :=
    c.equiv (CommAlgCat.of (CommRingCat.of k) k)
  let E := e.conjAlgEquiv k
  let M : Matrix (Fin d) (Fin d) k ≃ₐ[k] End k (Fin d → k) := Matrix.toLinAlgEquiv'
  have hconj : E (LieAlgebra.ad k (Additive (lieKernel G k)) (Additive.ofMul X)) =
      M ((adjointRepresentation c).tangentMatrix k X) := by
    apply LinearMap.ext
    intro v
    obtain ⟨Y, rfl⟩ := e.surjective v
    rw [LinearEquiv.conjAlgEquiv_apply_apply, LinearEquiv.symm_apply_apply, LieAlgebra.ad_apply]
    exact (adjointDifferentialLieHom_apply_bracket c (Additive.ofMul X) Y).symm
  apply (IsNilpotent.map_iff E.injective).mp
  rw [hconj]
  exact hX.map M

private theorem eq_one_of_isNilpotent_adjoint_tangent
    (hG : IsAnisotropic G) (hss : IsSemisimple G) {d : ℕ} (c : FiniteCoordinates G d)
    (X : lieKernel G k) (hX : IsNilpotent ((adjointRepresentation c).tangentMatrix k X)) :
    X = 1 := by
  let L := Additive (lieKernel G k)
  let e : L ≃ₗ[k] (Fin d → k) := c.equiv (CommAlgCat.of (CommRingCat.of k) k)
  let : FiniteDimensional k L := FiniteDimensional.of_injective e.toLinearMap e.injective
  let : LieAlgebra.HasTrivialRadical k L := semisimpleLieAlgebraCharZero k G hss
  let : Smooth G.X.hom := hss.isConnectedReductive.smooth
  let x : L := Additive.ofMul X
  obtain ⟨h, hh⟩ := Langlands.exists_lie_eq_of_isNilpotent_ad x (isNilpotent_ad_of_adjoint_tangent c X hX)
  by_contra hne
  have hv : e x ≠ 0 := fun hz => hne (e.injective (hz.trans e.map_zero.symm))
  let Y := semisimpleKernel G h.toMul
  obtain ⟨T, i, hi, hLift⟩ := exists_isMaximalTorus_forall_tangent_of_pairwise
    1 G [Y] rfl
      (fun Z hZ => (List.mem_singleton.mp hZ).symm ▸ isSemisimpleElement_semisimpleKernel G h.toMul)
      (by simp)
  obtain ⟨Z, hZ⟩ := hLift Y (by simp)
  have hLinear : adjointDifferentialFamily c h (e x) = e x :=
    (adjointDifferentialLieHom_apply_bracket c h x).trans (congrArg e hh)
  have hMatrix : ((adjointRepresentation c).restrict i).tangentMatrix k Z *ᵥ e x =
      (1 : k) • e x := by
    rw [MatrixRepresentation.tangentMatrix_restrict, hZ, one_smul]
    change adjointDifferentialFamily c (Additive.ofMul Y) (e x) = e x
    rw [adjointDifferentialFamily_semisimpleKernel]
    exact jordanSemisimplePart_apply_eq_self _ hLinear
  exact one_ne_zero (hG.tangentMatrix_eigenvalue_eq_zero hi.2.1 hi.1 _ Z 1 (e x) hv hMatrix)

/-- Every connected unipotent closed subgroup of an anisotropic semisimple group
in characteristic zero has trivial image on all tests. -/
theorem IsAnisotropic.range_eq_bot_of_isUnipotent_of_isSemisimple
    (hG : IsAnisotropic G) (hss : IsSemisimple G)
    {U : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G}
    (hi : IsClosedSubgroup i) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U) :
    SubgroupFunctor.range i = ⊥ := by
  let : IsAffineHom U.X.hom := hi.isAffineHom
  let : LocallyOfFiniteType U.X.hom := hi.locallyOfFiniteType
  let : Mono i.hom.hom := hi.mono_overHom
  let c := finiteCoordinates G
  have htriv (X : lieKernel U k) : X = 1 := by
    have hn := MatrixRepresentation.isNilpotent_tangentMatrix_of_isUnipotent
      hu ((adjointRepresentation c).restrict i) k X
    rw [MatrixRepresentation.tangentMatrix_restrict] at hn
    have h := eq_one_of_isNilpotent_adjoint_tangent hG hss c _ hn
    apply Subtype.ext
    apply (cancel_mono i.hom.hom).mp
    change X.val ≫ i.hom.hom = 1 ≫ i.hom.hom
    rw [MonObj.one_comp]
    exact congrArg Subtype.val h
  let : Subsingleton (lieKernel U k) := ⟨fun X Y => (htriv X).trans (htriv Y).symm⟩
  apply SubgroupFunctor.ext
  intro W
  rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  rw [points_eq_one_of_subsingleton_lieKernel U W y, MonObj.one_comp]

/-- A connected closed subgroup of an anisotropic semisimple group over a
characteristic-zero field is reductive. -/
theorem IsAnisotropic.isConnectedReductive_of_closed_of_isSemisimple
    (hG : IsAnisotropic G) (hss : IsSemisimple G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}
    (hi : IsClosedSubgroup i) (hconn : ConnectedSpace H.X.left) : IsConnectedReductive H := by
  have hs : Smooth H.X.hom := affineCartierSmooth k H hi.isAffineHom hi.locallyOfFiniteType
  refine (perfectFieldPseudoReductive k H).mp ⟨hs, hi.isAffineHom, hconn, ?_⟩
  intro U j hj _ hconnU hu _
  have htriv := hG.range_eq_bot_of_isUnipotent_of_isSemisimple hss (hj.comp hi) hconnU hu
  let : Mono i.hom.hom := hi.mono_overHom
  apply (SubgroupFunctor.range_eq_bot_iff_hom_eq_one j).2
  apply (cancel_mono i.hom.hom).mp
  simpa only [Grp.comp_hom_hom, MonObj.one_comp] using
    (SubgroupFunctor.range_eq_bot_iff_hom_eq_one (j ≫ i)).1 htriv

end SemisimpleAmbient

/-- Reductivity of connected closed subgroups of anisotropic semisimple groups
over characteristic-zero fields. -/
def AnisotropicConnectedSubgroupReductivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
      (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G → IsSemisimple G →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → ConnectedSpace H.X.left → IsConnectedReductive H

theorem anisotropicConnectedSubgroupReductivity : AnisotropicConnectedSubgroupReductivityStatement.{u} :=
  fun _ _ _ _ _ _ hG hss _ _ hi hconn =>
    hG.isConnectedReductive_of_closed_of_isSemisimple hss hi hconn

end Langlands.GroupScheme
