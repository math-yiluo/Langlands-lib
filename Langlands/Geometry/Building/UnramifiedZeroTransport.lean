import Langlands.GroupScheme.Rational.ScalarExtensionNaturality
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.Geometry.Building.UnramifiedZeroIndependenceStatement
import Langlands.Geometry.Building.KPTorusNormNaturality
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.MaximalTransport

/-!
# Transport of the data of KP Definition 2.6.23(1) along automorphisms

* `rationalPoints.map_comp_apply` and `GaloisPointComparison.rationalExtend_map`: rational-point
  maps are functorial and commute with the extension of scalars `M(F) → M(K)`;
* `UnramifiedZeroDatum.transport`: the data for `H(K)^0` transported along an automorphism of
  `H`, with `zeroPoints_transport`: the automorphism carries `H(K)^0` for the old data onto
  `H(K)^0` for the transported data;
* `map_mem_anisotropicZeroPoints`: given the independence statement of KP Lemma 2.6.24
  (`UnramifiedZeroPointsIndependenceStatement`), every automorphism of an `F`-group `M`
  preserves `M(F)^0 = M(K)^0 ∩ M(F)`, the step of the proof of KP Lemma 2.6.24 that gives
  normality.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme

theorem rationalPoints.map_comp_apply {k : Type u} [Field k]
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    (f : G ⟶ H) (g : H ⟶ K) (x : rationalPoints G) :
    rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace UnramifiedZeroDatum

variable {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- The data of KP Definition 2.6.23(1) transported along an automorphism `e` of `H`: the
torus, the splitting field and the simply connected cover are kept, and the inclusions of the
torus and of the derived subgroup are composed with `e`. -/
def transport (E : UnramifiedZeroDatum F H) (e : H ≅ H) : UnramifiedZeroDatum F H where
  T := E.T
  i := E.i ≫ e.hom
  isMaximallySplitMaximalTorus := by
    obtain ⟨hT, A, a, f, ha, hf⟩ := E.isMaximallySplitMaximalTorus
    refine ⟨hT.comp_iso e, A, a ≫ e.hom, f, ha.comp_iso e, ?_⟩
    rw [← Category.assoc, hf]
  L := E.L
  isSplitTorus := E.isSplitTorus
  D := E.D
  C := E.C
  d := E.d ≫ e.hom
  π := E.π
  isSimplyConnectedDerivedCover :=
    ⟨E.isSimplyConnectedDerivedCover.isConnectedReductive,
      E.isSimplyConnectedDerivedCover.isDerivedSubgroup.comp_iso e,
      E.isSimplyConnectedDerivedCover.isSimplyConnectedCover⟩

theorem transport_simplyConnectedImage (E : UnramifiedZeroDatum F H) (e : H ≅ H) :
    (E.transport e).simplyConnectedImage =
      E.simplyConnectedImage.map (rationalPoints.map e.hom) :=
  (map_simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
    (E.transport e).isSimplyConnectedDerivedCover e).symm

theorem transport_torusIwahori (E : UnramifiedZeroDatum F H) (e : H ≅ H) :
    (E.transport e).torusIwahori = E.torusIwahori :=
  rfl

theorem transport_i (E : UnramifiedZeroDatum F H) (e : H ≅ H) :
    (E.transport e).i = E.i ≫ e.hom :=
  rfl

/-- An automorphism `e` carries `H(K)^0` for `E` onto `H(K)^0` for the transported data. -/
theorem zeroPoints_transport (E : UnramifiedZeroDatum F H) (e : H ≅ H) :
    (E.transport e).zeroPoints = E.zeroPoints.map (rationalPoints.map e.hom) := by
  rw [zeroPoints, zeroPoints, Subgroup.map_sup, transport_simplyConnectedImage, Subgroup.map_map]
  congr 1

end UnramifiedZeroDatum

/-- Given KP Lemma 2.6.24 (independence), every automorphism `α` of an `F`-group `M` that is
anisotropic modulo its center preserves `M(F)^0 = M(K)^0 ∩ M(F)`. -/
theorem map_mem_anisotropicZeroPoints (hind : UnramifiedZeroPointsIndependenceStatement.{u})
    {M : GroupScheme (Spec (CommRingCat.of F))}
    (E : UnramifiedZeroDatum F (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M))
    (α : M ≅ M) {m : rationalPoints M} (hm : m ∈ anisotropicZeroPoints E) :
    rationalPoints.map α.hom m ∈ anisotropicZeroPoints E := by
  rw [mem_anisotropicZeroPoints] at hm ⊢
  have hE := hind F _ (E.transport ((GroupScheme.baseChange
    (GaloisPointComparison.baseMap F (UnramifiedClosure F))).mapIso α)) E
  rw [UnramifiedZeroDatum.zeroPoints_transport, Functor.mapIso_hom] at hE
  rw [GaloisPointComparison.rationalExtend_map, ← hE]
  exact Subgroup.mem_map_of_mem _ hm

end Langlands.Geometry.Building
