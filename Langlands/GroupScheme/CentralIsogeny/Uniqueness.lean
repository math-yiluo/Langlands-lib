import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.Topology.LocallyConstant.Basic

/-! # Cancellation through homomorphisms with finite kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Difference

variable {S : Scheme.{u}} {C H G : GroupScheme S}

/-- The quotient of two homomorphisms with equal composite, as a morphism into the full
scheme-theoretic kernel. It need not be a group homomorphism. -/
def kernelDifference (q : H ⟶ G) (a b : C ⟶ H) (hab : a ≫ q = b ≫ q) :
    C.X ⟶ (kernel q).X :=
  (kernelPointsEquiv q C.X).symm ⟨a.hom.hom / b.hom.hom, by
    change (a.hom.hom / b.hom.hom) ≫ q.hom.hom = 1
    rw [GrpObj.div_comp, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hab, div_self']⟩

/-- The kernel difference has the intended quotient as its composite with the inclusion. -/
theorem kernelDifference_comp (q : H ⟶ G) (a b : C ⟶ H)
    (hab : a ≫ q = b ≫ q) :
    kernelDifference q a b hab ≫ (kernelι q).hom.hom = a.hom.hom / b.hom.hom :=
  congrArg Subtype.val ((kernelPointsEquiv q C.X).apply_symm_apply _)

/-- The kernel difference takes the identity of the source to the kernel identity. -/
theorem kernelDifference_one (q : H ⟶ G) (a b : C ⟶ H)
    (hab : a ≫ q = b ≫ q) :
    η[C.X] ≫ kernelDifference q a b hab = η[(kernel q).X] := by
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [Category.assoc, kernelDifference_comp, GrpObj.comp_div, IsMonHom.one_hom,
    IsMonHom.one_hom, div_self', IsMonHom.one_hom]
  exact (MonObj.one_eq_one H.X).symm

end Difference

variable {k : Type u} [Field k]

/-- Over an algebraically closed field, maps from a connected reduced scheme into a finite
scheme agree if they agree at a single point. -/
theorem finiteTargetHom_ext_algClosed [IsAlgClosed k]
    {X Y : Scheme.{u}} (i : Y ⟶ Spec (CommRingCat.of k)) [IsFinite i]
    [IsReduced X] [PreconnectedSpace X] {f g : X ⟶ Y}
    [LocallyOfFiniteType (f ≫ i)] (h : f ≫ i = g ≫ i)
    (x : X) (hx : f x = g x) : f = g := by
  have : IsLocallyArtinian Y := .of_locallyQuasiFinite i
  have hf : IsLocallyConstant (fun z : X => f z) :=
    (IsLocallyConstant.iff_continuous _).mpr f.continuous
  have hg : IsLocallyConstant (fun z : X => g z) :=
    (IsLocallyConstant.iff_continuous _).mpr g.continuous
  apply AlgebraicGeometry.ext_of_apply_eq i Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro y _ _
    exact (hf.apply_eq_of_preconnectedSpace y x).trans
      (hx.trans (hg.apply_eq_of_preconnectedSpace x y))
  · exact h

/-- A morphism from a connected reduced algebraic group to a finite group scheme is
the unit morphism if it preserves the unit. -/
theorem finiteTargetOverHom_eq_one_algClosed [IsAlgClosed k]
    (C F : GroupScheme (Spec (CommRingCat.of k)))
    [IsReduced C.X.left] [PreconnectedSpace C.X.left] [LocallyOfFiniteType C.X.hom]
    [IsFinite F.X.hom] (d : C.X ⟶ F.X)
    (hd : η[C.X] ≫ d = η[F.X]) : d = 1 := by
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (d.left ≫ F.X.hom) := by
    rw [Over.w]
    infer_instance
  apply finiteTargetHom_ext_algClosed F.X.hom (by simp only [Over.w])
    (η[C.X].left (IsLocalRing.closedPoint k))
  have hde : η[C.X] ≫ d = η[C.X] ≫ (1 : C.X ⟶ F.X) := by
    rw [MonObj.comp_one, hd, ← MonObj.one_eq_one]
  exact congrArg (fun e => e.left (IsLocalRing.closedPoint k)) hde

/-- Cancellation for homomorphisms out of a connected reduced algebraic group, over an
algebraically closed field, when the full scheme-theoretic kernel is finite. -/
theorem finiteKernel_cancel_algClosed [IsAlgClosed k]
    {C H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsReduced C.X.left] [PreconnectedSpace C.X.left] [LocallyOfFiniteType C.X.hom]
    (q : H ⟶ G) [IsFinite (kernel q).X.hom]
    {a b : C ⟶ H} (hab : a ≫ q = b ≫ q) : a = b := by
  have hd1 := finiteTargetOverHom_eq_one_algClosed C (kernel q)
    (kernelDifference q a b hab) (kernelDifference_one q a b hab)
  apply Grp.hom_ext
  apply div_eq_one.mp
  rw [← kernelDifference_comp q a b hab, hd1, MonObj.one_comp]

/-- A finite group-scheme homomorphism can be cancelled on maps out of a smooth connected
affine group over any field. -/
theorem finiteHom_cancel
    {C H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (q : H ⟶ G) [IsFinite q.hom.hom.left]
    {a b : C ⟶ H} (hab : a ≫ q = b ≫ q) : a = b := by
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  have hff : Flat e ∧ Surjective e :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat e := hff.1
  have : Surjective e := hff.2
  have : (Over.pullback e).Faithful := inferInstance
  have : IsFinite (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) e q.hom.hom inferInstance
  have : IsFinite (kernel (B.map q)).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme (B.map q)) inferInstance
  have : Smooth (B.obj C).X.hom :=
    MorphismProperty.pullback_snd C.X.hom e inferInstance
  have : ConnectedSpace (B.obj C).X.left :=
    C.connectedSpace_baseChange_of_smooth_affine e
  have : IsReduced (B.obj C).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (AlgebraicClosure k) (B.obj C).X.left (B.obj C).X.hom
  have hab' : B.map a ≫ B.map q = B.map b ≫ B.map q := by
    rw [← B.map_comp, ← B.map_comp, hab]
  have heq : B.map a = B.map b := finiteKernel_cancel_algClosed (B.map q) hab'
  apply Grp.hom_ext
  apply (Over.pullback e).map_injective
  exact congrArg (fun f => f.hom.hom) heq

/-- In particular, a central isogeny admits at most one lift from a connected reductive
group scheme. -/
theorem IsCentralIsogeny.cancel_of_connectedReductive
    {C H G : GroupScheme (Spec (CommRingCat.of k))}
    (hC : IsConnectedReductive C) {q : H ⟶ G} (hq : IsCentralIsogeny q)
    {a b : C ⟶ H} (hab : a ≫ q = b ≫ q) : a = b := by
  have := hC.smooth
  have := hC.isAffineHom
  have := hC.connectedSpace
  have := hq.isFinite
  exact finiteHom_cancel q hab

end Langlands.GroupScheme
