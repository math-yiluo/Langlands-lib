import Langlands.GroupScheme.SubgroupFunctor.KernelCell
import Langlands.GroupScheme.SubgroupFunctor.UnipotentCell
import Langlands.GroupScheme.Dynamic.BaseOppositeCellProof
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Unipotent kernel coverage by an open binary cell -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {k : Type u} [Field k]

/-- Open multiplication of smooth affine unipotent factors is an isomorphism
over any field when the affine finite-type ambient group is connected. -/
theorem isIso_cellMultiplication_of_unipotent_overField
    {G U P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left]
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    [Smooth P.X.hom] [IsAffineHom P.X.hom]
    (i : U ⟶ G) (p : P ⟶ G)
    (hU : IsUnipotent U) (hP : IsUnipotent P)
    (hopen : IsOpenImmersion (cellMultiplication i p).left) :
    IsIso (cellMultiplication i p) := by
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have hb : Surjective b := (fieldExtension_fpqc k K).1
  have : Smooth (B.obj U).X.hom :=
    inferInstanceAs (Smooth (pullback.snd U.X.hom b))
  have : Smooth (B.obj P).X.hom :=
    inferInstanceAs (Smooth (pullback.snd P.X.hom b))
  have : IsAffineHom (B.obj U).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd U.X.hom b))
  have : IsAffineHom (B.obj P).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd P.X.hom b))
  have : IsAffineHom (B.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : LocallyOfFiniteType (B.obj G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : ConnectedSpace (B.obj G).X.left :=
    connectedSpace_baseChange_of_connected G b
  have hcIso : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X).left := by
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map
      (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X))
    infer_instance
  have hbc : IsOpenImmersion
      ((Over.pullback b).map (cellMultiplication i p)).left := by
    exact MorphismProperty.of_isPullback
      (overBaseChange_isPullback b (cellMultiplication i p)).flip hopen
  have hcell : IsOpenImmersion (cellMultiplication (B.map i) (B.map p)).left := by
    rw [DynamicBaseOppositeCell.baseChange_cellMultiplication, Over.comp_left] at hbc
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X).left _).mp hbc
  have : IsIso (cellMultiplication (B.map i) (B.map p)) :=
    isIso_cellMultiplication_of_unipotent (B.map i) (B.map p)
      (hU.baseChange (K := K)) (hP.baseChange (K := K)) hcell
  have : IsIso (cellMultiplication (B.map i) (B.map p)).left :=
    (Over.forget (Spec (CommRingCat.of K))).map_isIso
      (cellMultiplication (B.map i) (B.map p))
  have hsurj : Surjective
      ((Over.pullback b).map (cellMultiplication i p)).left := by
    rw [DynamicBaseOppositeCell.baseChange_cellMultiplication, Over.comp_left]
    infer_instance
  have : Surjective (cellMultiplication i p).left :=
    surjective_overHom_of_baseChange b (cellMultiplication i p) hsurj
  have : IsIso (cellMultiplication i p).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, inferInstance⟩
  have : IsIso ((Over.forget _).map (cellMultiplication i p)) :=
    ‹IsIso (cellMultiplication i p).left›
  exact isIso_of_reflects_iso _ (Over.forget _)

namespace KernelCell

section GeneralBase

variable {S : Scheme.{u}} {G H U V : GroupScheme S}
    (f : U ⟶ V) (q : G ⟶ H) (i : U ⟶ G) (j : V ⟶ H)
    (hi : i ≫ q = f ≫ j)

/-- A closed subgroup inclusion gives a closed map between the actual kernels. -/
theorem isClosedSubgroup_kernelHom [IsSeparated V.X.hom]
    (hclosed : IsClosedSubgroup i) : IsClosedSubgroup (kernelHom f q i j hi) := by
  have : IsClosedImmersion i.hom.hom.left := hclosed
  have hc : IsClosedImmersion
      ((kernelHom f q i j hi).hom.hom.left ≫ (kernelι q).hom.hom.left) := by
    change IsClosedImmersion ((kernelHom f q i j hi ≫ kernelι q).hom.hom.left)
    rw [kernelHom_ι]
    change IsClosedImmersion ((kernelι f).hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have := hc
  have : Mono (kernelι q).hom.hom.left :=
    inferInstanceAs (Mono ((Over.forget S).map (kernelι q).hom.hom))
  exact IsClosedImmersion.of_comp _ (kernelι q).hom.hom.left

/-- The actual kernel of a smooth homomorphism is smooth over the base. -/
theorem smooth_kernel [Smooth f.hom.hom.left] : Smooth (kernel f).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance

end GeneralBase

variable {G H U V P R : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ H) (f : U ⟶ V) (g : P ⟶ R)
    (i : U ⟶ G) (p : P ⟶ G) (j : V ⟶ H) (r : R ⟶ H)
    (hi : i ≫ q = f ≫ j) (hp : p ≫ q = g ≫ r)
    [IsSeparated V.X.hom] [IsSeparated R.X.hom]
    [IsAffineHom U.X.hom] [IsAffineHom P.X.hom]
    [Smooth f.hom.hom.left] [Smooth g.hom.hom.left]
    [IsAffineHom (kernel q).X.hom] [LocallyOfFiniteType (kernel q).X.hom]
    [ConnectedSpace (kernel q).X.left]
    [Mono (cellMultiplication j r)]
    [IsOpenImmersion (cellMultiplication i p).left]

/-- The actual kernel cell is an isomorphism if the ambient kernel is connected
and unipotent, the original factor inclusions are closed, and their quotient
maps are smooth. This holds over the original arbitrary field. -/
def unipotentKernelCellIso
    (hiClosed : IsClosedSubgroup i) (hpClosed : IsClosedSubgroup p)
    (hK : IsUnipotent (kernel q)) :
    (kernel f).X ⊗ (kernel g).X ≅ (kernel q).X := by
  have : Smooth (kernel f).X.hom := smooth_kernel f
  have : Smooth (kernel g).X.hom := smooth_kernel g
  have : IsAffineHom (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have : IsAffineHom (kernel g).X.hom := by
    rw [← Over.w (kernelι g).hom.hom]
    infer_instance
  have hf := unipotentClosedSubgroup k (kernel q) (kernel f) (kernelHom f q i j hi)
    (isClosedSubgroup_kernelHom f q i j hi hiClosed) hK
  have hg := unipotentClosedSubgroup k (kernel q) (kernel g) (kernelHom g q p r hp)
    (isClosedSubgroup_kernelHom g q p r hp hpClosed) hK
  have : IsIso (multiplication q f g i p j r hi hp) :=
    isIso_cellMultiplication_of_unipotent_overField
    (kernelHom f q i j hi) (kernelHom g q p r hp) hf hg
    (isOpenImmersion_multiplication q f g i p j r hi hp)
  exact asIso (multiplication q f g i p j r hi hp)

@[simp] theorem unipotentKernelCellIso_hom
    (hiClosed : IsClosedSubgroup i) (hpClosed : IsClosedSubgroup p)
    (hK : IsUnipotent (kernel q)) :
    (unipotentKernelCellIso q f g i p j r hi hp hiClosed hpClosed hK).hom =
      multiplication q f g i p j r hi hp := rfl

/-- Every point of the full ambient kernel factors through the original cell,
as an actual morphism over the original field. -/
def kernelChart
    (hiClosed : IsClosedSubgroup i) (hpClosed : IsClosedSubgroup p)
    (hK : IsUnipotent (kernel q)) : (kernel q).X ⟶ U.X ⊗ P.X :=
  (unipotentKernelCellIso q f g i p j r hi hp hiClosed hpClosed hK).inv ≫ inclusion f g

@[reassoc]
theorem kernelChart_comp
    (hiClosed : IsClosedSubgroup i) (hpClosed : IsClosedSubgroup p)
    (hK : IsUnipotent (kernel q)) :
    kernelChart q f g i p j r hi hp hiClosed hpClosed hK ≫ cellMultiplication i p =
      (kernelι q).hom.hom := by
  unfold kernelChart
  rw [Category.assoc, ← multiplication_ι]
  change (unipotentKernelCellIso q f g i p j r hi hp hiClosed hpClosed hK).inv ≫
    (unipotentKernelCellIso q f g i p j r hi hp hiClosed hpClosed hK).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

end KernelCell

end Langlands.GroupScheme.SubgroupFunctor
