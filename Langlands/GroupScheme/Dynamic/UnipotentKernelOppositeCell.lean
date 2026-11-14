import Langlands.GroupScheme.SubgroupFunctor.UnipotentKernelCell
import Langlands.GroupScheme.SubgroupFunctor.CellKernelSaturation
import Langlands.GroupScheme.Dynamic.UnipotentQuotient
import Langlands.GroupScheme.Dynamic.ParabolicQuotient
import Langlands.GroupScheme.Dynamic.OppositeCellMono
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Opposite dynamic cells under quotients with unipotent kernel -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth Q.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace Q.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (q : G ⟶ Q)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)
    [ConnectedSpace (kernel q).X.left] (hK : IsUnipotent (kernel q))
    {U P V R : GroupScheme (Spec (CommRingCat.of k))}
    (i : U ⟶ G) (p : P ⟶ G) (j : V ⟶ Q) (r : R ⟶ Q)
    (hi : (unipotent (oppositeCocharacter χ)).IsRepresentedBy i)
    (hp : (parabolic χ).IsRepresentedBy p)
    (hj : (unipotent (oppositeCocharacter (χ ≫ q))).IsRepresentedBy j)
    (hr : (parabolic (χ ≫ q)).IsRepresentedBy r)

include hi hp hj hr hqs hqsurj hK in
/-- The full connected unipotent kernel lies in the opposite dynamic cell,
with an actual chart over the original field. -/
theorem exists_oppositeCellKernelChart :
    ∃ κ : (kernel q).X ⟶ U.X ⊗ P.X,
      κ ≫ SubgroupFunctor.cellMultiplication i p = (kernelι q).hom.hom := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hj' : (unipotent (oppositeCocharacter χ ≫ q)).IsRepresentedBy j := by
    simpa only [oppositeCocharacter, Category.assoc] using hj
  obtain ⟨f, hf, hfs, _⟩ :=
    exists_unipotentQuotientHom (oppositeCocharacter χ) q hqs hqsurj i j hi hj'
  obtain ⟨g, hg, hgs, _⟩ :=
    exists_parabolicQuotientHom χ q hqs hqsurj p r hp hr
  have hiClosed := Affine.isClosedSubgroup_of_isRepresentedBy_unipotent _ hi
  have hpClosed := Affine.isClosedSubgroup_of_isRepresentedBy_parabolic _ hp
  have hjClosed := Affine.isClosedSubgroup_of_isRepresentedBy_unipotent _ hj
  have hrClosed := Affine.isClosedSubgroup_of_isRepresentedBy_parabolic _ hr
  have : IsClosedImmersion i.hom.hom.left := hiClosed
  have : IsClosedImmersion p.hom.hom.left := hpClosed
  have : IsClosedImmersion j.hom.hom.left := hjClosed
  have : IsClosedImmersion r.hom.hom.left := hrClosed
  have : IsAffineHom U.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  have : IsAffineHom P.X.hom := by rw [← Over.w p.hom.hom]; infer_instance
  have : IsSeparated V.X.hom := by rw [← Over.w j.hom.hom]; infer_instance
  have : IsSeparated R.X.hom := by rw [← Over.w r.hom.hom]; infer_instance
  have : Smooth f.hom.hom.left := hfs
  have : Smooth g.hom.hom.left := hgs
  have : Smooth q.hom.hom.left := hqs
  have : Smooth (kernel q).X.hom := SubgroupFunctor.KernelCell.smooth_kernel q
  have : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : Mono (SubgroupFunctor.cellMultiplication j r) :=
    mono_oppositeCellMul (χ ≫ q) hj hr
  have : IsOpenImmersion (SubgroupFunctor.cellMultiplication i p).left :=
    dynamicBaseOppositeCell _ G χ U P i p hi hp
  exact ⟨SubgroupFunctor.KernelCell.kernelChart q f g i p j r hf hg hiClosed hpClosed hK,
    SubgroupFunctor.KernelCell.kernelChart_comp q f g i p j r hf hg hiClosed hpClosed hK⟩

/-- The chosen chart of the full kernel through the opposite dynamic cell. -/
def oppositeCellKernelChart : (kernel q).X ⟶ U.X ⊗ P.X :=
  (exists_oppositeCellKernelChart χ q hqs hqsurj hK i p j r hi hp hj hr).choose

@[reassoc]
theorem oppositeCellKernelChart_comp :
    oppositeCellKernelChart χ q hqs hqsurj hK i p j r hi hp hj hr ≫
      SubgroupFunctor.cellMultiplication i p = (kernelι q).hom.hom :=
  (exists_oppositeCellKernelChart χ q hqs hqsurj hK i p j r hi hp hj hr).choose_spec

include hi hp hj hr hqs hqsurj hK in
/-- Membership in the opposite dynamic cell is the inverse image of membership
in the quotient opposite cell, on every test scheme over the original field. -/
theorem oppositeCell_exists_lift_iff {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ G.X) :
    (∃ a : T ⟶ U.X ⊗ P.X, a ≫ SubgroupFunctor.cellMultiplication i p = x) ↔
      ∃ b : T ⟶ V.X ⊗ R.X,
        b ≫ SubgroupFunctor.cellMultiplication j r = x ≫ q.hom.hom := by
  have hj' : (unipotent (oppositeCocharacter χ ≫ q)).IsRepresentedBy j := by
    simpa only [oppositeCocharacter, Category.assoc] using hj
  obtain ⟨f, hf, _, hfsurj⟩ :=
    exists_unipotentQuotientHom (oppositeCocharacter χ) q hqs hqsurj i j hi hj'
  obtain ⟨g, hg, _, hgsurj⟩ :=
    exists_parabolicQuotientHom χ q hqs hqsurj p r hp hr
  have : Surjective f.hom.hom.left := hfsurj
  have : Surjective g.hom.hom.left := hgsurj
  have : IsOpenImmersion (SubgroupFunctor.cellMultiplication i p).left :=
    dynamicBaseOppositeCell _ G χ U P i p hi hp
  exact SubgroupFunctor.KernelCell.exists_lift_iff q i p
    (oppositeCellKernelChart χ q hqs hqsurj hK i p j r hi hp hj hr)
    (oppositeCellKernelChart_comp χ q hqs hqsurj hK i p j r hi hp hj hr)
    f g j r hf hg x

/-- Source opposite-cell coordinates of a point whose image has supplied
quotient opposite-cell coordinates. -/
def oppositeCellLift {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ G.X) (b : T ⟶ V.X ⊗ R.X)
    (hb : b ≫ SubgroupFunctor.cellMultiplication j r = x ≫ q.hom.hom) :
    T ⟶ U.X ⊗ P.X :=
  ((oppositeCell_exists_lift_iff χ q hqs hqsurj hK i p j r hi hp hj hr x).mpr ⟨b, hb⟩).choose

@[reassoc]
theorem oppositeCellLift_comp {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ G.X) (b : T ⟶ V.X ⊗ R.X)
    (hb : b ≫ SubgroupFunctor.cellMultiplication j r = x ≫ q.hom.hom) :
    oppositeCellLift χ q hqs hqsurj hK i p j r hi hp hj hr x b hb ≫
      SubgroupFunctor.cellMultiplication i p = x :=
  ((oppositeCell_exists_lift_iff χ q hqs hqsurj hK i p j r hi hp hj hr x).mpr ⟨b, hb⟩).choose_spec

end Langlands.GroupScheme.Dynamic
