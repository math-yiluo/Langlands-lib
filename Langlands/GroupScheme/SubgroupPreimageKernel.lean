import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # The actual kernel of a subgroup-preimage projection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.SubgroupPreimage

variable {S : Scheme.{u}} {G Q H : GroupScheme S} (q : G ⟶ Q) (j : H ⟶ Q)

private theorem kernelPullback :
    IsPullback (kernelι (projection q j) ≫ inclusion q j)
      (pullback.snd (projection q j) (kernelUnit H)) q (kernelUnit Q) := by
  have hunit : kernelUnit H ≫ j = kernelUnit Q := Subsingleton.elim _ _
  have hp := (IsPullback.of_hasPullback (projection q j) (kernelUnit H)).paste_horiz
    (IsPullback.of_hasPullback q j)
  rw [hunit] at hp
  exact hp

/-- Taking the actual inverse image of any homomorphism leaves the full kernel
of its projection canonically isomorphic to the original full kernel. -/
def kernelIso : kernel (projection q j) ≅ kernel q :=
  (kernelPullback q j).isoPullback

/-- The comparison preserves the original kernel inclusion into the source. -/
@[reassoc]
theorem kernelIso_hom_comp :
    (kernelIso q j).hom ≫ kernelι q =
      kernelι (projection q j) ≫ inclusion q j :=
  (kernelPullback q j).isoPullback_hom_fst

/-- The comparison after forgetting the group structure over the original base. -/
def kernelOverIso : (kernel (projection q j)).X ≅ (kernel q).X :=
  (Grp.forget (Over S)).mapIso (kernelIso q j)

/-- Quasi-compactness of the original projection survives its actual inverse image. -/
theorem quasiCompact_projection [QuasiCompact q.hom.hom.left] :
    QuasiCompact (projection q j).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance

/-- Affineness of the original full kernel transfers to the new full kernel. -/
theorem isAffineHom_kernel [IsAffineHom (kernel q).X.hom] :
    IsAffineHom (kernel (projection q j)).X.hom := by
  let e := kernelOverIso q j
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

section Field

variable {k : Type u} [Field k]
    {G Q H : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ Q) (j : H ⟶ Q)

/-- Unipotence of the original full kernel transfers to the new full kernel. -/
theorem isUnipotent_kernel (hK : IsUnipotent (kernel q)) :
    IsUnipotent (kernel (projection q j)) :=
  hK.of_iso (kernelIso q j)

end Field

end Langlands.GroupScheme.SubgroupPreimage
