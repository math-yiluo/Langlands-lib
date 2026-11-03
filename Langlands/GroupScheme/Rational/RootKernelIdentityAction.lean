import Langlands.GroupScheme.Rational.RootKernelIdentityTorus
import Langlands.GroupScheme.Rational.CharacterFpqcProof

/-! # The descended action on a root-kernel centralizer's identity component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {H C G : GroupScheme B}

/-- Conjugation commutes with a homomorphism on every test scheme. -/
theorem conjugation_act_comp (i : H ⟶ C) (j : C ⟶ G)
    {U : Over B} (s : U ⟶ H.X) (c : U ⟶ C.X) :
    (conjugation i).act s c ≫ j.hom.hom =
      (conjugation (i ≫ j)).act s (c ≫ j.hom.hom) := by
  simp only [conjugation_act, MonObj.mul_comp, GrpObj.inv_comp,
    Grp.comp_hom_hom, Category.assoc]

end AutomorphicAction

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)

/-- The actual torus conjugation action on the identity component of the
represented full character-kernel centralizer. -/
def kernelCentralizerIdentityAction :
    AutomorphicAction T.toGrp (identityComponent C) :=
  AutomorphicAction.conjugation (kernelCentralizerIdentityTorus i hT a j hj)

/-- The action agrees with ambient torus conjugation after the actual inclusion. -/
theorem kernelCentralizerIdentityAction_act_comp_ambient
    {U : Over (Spec (CommRingCat.of k))} (s : U ⟶ T.X)
    (c : U ⟶ (identityComponent C).X) :
    (kernelCentralizerIdentityAction i hT a j hj).act s c ≫
        (identityComponentι C ≫ j).hom.hom =
      (AutomorphicAction.conjugation i).act s
        (c ≫ (identityComponentι C ≫ j).hom.hom) := by
  rw [kernelCentralizerIdentityAction, AutomorphicAction.conjugation_act_comp,
    kernelCentralizerIdentityTorus_comp_ambient]

/-- The inclusion of the identity component intertwines its torus action with
the existing action on the whole represented centralizer. -/
theorem kernelCentralizerIdentityAction_act_comp
    {U : Over (Spec (CommRingCat.of k))} (s : U ⟶ T.X)
    (c : U ⟶ (identityComponent C).X) :
    (kernelCentralizerIdentityAction i hT a j hj).act s c ≫
        (identityComponentι C).hom.hom =
      (centralizerAction i a j hj).act s (c ≫ (identityComponentι C).hom.hom) := by
  have : Mono j.hom.hom := hj.1
  have haction :
      (centralizerAction i a j hj).act s (c ≫ (identityComponentι C).hom.hom) ≫
          j.hom.hom =
        (AutomorphicAction.conjugation i).act s
          ((c ≫ (identityComponentι C).hom.hom) ≫ j.hom.hom) :=
    AutomorphicAction.onRepresentedFixedSubgroup_act_comp
      (AutomorphicAction.conjugation i) (characterKernelι a) j hj s
        (c ≫ (identityComponentι C).hom.hom)
  apply (cancel_mono j.hom.hom).mp
  calc
    ((kernelCentralizerIdentityAction i hT a j hj).act s c ≫
        (identityComponentι C).hom.hom) ≫ j.hom.hom =
        (AutomorphicAction.conjugation i).act s
          (c ≫ (identityComponentι C ≫ j).hom.hom) := by
      rw [Category.assoc, ← Grp.comp_hom_hom,
        kernelCentralizerIdentityAction_act_comp_ambient]
    _ = (centralizerAction i a j hj).act s
        (c ≫ (identityComponentι C).hom.hom) ≫ j.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using haction.symm

/-- The entire scheme-theoretic character kernel acts trivially on the actual
identity component, including on nonreduced test schemes. -/
theorem kernelCentralizerIdentityAction_kernelActsTrivially :
    (kernelCentralizerIdentityAction i hT a j hj).KernelActsTrivially
      (CommGroupScheme.groupHom a) := by
  intro U c g
  apply (cancel_mono (identityComponentι C).hom.hom).mp
  rw [AutomorphicAction.restrict_act, kernelCentralizerIdentityAction_act_comp]
  simpa only [AutomorphicAction.restrict_act] using
    centralizerAction_kernelActsTrivially i a j hj U c
      (g ≫ (identityComponentι C).hom.hom)

section Fpqc

variable [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- Descend the identity-component conjugation action through the actual
fpqc character, without replacing its possibly nonsmooth kernel. -/
def kernelCentralizerIdentityQuotientAction :
    AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp (identityComponent C) :=
  AutomorphicAction.quotientAction (kernelCentralizerIdentityAction i hT a j hj)
    (CommGroupScheme.groupHom a)
    (kernelCentralizerIdentityAction_kernelActsTrivially i hT a j hj)

/-- Pullback through the character is exactly torus conjugation on the component. -/
theorem kernelCentralizerIdentityQuotientAction_restrict :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).restrict
        (CommGroupScheme.groupHom a) = kernelCentralizerIdentityAction i hT a j hj :=
  AutomorphicAction.quotientAction_restrict _ _ _

/-- The component inclusion intertwines both actual descended actions on every
test scheme, even when the acting point has no global lift through the character. -/
theorem kernelCentralizerIdentityQuotientAction_act_comp
    {U : Over (Spec (CommRingCat.of k))}
    (z : U ⟶ (Gm (Spec (CommRingCat.of k))).X)
    (c : U ⟶ (identityComponent C).X) :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).act z c ≫
        (identityComponentι C).hom.hom =
      (quotientAction i a j hj).act z (c ≫ (identityComponentι C).hom.hom) := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift
    (CommGroupScheme.groupHom a) z
  intro V b s hs
  rw [← Category.assoc,
    (kernelCentralizerIdentityQuotientAction i hT a j hj).naturality,
    (quotientAction i a j hj).naturality, hs]
  change
    (AutomorphicAction.quotientAction _ _ _).act
          (s ≫ (CommGroupScheme.groupHom a).hom.hom) (b ≫ c) ≫
        (identityComponentι C).hom.hom =
      (AutomorphicAction.quotientAction _ _ _).act
        (s ≫ (CommGroupScheme.groupHom a).hom.hom)
        (b ≫ c ≫ (identityComponentι C).hom.hom)
  rw [AutomorphicAction.quotientAction_act_lift,
    AutomorphicAction.quotientAction_act_lift,
    kernelCentralizerIdentityAction_act_comp]
  simp only [Category.assoc]

end Fpqc

/-- Every nonzero character of the split torus gives a unique actual descended
action on the identity component; no separate fpqc premise is needed. -/
theorem existsUnique_kernelCentralizerIdentityQuotientAction (ha : a ≠ 0) :
    ∃! b : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp
        (identityComponent C),
      b.restrict (CommGroupScheme.groupHom a) =
        kernelCentralizerIdentityAction i hT a j hj := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT a ha
  exact ⟨kernelCentralizerIdentityQuotientAction i hT a j hj,
    kernelCentralizerIdentityQuotientAction_restrict i hT a j hj,
    fun b hb => AutomorphicAction.quotientAction_unique _ _ _ b hb⟩

end RelativeRoot

end Langlands.GroupScheme
