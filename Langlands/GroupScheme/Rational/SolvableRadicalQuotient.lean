import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.HomImage

/-! # Quotients by represented solvable radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every smooth connected solvable normal closed subgroup is trivial on all
test schemes. This does not choose or assert existence of a radical. -/
def HasTrivialSolvableRadical {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
    IsSolvableGroupScheme H → (SubgroupFunctor.range j).IsNormal →
    SubgroupFunctor.range j = ⊥

namespace SubgroupPreimage

variable {S : Scheme.{u}} {R G Q H : GroupScheme S}
    (r : R ⟶ G) (q : G ⟶ Q) (j : H ⟶ Q)

/-- An inverse image is solvable on a test scheme if both the represented full
kernel and the target subgroup have solvable point groups on that test. -/
theorem isSolvable_points_of_kernel_range (hj : IsClosedSubgroup j)
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range r)
    (T : Over S) [Group.IsSolvable (T ⟶ R.X)] [Group.IsSolvable (T ⟶ H.X)] :
    Group.IsSolvable (T ⟶ (groupScheme q j).X) := by
  have : IsClosedImmersion (inclusion q j).hom.hom.left := isClosedSubgroup q j hj
  have : Mono (inclusion q j).hom.hom := Over.mono_of_mono_left _
  let p := IsMonHom.monoidHom (projection q j).hom.hom T
  let incl := IsMonHom.monoidHom (inclusion q j).hom.hom T
  let ρ := IsMonHom.monoidHom r.hom.hom T
  have : Group.IsSolvable ρ.range :=
    Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have hmem : ∀ x : p.ker, incl x ∈ ρ.range := by
    intro x
    have hx : (x : T ⟶ _) ≫ (projection q j).hom.hom = 1 := x.2
    have hker : incl x ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
      rw [mem_range_kernelι_iff]
      change ((x : T ⟶ _) ≫ (inclusion q j).hom.hom) ≫ q.hom.hom = 1
      rw [Category.assoc, (isPullback q j).w, ← Category.assoc, hx, MonObj.one_comp]
    rw [hk] at hker
    exact hker
  let ψ : p.ker →* ρ.range := (incl.comp p.ker.subtype).codRestrict ρ.range hmem
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    exact (cancel_mono (inclusion q j).hom.hom).mp (congrArg Subtype.val hxy)
  have : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective hψ
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p (by rw [Subgroup.range_subtype])

end SubgroupPreimage

section Field

variable {k : Type u} [Field k] {R G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {r : R ⟶ G}

/-- An actual quotient by a represented solvable radical has no nontrivial
smooth connected solvable normal closed subgroup. -/
theorem IsSolvableRadical.range_eq_bot_of_isFppfQuotient
    (hr : IsSolvableRadical r) (q : G ⟶ Q) [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q)
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ Q)
    (hj : IsClosedSubgroup j) (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left)
    (hsol : IsSolvableGroupScheme H) (hn : (SubgroupFunctor.range j).IsNormal) :
    SubgroupFunctor.range j = ⊥ := by
  have : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  have : Mono r.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : Smooth R.X.hom := hr.smooth
  have : ConnectedSpace R.X.left := hr.connectedSpace
  have : GeometricallyConnected R.X.hom := R.geometricallyConnected_of_connected
  have : GeometricallyConnected (kernel q).X.hom :=
    KernelRepresentative.geometricallyConnected q r hq.2.2.2
  have : QuasiCompact q.hom.hom.left := HomImage.quasiCompact_hom q
  have : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hr.smooth
  have : Surjective q.hom.hom.left := hq.2.1
  have : Flat q.hom.hom.left := hq.1
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hpre : IsSolvableGroupScheme (SubgroupPreimage.groupScheme q j) := by
    apply isSolvableGroupScheme_of_isSolvable_points
    have : Group.IsSolvable (algebraicClosurePoint k ⟶ R.X) :=
      SolvableFieldExtensionProof.allPoints_isSolvable R hr.smooth hr.isSolvableGroupScheme _
    have : Group.IsSolvable (algebraicClosurePoint k ⟶ H.X) :=
      SolvableFieldExtensionProof.allPoints_isSolvable H hs hsol _
    exact SubgroupPreimage.isSolvable_points_of_kernel_range r q j hj hq.2.2.2 _
  apply SubgroupPreimage.range_eq_bot_of_range_inclusion_le_kernel q j
  rw [hq.2.2.2]
  exact hr.greatest (SubgroupPreimage.groupScheme q j) (SubgroupPreimage.inclusion q j)
    (SubgroupPreimage.isClosedSubgroup q j hj) (SubgroupPreimage.smooth q j)
    (SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q j) hpre
    (SubgroupPreimage.isNormal q j hn)

/-- An affine fppf quotient by a supplied solvable radical has trivial
ground-field solvable radical in the all-test sense. -/
theorem IsSolvableRadical.hasTrivialSolvableRadical_quotient
    (hr : IsSolvableRadical r) (q : G ⟶ Q) [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q) :
    HasTrivialSolvableRadical Q :=
  hr.range_eq_bot_of_isFppfQuotient q hq

/-- The same quotient has trivial ground-field unipotent radical. -/
theorem IsSolvableRadical.hasTrivialUnipotentRadical_quotient
    (hr : IsSolvableRadical r) (q : G ⟶ Q) [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q) :
    HasTrivialUnipotentRadical Q := by
  intro H j hj hs hc hu hn
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Smooth H.X.hom := hs
  exact hr.range_eq_bot_of_isFppfQuotient q hq H j hj hs hc
    (isSolvableGroupScheme_of_isSolvable_points (isSolvable_points_of_isUnipotent hu _)) hn

/-- After base change to the algebraic closure, an affine fppf quotient by
a geometric solvable radical has no smooth connected solvable normal subgroup. -/
theorem IsGeometricSolvableRadical.hasTrivialGeometricSolvableRadical_quotient
    (hr : IsGeometricSolvableRadical r) (q : G ⟶ Q) [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q) :
    HasTrivialSolvableRadical ((GroupScheme.baseChange (toAlgebraicClosure k)).obj Q) := by
  let b := toAlgebraicClosure k
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  apply hr.2.hasTrivialSolvableRadical_quotient ((GroupScheme.baseChange b).map q)
  rw [SubgroupFunctor.range_baseChangeHom]
  exact hq.baseChange b

/-- An affine fppf quotient by a geometric solvable radical is connected
reductive over the original field. -/
theorem IsGeometricSolvableRadical.isConnectedReductive_quotient
    (hr : IsGeometricSolvableRadical r)
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (q : G ⟶ Q) [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q) :
    IsConnectedReductive Q := by
  let b := toAlgebraicClosure k
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  have hq' : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map r))
      ((GroupScheme.baseChange b).map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  exact
    { smooth := hq.smooth_target
      isAffineHom := inferInstance
      connectedSpace := hq.connectedSpace
      hasTrivialGeometricUnipotentRadical :=
        hr.2.hasTrivialUnipotentRadical_quotient _ hq' }

end Field

end Langlands.GroupScheme
