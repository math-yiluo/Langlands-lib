import Langlands.GroupScheme.AffineKernelQuotient
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.GroupScheme.FppfQuotientTargetSmooth

/-! # Reduction of smooth affine normal quotients to algebraically closed kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The remaining algebraically closed-field construction input: every normal
closed subgroup of a smooth affine group is the full kernel of an actual
homomorphism into an affine locally finite type group. -/
def AlgClosedNormalSubgroupAffineKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (f : G ⟶ H),
        IsAffineHom H.X.hom ∧ LocallyOfFiniteType H.X.hom ∧
          SubgroupFunctor.range (kernelι f) = SubgroupFunctor.range i

/-- The exact universe-general normal quotient theorem follows from only the
algebraically closed-field affine-kernel construction. -/
def NormalSubgroupQuotientAlgClosedReductionStatement : Prop :=
  AlgClosedNormalSubgroupAffineKernelStatement.{u} → NormalSubgroupQuotientStatement.{u}

/-- Form the quotient over an algebraic closure and descend its actual affine
group, original map and full represented kernel through the fpqc field cover. -/
theorem normalSubgroupQuotient_of_algClosed_affineKernel :
    NormalSubgroupQuotientAlgClosedReductionStatement.{u} := by
  intro h k _ G _ _ N i hi hn
  let Ω : Type u := AlgebraicClosure k
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let G' := (GroupScheme.baseChange b).obj G
  let N' := (GroupScheme.baseChange b).obj N
  let i' : N' ⟶ G' := (GroupScheme.baseChange b).map i
  have : IsAffineHom G'.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have : Smooth G'.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have hi' : IsClosedSubgroup i' := hi.baseChange b
  have hn' : (SubgroupFunctor.range i').IsNormal := by
    change (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).IsNormal
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  obtain ⟨H, f, hHa, hHl, hfk⟩ := h Ω G' N' i' hi' hn'
  have := hHa
  have := hHl
  obtain ⟨Q, q, _, hQa, hq⟩ := exists_quotient_of_affine_kernel i' f hfk
  have : IsAffineHom Q.X.hom := hQa
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨R, r, hRa, hr, _⟩ := Descent.exists_affine_fppfQuotient b i Q q hq
  have : IsAffine R.X.left := hRa
  exact ⟨R, r, hr.smooth_target, inferInstance, hr⟩

end Langlands.GroupScheme
