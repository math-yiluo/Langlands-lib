import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelQuotientDescent
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.SubgroupFunctor.QuotientPreimage
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Borel correspondence through smooth connected unipotent kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace UnipotentQuotientBorels

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)

include hq

omit [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] in
/-- Every Borel contains the full actual kernel, on every scheme test. -/
theorem kernel_le_borel
    {B : GroupScheme (Spec (CommRingCat.of k))}
    (i : B ⟶ G) (hi : IsBorelSubgroup i) :
    SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i :=
  normalUnipotentBorelContainment k G (kernel q) (kernelι q)
    (kernelι_isClosedImmersion q) hq.1 hq.2.1 hq.2.2
    (HopfPrimitive.isNormal_range_kernelι q) B i hi

/-- A Borel's fpqc closed image is Borel and recovers that Borel by full inverse image. -/
theorem isBorelSubgroup_image
    {B I : GroupScheme (Spec (CommRingCat.of k))}
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (p : B ⟶ I)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left]
    (j : I ⟶ Q) (hj : IsClosedSubgroup j)
    (hsq : i ≫ q = p ≫ j) :
    IsBorelSubgroup j ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i ∧
      IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : GeometricallyConnected (kernel q).X.hom := hq.geometricallyConnected
  have : GeometricallyConnected q.hom.hom.left :=
    geometricallyConnected_of_geometricallyConnected_kernel q
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have heq := SubgroupFunctor.comap_range_eq_of_fpqc_square i q p j hsq
    (kernel_le_borel q hq i hi)
  have hpb := SubgroupFunctor.IsRepresentedBy.isPullback_of_comap_eq
    (F := SubgroupFunctor.range i) (E := SubgroupFunctor.range j)
    ⟨inferInstance, rfl⟩ ⟨inferInstance, rfl⟩ q p hsq heq
  have : Smooth p.hom.hom.left :=
    MorphismProperty.of_isPullback (hpb.map (Over.forget _))
      (inferInstance : Smooth q.hom.hom.left)
  exact ⟨isBorelSubgroup_of_quotient_square i hi q p j hj hpb, heq, hpb⟩

/-- Construct the actual Borel image of any supplied Borel embedding. -/
theorem exists_borel_image
    {B : GroupScheme (Spec (CommRingCat.of k))}
    (i : B ⟶ G) (hi : IsBorelSubgroup i) :
    ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (j : I ⟶ Q) (p : B ⟶ I),
      IsBorelSubgroup j ∧ i ≫ q = p ≫ j ∧
      Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      QuasiCompact p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i ∧
      IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : Smooth (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : Smooth Q.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.hom.hom.left Q.X.hom
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : IsAffineHom B.X.hom := hi.isClosedSubgroup.isAffineHom
  obtain ⟨I, j, p, hj, hfac, hpf, hps, hpq, hpl, _, _, _⟩ :=
    HomImage.exists_image (i ≫ q)
  have := hpf
  have := hps
  have := hpq
  obtain ⟨hB, heq, hpb⟩ := isBorelSubgroup_image q hq i hi p j hj hfac.symm
  exact ⟨I, j, p, hB, hfac.symm, hpf, hps, hpq, hpl, heq, hpb⟩

/-- Any closed representative of the full inverse image of a target Borel is Borel. -/
theorem isBorelSubgroup_of_range_eq_comap
    {B P : GroupScheme (Spec (CommRingCat.of k))}
    (j : B ⟶ Q) (hj : IsBorelSubgroup j)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q) :
    IsBorelSubgroup i := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : Smooth (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : Smooth Q.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.hom.hom.left Q.X.hom
  have : ConnectedSpace Q.X.left :=
    q.hom.hom.left.surjective.connectedSpace q.hom.hom.left.continuous
  obtain ⟨B₁, i₁, hi₁⟩ := BorelExistence.exists_isBorelSubgroup G
  obtain ⟨I, jI, p, hjI, hfac, hpf, hps, hpq, hpl, _, _⟩ :=
    exists_borel_image q hq i₁ hi₁
  obtain ⟨a, φ, ha⟩ := (borelConjugacy k Q).2 I B jI j hjI hj
  let g := rationalPointLift q a
  have hg : g ≫ q.hom.hom = a := rationalPointLift_comp q a
  let i₀ := i₁ ≫ (G.innerIso g).hom
  have hi₀ : IsBorelSubgroup i₀ := hi₁.comp_iso (G.innerIso g)
  let p₀ := p ≫ φ.hom
  have hsq : i₀ ≫ q = p₀ ≫ j := by
    calc i₀ ≫ q = i₁ ≫ ((G.innerIso g).hom ≫ q) := Category.assoc _ _ _
      _ = i₁ ≫ (q ≫ (Q.innerIso (g ≫ q.hom.hom)).hom) := by
        rw [innerIso_hom_comp]
      _ = (p ≫ jI) ≫ (Q.innerIso a).hom := by
        rw [hg, ← Category.assoc, hfac]
      _ = p₀ ≫ j := by rw [Category.assoc, ha, ← Category.assoc]
  have : Flat p.hom.hom.left := hpf
  have : Surjective p.hom.hom.left := hps
  have : LocallyOfFinitePresentation p.hom.hom.left := hpl
  have : IsIso φ.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso φ)).hom)
  have hp₀f : Flat p₀.hom.hom.left := by
    change Flat (p.hom.hom.left ≫ φ.hom.hom.hom.left)
    infer_instance
  have hp₀s : Surjective p₀.hom.hom.left := by
    change Surjective (p.hom.hom.left ≫ φ.hom.hom.hom.left)
    infer_instance
  have hp₀l : LocallyOfFinitePresentation p₀.hom.hom.left := by
    change LocallyOfFinitePresentation (p.hom.hom.left ≫ φ.hom.hom.hom.left)
    infer_instance
  have : Mono i₀.hom.hom := hi₀.isClosedSubgroup.mono_overHom
  have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
  have himg : SubgroupFunctor.IsFppfImage (SubgroupFunctor.range i₀)
      (SubgroupFunctor.range j) q :=
    ⟨B₁, B, i₀, j, p₀, ⟨inferInstance, rfl⟩, ⟨inferInstance, rfl⟩,
      hsq, hp₀f, hp₀s, hp₀l⟩
  have heq : SubgroupFunctor.range i = SubgroupFunctor.range i₀ :=
    hrange.trans (himg.comap_eq_of_kernel_le (kernel_le_borel q hq i₀ hi₀))
  have h := hi₀.iso_comp (hi.sourceIsoOfRangeEq hi₀.isClosedSubgroup heq)
  rwa [IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp] at h

/-- The actual scheme-theoretic preimage of a target Borel is Borel. -/
theorem isBorelSubgroup_preimage
    {B : GroupScheme (Spec (CommRingCat.of k))}
    (j : B ⟶ Q) (hj : IsBorelSubgroup j) :
    IsBorelSubgroup (SubgroupPreimage.inclusion q j) :=
  isBorelSubgroup_of_range_eq_comap q hq j hj
    (SubgroupPreimage.inclusion q j)
    (SubgroupPreimage.isClosedSubgroup q j hj.isClosedSubgroup)
    (SubgroupPreimage.range_inclusion q j)

end UnipotentQuotientBorels

/-- Actual Borel images and full inverse images through supplied smooth
connected unipotent-kernel quotients over algebraically closed fields. -/
def UnipotentQuotientBorelCorrespondenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left],
    HasSmoothConnectedUnipotentKernel q →
      (∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
        IsBorelSubgroup i →
          ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (j : I ⟶ Q) (p : B ⟶ I),
            IsBorelSubgroup j ∧ i ≫ q = p ≫ j ∧
            Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
            QuasiCompact p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left ∧
            (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i ∧
            IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom) ∧
      (∀ (B P : GroupScheme (Spec (CommRingCat.of k))) (j : B ⟶ Q) (i : P ⟶ G),
        IsBorelSubgroup j → IsClosedSubgroup i →
          SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q →
            IsBorelSubgroup i)

/-- The Borel correspondence requires no retained lifting or conjugacy premise. -/
theorem unipotentQuotientBorelCorrespondence :
    UnipotentQuotientBorelCorrespondenceStatement.{u} := by
  intro k _ _ G Q _ _ _ _ q _ _ _ hq
  constructor
  · intro B i hi
    exact UnipotentQuotientBorels.exists_borel_image q hq i hi
  · intro B P j i hj hi hrange
    exact UnipotentQuotientBorels.isBorelSubgroup_of_range_eq_comap q hq j hj i hi hrange

end Langlands.GroupScheme
