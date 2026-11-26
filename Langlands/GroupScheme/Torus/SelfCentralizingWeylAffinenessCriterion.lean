import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionHelpers
import Langlands.GroupScheme.RelativeMultiplicativeTypeQuotientReduction
import Langlands.GroupScheme.DiagonalizableQuotientModelTransport
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotient
import Langlands.GroupScheme.FppfQuotientKernelGeometry
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.QuotientCell

/-! # The affineness criterion for the Weyl quotient of a self-centralizing torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SelfCentralizingWeylAffineness

variable {S : Scheme.{u}}

section Descent

variable {G H : GroupScheme S} {Y : Over S}

/-- A flat, surjective map locally of finite presentation out of a group, whose fibres
on every test scheme are exactly the cosets of a represented subgroup with affine
structure morphism, is an affine morphism. -/
theorem isAffineHom_of_coset_fibres (i : H ⟶ G) [Mono i.hom.hom]
    [IsAffineHom H.X.hom] (p : G.X ⟶ Y) [Flat p.left] [Surjective p.left]
    [LocallyOfFinitePresentation p.left]
    (hf : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier U) :
    IsAffineHom p.left := by
  have hpb := (QuotientCell.multiplication_isPullback i (𝟙 G.X) p hf).map (Over.forget S)
  change IsPullback (QuotientCell.multiplication i (𝟙 G.X)).left
    (fst G.X H.X).left p.left ((𝟙 G.X) ≫ p).left at hpb
  simp only [Category.id_comp] at hpb
  have hsource : IsAffineHom (fst G.X H.X).left := by
    change IsAffineHom (Limits.pullback.fst G.X.hom H.X.hom)
    exact MorphismProperty.pullback_fst G.X.hom H.X.hom
      (inferInstanceAs (IsAffineHom H.X.hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hpb.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsource

end Descent

section Torus

variable {G N W : GroupScheme S} {T : CommGroupScheme S} {t : T.toGrp ⟶ G}
  {n : N ⟶ G} (hn : (torusNormalizer t).IsRepresentedBy n)

/-- The torus factors through its represented normalizer. -/
def torusToNormalizer : T.toGrp ⟶ N :=
  SubgroupFunctor.IsRepresentedBy.factorHom hn t (SubgroupFunctor.range t).le_normalizer

@[reassoc]
theorem torusToNormalizer_comp : torusToNormalizer hn ≫ n = t :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp hn t (SubgroupFunctor.range t).le_normalizer

theorem torusToNormalizer_hom_comp :
    (torusToNormalizer hn).hom.hom ≫ n.hom.hom = t.hom.hom := by
  rw [← Grp.comp_hom_hom, torusToNormalizer_comp]

include hn in
theorem mono_normalizer : Mono n.hom.hom := hn.1

/-- A point of `N` lies in the image of the torus exactly when its image in `G` does. -/
theorem mem_range_torusToNormalizer_iff {U : Over S} (y : U ⟶ N.X) :
    y ∈ (SubgroupFunctor.range (torusToNormalizer hn)).carrier U ↔
      y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U := by
  have := mono_normalizer hn
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by rw [Category.assoc, torusToNormalizer_hom_comp]⟩
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    apply (cancel_mono n.hom.hom).mp
    rw [Category.assoc, torusToNormalizer_hom_comp, hs]

/-- The torus is normal in its normalizer. -/
theorem range_torusToNormalizer_isNormal :
    (SubgroupFunctor.range (torusToNormalizer hn)).IsNormal := by
  intro U g x _ hx
  rw [mem_range_torusToNormalizer_iff] at hx ⊢
  have hg : g ≫ n.hom.hom ∈ (torusNormalizer t).carrier U := by
    rw [← hn.2]
    exact ⟨g, rfl⟩
  have h := SubgroupFunctor.conj_mem_of_mem_normalizer hg hx
  rwa [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]

/-- The torus inclusion into the normalizer is a closed subgroup. -/
theorem isClosedSubgroup_torusToNormalizer (ht : IsClosedSubgroup t)
    (hnc : IsClosedSubgroup n) : IsClosedSubgroup (torusToNormalizer hn) := by
  let : IsClosedImmersion n.hom.hom.left := hnc
  have : IsClosedImmersion ((torusToNormalizer hn).hom.hom.left ≫ n.hom.hom.left) := by
    rw [← Over.comp_left, torusToNormalizer_hom_comp]
    exact ht
  exact IsClosedImmersion.of_comp _ n.hom.hom.left

variable {q : N ⟶ W}
  (hker : ∀ (U : Over S) (y : U ⟶ N.X),
    y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U)

include hker in
/-- The kernel condition identifies the actual kernel of `q` with the torus. -/
theorem range_kernelι_eq :
    SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range (torusToNormalizer hn) := by
  apply SubgroupFunctor.ext
  intro U
  ext y
  rw [mem_range_kernelι_iff, mem_range_torusToNormalizer_iff, hker]

include hker in
/-- The Weyl projection is an fppf quotient by the torus. -/
theorem isFppfQuotient (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hlfp : LocallyOfFinitePresentation q.hom.hom.left) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (torusToNormalizer hn)) q :=
  ⟨hflat, hsurj, hlfp, range_kernelι_eq hn hker⟩

include hn hker in
/-- If the Weyl quotient is affine, so is the normalizer: the Weyl projection is an fppf
quotient by the affine torus. -/
theorem isAffineHom_normalizer_of_weyl (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hlfp : LocallyOfFinitePresentation q.hom.hom.left) [IsAffineHom W.X.hom] :
    IsAffineHom N.X.hom := by
  have : IsAffineHom T.toGrp.X.hom := hT.isMultiplicativeType.isAffineHom
  have : Mono (torusToNormalizer hn).hom.hom := by
    have : Mono n.hom.hom := mono_normalizer hn
    have : Mono ((torusToNormalizer hn).hom.hom ≫ n.hom.hom) := by
      rw [torusToNormalizer_hom_comp]
      let : IsClosedImmersion t.hom.hom.left := ht
      exact Over.mono_of_mono_left _
    exact mono_of_mono _ n.hom.hom
  have : IsAffineHom q.hom.hom.left :=
    (isFppfQuotient hn hker hflat hsurj hlfp).isAffineHom_of_kernel (torusToNormalizer hn)
  rw [← Over.w q.hom.hom]
  infer_instance

include hn hker in
/-- If the normalizer is affine, so is the Weyl quotient: the quotient of an affine group
by its normal torus is affine, and fppf quotients are unique. -/
theorem isAffineHom_weyl_of_normalizer (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hnc : IsClosedSubgroup n)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hlfp : LocallyOfFinitePresentation q.hom.hom.left) [IsAffineHom N.X.hom] :
    IsAffineHom W.X.hom := by
  obtain ⟨Q, q', hQ, hq'⟩ := NormalQuotient.exists_affine_fppfQuotient_of_multiplicativeType
    (affineDiagonalizableNormalQuotient_of_model affineDiagonalizableModelQuotient)
    (torusToNormalizer hn) (isClosedSubgroup_torusToNormalizer hn ht hnc)
    (range_torusToNormalizer_isNormal hn) hT.isMultiplicativeType
  have := hQ
  exact FppfQuotientComparison.isAffineHom_target (isFppfQuotient hn hker hflat hsurj hlfp) hq'

/-- A closed subgroup of an affine group is affine. -/
theorem isAffineHom_normalizer_of_group (hnc : IsClosedSubgroup n) [IsAffineHom G.X.hom] :
    IsAffineHom N.X.hom := by
  let : IsClosedImmersion n.hom.hom.left := hnc
  rw [← Over.w n.hom.hom]
  infer_instance

include hn in
/-- If the normalizer is affine and the conjugacy quotient `G / N` is affine over the base,
then the group is affine: the projection `G → G / N` is affine by fppf descent from the
torsor isomorphism `G × N ≅ G ×_{G/N} G`. -/
theorem isAffineHom_group_of_normalizer {Y : Over S} (p : G.X ⟶ Y) [IsAffineHom Y.hom]
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    (hp : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U)
    [IsAffineHom N.X.hom] : IsAffineHom G.X.hom := by
  have : Mono n.hom.hom := mono_normalizer hn
  have : IsAffineHom p.left := by
    apply isAffineHom_of_coset_fibres n p
    intro U g h
    rw [hp, hn.2]
  rw [← Over.w p]
  infer_instance

end Torus

/-- **The affineness criterion.** Let `G` be a smooth, separated, quasi-compact group over
`S` with connected affine residue fibres, `t : T → G` a closed relative maximal torus that
represents its own centralizer, `n : N → G` a closed subgroup representing the normalizer
of `t`, and `q : N → W` a flat surjective map locally of finite presentation whose kernel
on every test scheme is the torus. Assuming the affine conjugacy-quotient statement
(SGA 3, XVI 4.1(c)), `G` is affine over `S` exactly when `W` is. -/
theorem isAffineHom_iff
    (hS2 : SelfCentralizingTorusConjugacyQuotientAffineStatement.{u})
    {S : Scheme.{u}} (G : GroupScheme S) (hsmooth : Smooth G.X.hom)
    (hsep : IsSeparated G.X.hom) (hqc : QuasiCompact G.X.hom)
    (hfib : ∀ s : S,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (hcent : (torusCentralizer t).IsRepresentedBy t)
    {N W : GroupScheme S} (n : N ⟶ G) (q : N ⟶ W)
    (hnc : IsClosedSubgroup n) (hn : (torusNormalizer t).IsRepresentedBy n)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hlfp : LocallyOfFinitePresentation q.hom.hom.left)
    (hker : ∀ (U : Over S) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U) :
    IsAffineHom G.X.hom ↔ IsAffineHom W.X.hom := by
  constructor
  · intro hG
    have : IsAffineHom N.X.hom := isAffineHom_normalizer_of_group hnc
    exact isAffineHom_weyl_of_normalizer hn hker hT ht hnc hflat hsurj hlfp
  · intro hW
    have : IsAffineHom N.X.hom := isAffineHom_normalizer_of_weyl hn hker hT ht hflat hsurj hlfp
    obtain ⟨Y, p, hY, hpflat, hpsurj, hplfp, hp⟩ :=
      hS2 S G hsmooth hsep hqc hfib T t hT ht hmax hcent
    exact isAffineHom_group_of_normalizer hn p hp

end Langlands.GroupScheme.SelfCentralizingWeylAffineness
