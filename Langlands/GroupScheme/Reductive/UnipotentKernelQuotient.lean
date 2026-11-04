import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.GroupScheme.Reductive.UnipotentExtension
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.SubgroupPreimageKernel
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Ground-field radicals under quotients with unipotent kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual scheme-theoretic kernel is smooth, connected and unipotent
over the original field. -/
def HasSmoothConnectedUnipotentKernel (q : G ⟶ Q) : Prop :=
  Smooth (kernel q).X.hom ∧ ConnectedSpace (kernel q).X.left ∧
    IsUnipotent (kernel q)

namespace HasSmoothConnectedUnipotentKernel

variable {q : G ⟶ Q}

/-- An exact fppf quotient with a supplied smooth connected unipotent
closed kernel representative has the corresponding actual-kernel property. -/
theorem of_representative
    {N : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ G)
    (hn : IsClosedSubgroup n) [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (hN : IsUnipotent N)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q) :
    HasSmoothConnectedUnipotentKernel q := by
  have : IsClosedImmersion n.hom.hom.left := hn
  have : Mono n.hom.hom := Over.mono_of_mono_left _
  exact ⟨KernelRepresentative.smooth q n hq.2.2.2,
    KernelRepresentative.connectedSpace q n hq.2.2.2,
    KernelRepresentative.isUnipotent q n hq.2.2.2 hN⟩

variable [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]

local instance : IsAffineHom (kernel q).X.hom := by
  rw [← Over.w (kernelι q).hom.hom]
  infer_instance

/-- Smoothness of the actual kernel makes the supplied fppf projection smooth. -/
theorem smooth (hq : HasSmoothConnectedUnipotentKernel q) :
    Smooth q.hom.hom.left := by
  have hquot : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q :=
    ⟨inferInstance, inferInstance, inferInstance, rfl⟩
  exact hquot.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hq.1

omit [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] in
/-- The actual kernel is geometrically connected over the original field. -/
theorem geometricallyConnected (hq : HasSmoothConnectedUnipotentKernel q) :
    GeometricallyConnected (kernel q).X.hom := by
  have : Smooth (kernel q).X.hom := hq.1
  have : ConnectedSpace (kernel q).X.left := hq.2.1
  exact geometricallyConnected_of_connected (kernel q)

variable [LocallyOfFiniteType Q.X.hom]

omit [LocallyOfFinitePresentation q.hom.hom.left] in
/-- The image of a represented ground-field radical is contained in any
represented ground-field radical of the target. -/
theorem radical_le_comap
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    SubgroupFunctor.range i ≤ (SubgroupFunctor.range j).comap q := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Smooth U.X.hom := hi.smooth
  have : ConnectedSpace U.X.left := hi.connectedSpace
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨D, inc, p, hinc, hp, hpf, hps, hpqc, _, hDs, hDc, _⟩ :=
    HomImage.exists_image (i ≫ q)
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Mono inc.hom.hom := Over.mono_of_mono_left _
  have : Flat p.hom.hom.left := hpf
  have : Surjective p.hom.hom.left := hps
  have : QuasiCompact p.hom.hom.left := hpqc
  have hDu : IsUnipotent D := hi.isUnipotent.of_flat_surjective p
  have hDn : (SubgroupFunctor.range inc).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square i q p inc hp.symm hi.isNormal
  have hle := hj.greatest D inc hinc hDs hDc hDu hDn
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply hle T
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ p.hom.hom, ?_⟩
  change (y ≫ p.hom.hom) ≫ inc.hom.hom =
    (y ≫ i.hom.hom) ≫ q.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, hp, Grp.comp_hom_hom,
    ← Category.assoc]

omit [LocallyOfFiniteType Q.X.hom] in
/-- A smooth connected unipotent kernel makes the inverse image of the
target radical lie in the source radical. -/
theorem comap_radical_le (hq : HasSmoothConnectedUnipotentKernel q)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    (SubgroupFunctor.range j).comap q ≤ SubgroupFunctor.range i := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : GeometricallyConnected (kernel q).X.hom := hq.geometricallyConnected
  have : Smooth V.X.hom := hj.smooth
  have : ConnectedSpace V.X.left := hj.connectedSpace
  have : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj.isClosedSubgroup
  have : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  have : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.surjective_projection q j
  have : QuasiCompact (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.quasiCompact_projection q j
  have : IsAffineHom (kernel (SubgroupPreimage.projection q j)).X.hom :=
    SubgroupPreimage.isAffineHom_kernel q j
  rw [← SubgroupPreimage.range_inclusion q j]
  exact hi.greatest (SubgroupPreimage.groupScheme q j)
    (SubgroupPreimage.inclusion q j)
    (SubgroupPreimage.isClosedSubgroup q j hj.isClosedSubgroup)
    (SubgroupPreimage.smooth q j)
    (SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q j)
    (isUnipotent_of_kernel_of_quotient (SubgroupPreimage.projection q j)
      (SubgroupPreimage.isUnipotent_kernel q j hq.2.2) hj.isUnipotent)
    (SubgroupPreimage.isNormal q j hj.isNormal)

/-- Under a supplied fppf map with smooth connected unipotent kernel, the
source radical is exactly the full inverse image of the target radical on
every relative scheme test. -/
theorem radical_comap_eq (hq : HasSmoothConnectedUnipotentKernel q)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i :=
  le_antisymm (hq.comap_radical_le hi hj) (radical_le_comap hi hj)

/-- The same supplied fppf homomorphism has the target radical as its actual
fppf image of the source radical. -/
theorem radical_isFppfImage (hq : HasSmoothConnectedUnipotentKernel q)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    SubgroupFunctor.IsFppfImage (SubgroupFunctor.range i)
      (SubgroupFunctor.range j) q := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.IsRepresentedBy.isFppfImage_of_comap_eq
    ⟨inferInstance, rfl⟩ ⟨inferInstance, rfl⟩ q (hq.radical_comap_eq hi hj)

end HasSmoothConnectedUnipotentKernel

end Langlands.GroupScheme
