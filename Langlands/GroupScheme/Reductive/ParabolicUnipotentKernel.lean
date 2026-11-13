import Langlands.GroupScheme.Absolute.TriangularDiagonalImageReduction
import Langlands.GroupScheme.Rational.NestedParabolicContainment
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Unipotent kernels of restrictions to parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
    {G Q H : GroupScheme (Spec (CommRingCat.of k))}

/-- Removing a monomorphic postcomposition preserves the actual smooth
connected unipotent kernel property. -/
theorem HasSmoothConnectedUnipotentKernel.of_comp_mono
    (q : G ⟶ Q) (i : Q ⟶ H) [Mono i.hom.hom]
    (h : HasSmoothConnectedUnipotentKernel (q ≫ i)) :
    HasSmoothConnectedUnipotentKernel q := by
  have : Smooth (kernel (q ≫ i)).X.hom := h.1
  have : ConnectedSpace (kernel (q ≫ i)).X.left := h.2.1
  have hk := (range_kernelι_comp_mono q i).symm
  exact ⟨KernelRepresentative.smooth q (kernelι (q ≫ i)) hk,
    KernelRepresentative.connectedSpace q (kernelι (q ≫ i)) hk,
    KernelRepresentative.isUnipotent q (kernelι (q ≫ i)) hk h.2.2⟩

/-- Smooth connected unipotent kernels are closed under composition of
supplied fppf homomorphisms between affine groups. -/
theorem HasSmoothConnectedUnipotentKernel.comp
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ Q) (r : Q ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (hr : HasSmoothConnectedUnipotentKernel r) :
    HasSmoothConnectedUnipotentKernel (q ≫ r) := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : GeometricallyConnected (kernel q).X.hom := hq.geometricallyConnected
  have : Smooth (kernel r).X.hom := hr.1
  have : ConnectedSpace (kernel r).X.left := hr.2.1
  let W := SubgroupPreimage.groupScheme q (kernelι r)
  let n : W ⟶ G := SubgroupPreimage.inclusion q (kernelι r)
  let p : W ⟶ kernel r := SubgroupPreimage.projection q (kernelι r)
  have hn : IsClosedSubgroup n :=
    SubgroupPreimage.isClosedSubgroup q (kernelι r)
      (inferInstanceAs (IsClosedImmersion (kernelι r).hom.hom.left))
  have : Mono n.hom.hom := hn.mono_overHom
  have : Smooth W.X.hom := SubgroupPreimage.smooth q (kernelι r)
  have : ConnectedSpace W.X.left :=
    SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q (kernelι r)
  have : IsAffineHom W.X.hom :=
    SubgroupPreimage.isAffineHom q (kernelι r)
      (inferInstanceAs (IsClosedImmersion (kernelι r).hom.hom.left))
  have : Flat p.hom.hom.left := SubgroupPreimage.flat_projection q (kernelι r)
  have : Surjective p.hom.hom.left :=
    SubgroupPreimage.surjective_projection q (kernelι r)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : QuasiCompact p.hom.hom.left :=
    SubgroupPreimage.quasiCompact_projection q (kernelι r)
  have : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : IsAffineHom (kernel p).X.hom :=
    SubgroupPreimage.isAffineHom_kernel q (kernelι r)
  have hu : IsUnipotent W := isUnipotent_of_kernel_of_quotient p
    (SubgroupPreimage.isUnipotent_kernel q (kernelι r) hq.2.2) hr.2.2
  have hk : SubgroupFunctor.range (kernelι (q ≫ r)) = SubgroupFunctor.range n := by
    rw [range_kernelι_comp_eq_comap, SubgroupPreimage.range_inclusion]
  exact ⟨KernelRepresentative.smooth (q ≫ r) n hk,
    KernelRepresentative.connectedSpace (q ≫ r) n hk,
    KernelRepresentative.isUnipotent (q ≫ r) n hk hu⟩

end Field

section Parabolic

variable {k : Type u} [Field k]
    {G P U Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    (p : P ⟶ G) (hp : IsParabolicSubgroup p)
    (n : U ⟶ G) (hn : IsUnipotentRadical n)

include hp hn

/-- Every represented ground-field radical lies in every parabolic subgroup,
as an inclusion on all relative scheme tests. -/
theorem IsParabolicSubgroup.radical_le :
    SubgroupFunctor.range n ≤ SubgroupFunctor.range p := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Mono p.hom.hom := hp.isClosedSubgroup.mono_overHom
  have : IsAffineHom U.X.hom := hn.isClosedSubgroup.isAffineHom
  have : Smooth U.X.hom := hn.smooth
  have : ConnectedSpace U.X.left := hn.connectedSpace
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hsurj
  have : Flat b := hflat
  have : QuasiCompact b := hqc
  apply SubgroupFunctor.le_range_of_baseChange_le b p
  rw [← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom]
  have : ConnectedSpace (F.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth (F.obj U).X.hom := by
    change Smooth (pullback.snd U.X.hom b)
    infer_instance
  obtain ⟨B, j, f, hj, hf⟩ := hp.exists_isBorelSubgroup
  exact (normalUnipotentBorelContainment (AlgebraicClosure k) (F.obj G)
    (F.obj U) (F.map n) (hn.isClosedSubgroup.baseChange b)
    (show Smooth (F.obj U).X.hom from inferInstance)
    (U.connectedSpace_baseChange_of_smooth_affine b) hn.isUnipotent.baseChange
    (by rw [SubgroupFunctor.range_baseChangeHom]; exact hn.isNormal.baseChange b)
    B j hj).trans (SubgroupFunctor.range_le_of_factor f hf)

/-- The actual factor of the supplied radical inclusion through the
supplied parabolic inclusion. -/
def IsParabolicSubgroup.radicalFactor : U ⟶ P := by
  have : Mono p.hom.hom := hp.isClosedSubgroup.mono_overHom
  have : Mono n.hom.hom := hn.isClosedSubgroup.mono_overHom
  exact SubgroupFunctor.factorOfRangeLE (hp.radical_le p n hn)

@[reassoc]
theorem IsParabolicSubgroup.radicalFactor_comp :
    hp.radicalFactor p n hn ≫ p = n := by
  have : Mono p.hom.hom := hp.isClosedSubgroup.mono_overHom
  have : Mono n.hom.hom := hn.isClosedSubgroup.mono_overHom
  exact SubgroupFunctor.factorOfRangeLE_comp (hp.radical_le p n hn)

/-- Restricting an exact radical quotient to a parabolic has the same smooth
connected unipotent full kernel. -/
theorem IsParabolicSubgroup.hasSmoothConnectedUnipotentKernel_comp
    (q : G ⟶ Q)
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n) :
    HasSmoothConnectedUnipotentKernel (p ≫ q) := by
  let f := hp.radicalFactor p n hn
  have hf : f ≫ p = n := hp.radicalFactor_comp p n hn
  have hfc : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hp.isClosedSubgroup (hf ▸ hn.isClosedSubgroup)
  have : Mono f.hom.hom := hfc.mono_overHom
  have : Mono p.hom.hom := hp.isClosedSubgroup.mono_overHom
  have : Smooth U.X.hom := hn.smooth
  have : ConnectedSpace U.X.left := hn.connectedSpace
  have hker : SubgroupFunctor.range (kernelι (p ≫ q)) = SubgroupFunctor.range f := by
    rw [range_kernelι_comp_eq_comap, hk]
    ext T x
    rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (cancel_mono p.hom.hom).mp ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, hf]
      exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Category.assoc, ← Grp.comp_hom_hom, hf]⟩
  exact ⟨KernelRepresentative.smooth (p ≫ q) f hker,
    KernelRepresentative.connectedSpace (p ≫ q) f hker,
    KernelRepresentative.isUnipotent (p ≫ q) f hker hn.isUnipotent⟩

end Parabolic

end Langlands.GroupScheme
