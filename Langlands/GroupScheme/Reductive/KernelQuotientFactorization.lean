import Langlands.GroupScheme.Reductive.FiniteNormalQuotient
import Langlands.GroupScheme.Reductive.FibrewiseIsogenyBaseChange
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.FppfHomDescent

/-! # Removing a supplied finite normal kernel subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace KernelQuotientFactorization

/-- An affine finite-type factor of a finite flat surjective composite is
an isogeny when the preceding map is flat and surjective. -/
theorem isIsogeny_of_comp {S : Scheme.{u}} {G Q H : GroupScheme S}
    (q : G ⟶ Q) (g : Q ⟶ H) [IsAffine Q.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType Q.X.hom] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] (h : IsIsogeny (q ≫ g)) :
    IsIsogeny g := by
  have : IsFinite (q.hom.hom.left ≫ g.hom.hom.left) := h.1
  have : Flat (q.hom.hom.left ≫ g.hom.hom.left) := h.2.1
  have : Flat g.hom.hom.left :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      q.hom.hom.left g.hom.hom.left
  have : UniversallyClosed g.hom.hom.left :=
    UniversallyClosed.of_comp_surjective q.hom.hom.left g.hom.hom.left
  have : LocallyOfFiniteType (g.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w g.hom.hom]
    infer_instance
  have : LocallyOfFiniteType g.hom.hom.left :=
    locallyOfFiniteType_of_comp g.hom.hom.left H.X.hom
  have : IsProper g.hom.hom.left := {}
  refine ⟨IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩,
    inferInstance, ⟨?_⟩⟩
  intro y
  obtain ⟨x, hx⟩ := h.2.2.surj y
  exact ⟨q.hom.hom.left x, hx⟩

/-- The full kernel of a quotient by a subgroup killed by `f` is killed by `f`. -/
theorem kernel_comp_eq_zero {S : Scheme.{u}} {G N Q H : GroupScheme S}
    (i : N ⟶ G) (q : G ⟶ Q) (f : G ⟶ H)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hi : i ≫ f = 0) : kernelι q ≫ f = 0 := by
  have hm : (kernelι q).hom.hom ∈ (SubgroupFunctor.range i).carrier (kernel q).X := by
    rw [← hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hm
  have hif : i.hom.hom ≫ f.hom.hom = 1 :=
    congrArg (fun z => z.hom.hom) hi
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ f.hom.hom = 1
  rw [← hx, Category.assoc, hif, MonObj.comp_one]

/-- The specified factor between two fppf quotients of the same full kernel
is an isomorphism. -/
theorem isIso_of_same_kernel {S : Scheme.{u}} {G Q H : GroupScheme S}
    {F : SubgroupFunctor G} (q : G ⟶ Q) (f : G ⟶ H) (g : Q ⟶ H)
    [QuasiCompact q.hom.hom.left] [QuasiCompact f.hom.hom.left]
    (hq : RelativeRoot.IsFppfQuotient F q)
    (hf : RelativeRoot.IsFppfQuotient F f) (hfac : q ≫ g = f) :
    IsIso g := by
  have hg : g = (FppfQuotientComparison.iso hq hf).hom := by
    apply FppfQuotientComparison.hom_ext hq
    rw [hfac, FppfQuotientComparison.iso_fac]
  rw [hg]
  infer_instance

end KernelQuotientFactorization

/-- An actual reductive finite kernel quotient and the specified remaining
fibrewise isogeny, invertible at a chosen field-valued point. -/
structure ReductiveKernelQuotientFactorization {S : Scheme.{u}}
    {G N H : GroupScheme S} (f : G ⟶ H) (i : N ⟶ G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) where
  quotient : ReductiveFiniteNormalSubgroupQuotient i
  remaining : quotient.quotient ⟶ H
  fac : quotient.projection ≫ remaining = f
  fibrewise : IsFibrewiseIsogeny remaining
  isIso : IsIso ((baseChange b).map remaining)

/-- Remove a supplied finite flat normal subgroup of the kernel which equals
the entire kernel at the specified field-valued point. -/
def reductiveKernelQuotientFactorization
    {S : Scheme.{u}} [IsAffine S] {G N H : GroupScheme S}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : G ⟶ H) (hf : IsFibrewiseIsogeny f)
    (i : N ⟶ G) [Mono i.hom.hom]
    [IsFinite N.X.hom] [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    (hn : (SubgroupFunctor.range i).IsNormal) (hi : i ≫ f = 0)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hs : SubgroupFunctor.range ((baseChange b).map i) =
      SubgroupFunctor.range (kernelι ((baseChange b).map f))) :
    ReductiveKernelQuotientFactorization f i b := by
  let Q := reductiveFiniteNormalSubgroupQuotient hG i hn
  have : Flat Q.projection.hom.hom.left := Q.isFppfQuotient.1
  have : Surjective Q.projection.hom.hom.left := Q.isFppfQuotient.2.1
  have : LocallyOfFinitePresentation Q.projection.hom.hom.left :=
    Q.isFppfQuotient.2.2.1
  let g := FppfHomDescent.hom Q.projection f
    (KernelQuotientFactorization.kernel_comp_eq_zero i Q.projection f Q.isFppfQuotient hi)
  have hfac : Q.projection ≫ g = f := FppfHomDescent.fac _ _ _
  have hfield : IsFieldwiseIsogeny g := by
    intro l _ c
    have hQ := Q.reductive.isConnectedReductive_baseChange c
    have hHc := hH.isConnectedReductive_baseChange c
    have : IsAffineHom ((baseChange c).obj Q.quotient).X.hom := hQ.isAffineHom
    have : IsAffineHom ((baseChange c).obj H).X.hom := hHc.isAffineHom
    have : IsAffine ((baseChange c).obj Q.quotient).X.left :=
      isAffine_of_isAffineHom ((baseChange c).obj Q.quotient).X.hom
    have : IsAffine ((baseChange c).obj H).X.left :=
      isAffine_of_isAffineHom ((baseChange c).obj H).X.hom
    have : Smooth ((baseChange c).obj Q.quotient).X.hom := hQ.smooth
    have hq := Q.isFppfQuotient.baseChange c
    have : Flat ((baseChange c).map Q.projection).hom.hom.left := hq.1
    have : Surjective ((baseChange c).map Q.projection).hom.hom.left := hq.2.1
    apply KernelQuotientFactorization.isIsogeny_of_comp ((baseChange c).map Q.projection)
      ((baseChange c).map g)
    rw [← Functor.map_comp, hfac]
    exact hf.isFieldwiseIsogeny l c
  refine ⟨Q, g, hfac, (isFieldwiseIsogeny_iff_isFibrewiseIsogeny g).mp hfield, ?_⟩
  let qb := (baseChange b).map Q.projection
  let fb := (baseChange b).map f
  have hqb : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange b).map i)) qb := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using Q.isFppfQuotient.baseChange b
  have hfb := hf.isFieldwiseIsogeny k b
  have : IsFinite fb.hom.hom.left := hfb.1
  have : IsFinite Q.projection.hom.hom.left := Q.finite
  have : IsFinite qb.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) b Q.projection.hom.hom inferInstance
  have hGb := hG.isConnectedReductive_baseChange b
  have hHb := hH.isConnectedReductive_baseChange b
  have : Smooth ((baseChange b).obj G).X.hom := hGb.smooth
  have : Smooth ((baseChange b).obj H).X.hom := hHb.smooth
  have : LocallyOfFinitePresentation (fb.hom.hom.left ≫ ((baseChange b).obj H).X.hom) := by
    rw [Over.w fb.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation fb.hom.hom.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp
      fb.hom.hom.left ((baseChange b).obj H).X.hom
  apply KernelQuotientFactorization.isIso_of_same_kernel qb fb ((baseChange b).map g)
    hqb
  · exact ⟨hfb.2.1, hfb.2.2, inferInstance, hs.symm⟩
  · rw [← Functor.map_comp, hfac]

end Langlands.GroupScheme
