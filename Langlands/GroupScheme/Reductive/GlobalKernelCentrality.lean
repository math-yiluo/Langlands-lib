import Langlands.GroupScheme.Reductive.NoetherianKernelCentrality
import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyFiniteAssembly
import Langlands.GroupScheme.Reductive.RelativeCenterProof

/-! # The global criterion from finite flat local Artinian centrality -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.GlobalKernelCentrality

open NoetherianKernelCentrality KernelInfinitesimalCentrality
open HopfFiberCentralityResidue

variable {S T : Scheme.{u}}

/-- All-test centrality is local on an arbitrary open cover of the base. -/
theorem isCentral_of_openCover {K G : GroupScheme S}
    (𝒰 : S.OpenCover.{v}) (i : K ⟶ G)
    (hi : ∀ k, IsCentral ((baseChange (𝒰.f k)).map i)) : IsCentral i := by
  intro V x
  apply mem_center.mpr
  intro V' a y
  change (a ≫ (x ≫ i.hom.hom)) * y = y * (a ≫ (x ≫ i.hom.hom))
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ V'.hom)
  intro k
  let W : Over (𝒰.X k) := (Over.pullback (𝒰.f k)).obj V'
  let q : (Over.map (𝒰.f k)).obj W ⟶ V' :=
    Over.homMk (pullback.fst V'.hom (𝒰.f k)) pullback.condition
  let x' := (baseChangePointsEquiv (𝒰.f k) K W).symm (q ≫ a ≫ x)
  let y' := (baseChangePointsEquiv (𝒰.f k) G W).symm (q ≫ y)
  have hc := congrArg (baseChangePointsEquiv (𝒰.f k) G W)
    (commute_of_mem_center (hi k W x') y').eq
  have hp : q ≫ ((a ≫ (x ≫ i.hom.hom)) * y) =
      q ≫ (y * (a ≫ (x ≫ i.hom.hom))) := by
    simpa only [map_mul, baseChangePointsEquiv_comp, x', y',
      MulEquiv.apply_symm_apply, MonObj.comp_mul, Category.assoc] using hc
  exact congrArg CommaMorphism.left hp

/-- Centrality of all canonical residue inclusions persists under every
morphism of scheme bases. -/
theorem central_residue_inclusions_baseChange {K G : GroupScheme S} (i : K ⟶ G)
    (hc : ∀ s : S, IsCentral ((baseChange (S.fromSpecResidueField s)).map i))
    (b : T ⟶ S) (t : T) :
    IsCentral ((baseChange (T.fromSpecResidueField t)).map ((baseChange b).map i)) := by
  apply (isCentral_baseChange_comp_iff b (T.fromSpecResidueField t) i).1
  rw [← b.SpecMap_residueFieldMap_fromSpecResidueField t]
  apply (isCentral_baseChange_comp_iff (S.fromSpecResidueField (b t))
    (Spec.map (b.residueFieldMap t)) i).2
  exact (hc (b t)).baseChange _

/-- Every actual residue kernel remains central after arbitrary scheme base
change, using the canonical kernel comparisons. -/
theorem central_kernel_fibres_baseChange {G H : GroupScheme S} (f : G ⟶ H)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f)))
    (b : T ⟶ S) (t : T) :
    IsCentral (kernelι ((baseChange (T.fromSpecResidueField t)).map
      ((baseChange b).map f))) := by
  apply (isCentral_kernel_baseChange_iff _ _).2
  have h := central_residue_inclusions_baseChange (kernelι f)
    (fun s => (isCentral_kernel_baseChange_iff _ f).1 (hc s)) b t
  have h' := h.comp
    ((baseChange (T.fromSpecResidueField t)).map (kernelBaseChangeIso b f).inv)
  rw [← Functor.map_comp, kernelBaseChangeIso_inv_ι] at h'
  exact h'

/-- The focused local Artinian input gives centrality over every scheme base,
by the arbitrary affine result and locality on the affine open cover. -/
theorem isCentral_kernel
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {G H : GroupScheme S} (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f))) :
    IsCentral (kernelι f) := by
  apply isCentral_of_openCover S.affineCover (kernelι f)
  intro k
  let b := S.affineCover.f k
  apply (isCentral_kernel_baseChange_iff b f).1
  exact isCentral_kernel_of_affine ha (hG.baseChange b) (hH.baseChange b)
    ((baseChange b).map f)
    (MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hq)
    (MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hf)
    (MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hs)
    (central_kernel_fibres_baseChange f hc b)

/-- The unchanged actual kernel bundled as commutative over an arbitrary
scheme, retaining the focused local Artinian input. -/
def centralKernelOfArtinianInput
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {G H : GroupScheme S} (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f))) : CommGroupScheme S :=
  (isCentral_kernel ha hG hH f hq hf hs hc).commGroupScheme

@[simp]
theorem centralKernelOfArtinianInput_toGrp
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {G H : GroupScheme S} (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f))) :
    (centralKernelOfArtinianInput ha hG hH f hq hf hs hc).toGrp = kernel f := rfl

/-- The focused local Artinian centrality input suffices for the unchanged
fibrewise central-isogeny criterion, using the relative-centre theorem. -/
theorem criterion_of_artinianInput
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u}) :
    ReductiveFibrewiseCentralIsogenyStatement.{u} := by
  apply FibrewiseCentralIsogenyFiniteAssembly.criterion_of_kernelCentrality
    reductiveRelativeCenter
  intro B G H hG hH f hs hk
  have hf := FibrewiseCentralIsogenyReduction.flat_and_locallyQuasiFinite_of_finite_kernel_fibres
    hG hH f hs (fun s => (hk s).1)
  exact isCentral_kernel ha hG hH f hf.2 hf.1 hs (fun s => (hk s).2)

end Langlands.GroupScheme.GlobalKernelCentrality
