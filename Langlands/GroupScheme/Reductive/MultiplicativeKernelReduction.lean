import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom
import Langlands.GroupScheme.ReducedIdentityCoreSurjective
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Reductive.PerfectFieldProof

/-! # Reduced identity cores of extensions with multiplicative-type kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {E G : GroupScheme (Spec (CommRingCat.of k))}

set_option backward.isDefEq.respectTransparency false

/-- Multiplicative-type full kernels preserve triviality of the ground-field
unipotent radical along faithfully flat maps of affine groups. -/
theorem HasTrivialUnipotentRadical.of_multiplicativeTypeKernel
    [IsAffineHom E.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (p : E ⟶ G) [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    (hD : IsMultiplicativeType (kernel p)) (hG : HasTrivialUnipotentRadical G) :
    HasTrivialUnipotentRadical E := by
  intro U j hj hs hc hu hn
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Smooth U.X.hom := hs
  have : ConnectedSpace U.X.left := hc
  obtain ⟨I, inc, fac, hinc, hfac, hflat, hsurj, hqc, _, hIs, hIc, _⟩ :=
    HomImage.exists_image (j ≫ p)
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Mono inc.hom.hom := Over.mono_of_mono_left _
  have : Flat fac.hom.hom.left := hflat
  have : Surjective fac.hom.hom.left := hsurj
  have : QuasiCompact fac.hom.hom.left := hqc
  have hIn : (SubgroupFunctor.range inc).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square j p fac inc hfac.symm hn
  have hbot := hG I inc hinc hIs hIc (hu.of_flat_surjective fac) hIn
  apply hu.range_eq_bot_of_range_le_isMultiplicativeType hD j (kernelι p) hj
    (show IsClosedImmersion (kernelι p).hom.hom.left from inferInstance)
  intro S x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [mem_range_kernelι_iff]
  have hmem : (y ≫ j.hom.hom) ≫ p.hom.hom ∈
      (SubgroupFunctor.range inc).carrier S := by
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ fac.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hfac, Grp.comp_hom_hom,
      ← Category.assoc]
  simpa only [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hmem

/-- A smooth connected affine extension with multiplicative-type full kernel of
a pseudo-reductive group is pseudo-reductive. -/
theorem IsPseudoReductive.of_multiplicativeTypeKernel
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    (p : E ⟶ G) [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    (hD : IsMultiplicativeType (kernel p)) (hG : IsPseudoReductive G) :
    IsPseudoReductive E := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  exact ⟨inferInstance, inferInstance, inferInstance,
    hG.hasTrivialUnipotentRadical.of_multiplicativeTypeKernel p hD⟩

/-- Over a perfect field, the smooth connected reduced identity core of any
finite-type affine extension of a connected reductive group by a group of
multiplicative type is connected reductive. -/
theorem IsConnectedReductive.identityCore_of_multiplicativeTypeKernel
    [PerfectField k] [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom]
    (p : E ⟶ G) [Flat p.hom.hom.left]
    (hD : IsMultiplicativeType (kernel p)) (hG : IsConnectedReductive G) :
    IsConnectedReductive (ReducedSubgroup.identityCore E) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨hflat, hsurj⟩ := ReducedSubgroup.identityCore_comp_flat_surjective p
  have : Flat (ReducedSubgroup.identityCoreι E ≫ p).hom.hom.left := hflat
  have : Surjective (ReducedSubgroup.identityCoreι E ≫ p).hom.hom.left := hsurj
  have hD' : IsMultiplicativeType (kernel (ReducedSubgroup.identityCoreι E ≫ p)) :=
    hD.kernel_comp_of_isClosedSubgroup p (ReducedSubgroup.identityCoreι E)
      (show IsClosedImmersion (ReducedSubgroup.identityCoreι E).hom.hom.left from inferInstance)
  exact (perfectFieldPseudoReductive k _).mp
    (hG.isPseudoReductive.of_multiplicativeTypeKernel
      (ReducedSubgroup.identityCoreι E ≫ p) hD')

/-- An actual connected reductive closed source inside an extension, together with
its faithfully flat restricted quotient and multiplicative-type full kernel. -/
structure MultiplicativeExtensionCore (p : E ⟶ G) where
  groupScheme : GroupScheme (Spec (CommRingCat.of k))
  reductive : IsConnectedReductive groupScheme
  inclusion : groupScheme ⟶ E
  closed : IsClosedSubgroup inclusion
  flat : Flat (inclusion ≫ p).hom.hom.left
  surjective : Surjective (inclusion ≫ p).hom.hom.left
  kernelMultiplicativeType : IsMultiplicativeType (kernel (inclusion ≫ p))

/-- The canonical reductive source package is the reduced identity core, with its
actual inclusion and the geometry proved above. -/
def IsConnectedReductive.multiplicativeExtensionCore
    [PerfectField k] [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom]
    (p : E ⟶ G) [Flat p.hom.hom.left]
    (hD : IsMultiplicativeType (kernel p)) (hG : IsConnectedReductive G) :
    MultiplicativeExtensionCore p := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨hf, hs⟩ := ReducedSubgroup.identityCore_comp_flat_surjective p
  exact {
    groupScheme := ReducedSubgroup.identityCore E
    reductive := hG.identityCore_of_multiplicativeTypeKernel p hD
    inclusion := ReducedSubgroup.identityCoreι E
    closed := inferInstanceAs
      (IsClosedImmersion (ReducedSubgroup.identityCoreι E).hom.hom.left)
    flat := hf
    surjective := hs
    kernelMultiplicativeType := hD.kernel_comp_of_isClosedSubgroup p
      (ReducedSubgroup.identityCoreι E)
      (inferInstanceAs (IsClosedImmersion (ReducedSubgroup.identityCoreι E).hom.hom.left)) }

end Langlands.GroupScheme
