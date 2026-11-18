import Langlands.GroupScheme.Reductive.TitsKernelStarRestriction
import Langlands.GroupScheme.SimplyConnected.TypeEAnisotropicKernelModel
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient

/-! # Star-fixed weight restriction to the actual anisotropic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G}

/-- Actual integral character restriction from the ambient absolute torus to
the absolute torus of the actual anisotropic kernel. -/
def weightRestriction (p : d.AnisotropicKernelIndex) :
    characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
          d.pinning.torus) →ₗ[ℤ]
      characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
          p.index.pinning.torus) :=
  p.comparison.weightRestriction

/-- Restriction to the actual anisotropic kernel is precomposition with the
base change of the actual kernel torus morphism. -/
theorem weightRestriction_apply (p : d.AnisotropicKernelIndex)
    (x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)) :
    p.weightRestriction x = p.comparison.weightRestriction x :=
  rfl

/-- For simply connected `G`, restriction to the actual anisotropic kernel
intertwines the full absolute star actions. -/
theorem weightRestriction_starAction (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G) (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)) :
    p.weightRestriction ((d.pinning.starAction σ).val.weightEquiv x) =
      (p.index.pinning.starAction σ).val.weightEquiv (p.weightRestriction x) :=
  p.comparison.weightRestriction_starAction
    (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc)) σ x

/-- For simply connected `G`, restriction to the actual anisotropic kernel
carries full-star-fixed weights to full-star-fixed weights. -/
theorem weightRestriction_starFixed (p : d.AnisotropicKernelIndex)
    (hsc : IsSimplyConnected G)
    {x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)}
    (hx : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      (d.pinning.starAction σ).val.weightEquiv x = x)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    (p.index.pinning.starAction σ).val.weightEquiv (p.weightRestriction x) =
      p.weightRestriction x :=
  p.comparison.weightRestriction_starFixed
    (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc)) hx σ

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
