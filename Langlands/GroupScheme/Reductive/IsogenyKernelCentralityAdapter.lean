import Langlands.GroupScheme.Reductive.IsogenyKernelCentrality
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # From full-kernel torus containment to ambient centrality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section GeneralBase

variable {S : Scheme.{u}} {G H : GroupScheme S} {T T' : CommGroupScheme S}
    (q : G ⟶ H) (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H)
    (t : T.toGrp ⟶ T'.toGrp) [Mono i'.hom.hom]
    (ht : i ≫ q = t ≫ i')
    (κ : kernel q ⟶ T.toGrp) (hκ : κ ≫ i = kernelι q)

/-- A factorization of the ambient kernel through the source torus lands in
the actual kernel of the torus map. -/
def kernelRestrictionFactorOfTorusFactor : kernel q ⟶ kernel t := by
  let hr : (SubgroupFunctor.range (kernelι t)).IsRepresentedBy (kernelι t) :=
    ⟨inferInstance, rfl⟩
  refine hr.factorHom κ ?_
  intro V y hy
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  apply (mem_range_kernelι_iff t _).mpr
  apply (cancel_mono i'.hom.hom).mp
  rw [MonObj.one_comp]
  calc
    ((x ≫ κ.hom.hom) ≫ t.hom.hom) ≫ i'.hom.hom =
        x ≫ (κ ≫ t ≫ i').hom.hom := by
      simp only [Grp.comp_hom_hom, Category.assoc]
    _ = x ≫ (κ ≫ i ≫ q).hom.hom := by rw [← ht]
    _ = (x ≫ (kernelι q).hom.hom) ≫ q.hom.hom := by
      rw [← Category.assoc, hκ]
      rfl
    _ = 1 := (kernelPointsEquiv q V x).property

theorem kernelRestrictionFactorOfTorusFactor_comp :
    kernelRestrictionFactorOfTorusFactor q i i' t ht κ hκ ≫ kernelι t = κ := by
  unfold kernelRestrictionFactorOfTorusFactor
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

theorem kernelRestrictionFactorOfTorusFactor_comp_comp :
    kernelRestrictionFactorOfTorusFactor q i i' t ht κ hκ ≫ kernelι t ≫ i =
      kernelι q := by
  rw [← Category.assoc, kernelRestrictionFactorOfTorusFactor_comp, hκ]

include i' ht κ hκ in
/-- Centrality of the full torus kernel transfers to the ambient kernel when
the latter factors through that torus. -/
theorem isCentral_kernelι_of_torusFactor
    (hc : IsCentral (kernelι t ≫ i)) : IsCentral (kernelι q) := by
  rw [← kernelRestrictionFactorOfTorusFactor_comp_comp q i i' t ht κ hκ]
  exact hc.comp _

end GeneralBase

section Field

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsConnectedReductive G)
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hplus : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier V →
        x ≫ q.hom.hom = 1 → x = 1)
    (hminus : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).carrier V →
        x ≫ q.hom.hom = 1 → x = 1)

/-- For a generic cocharacter of a split maximal torus in a connected
reductive source, opposite unipotent kernel triviality gives a torus factor. -/
def kernelTorusFactorOfGenericUnipotentKernels : kernel q ⟶ T.toGrp := by
  have : Smooth G.X.hom := hG.smooth
  have hself := maximalTorusCentralizer k G hG T i hi
  have hcent := genericCentralizer k G hG T i (hi.isMaximalSplitTorus hT) ν hν
  exact kernelTorusFactorOfUnipotentKernels q hT.isTorus i hi.2.1 hself
    (CommGroupScheme.groupHom ν ≫ i) (hcent.trans hself) hplus hminus

theorem kernelTorusFactorOfGenericUnipotentKernels_comp :
    kernelTorusFactorOfGenericUnipotentKernels hG q hT i hi ν hν hplus hminus ≫ i =
      kernelι q := by
  have : Smooth G.X.hom := hG.smooth
  unfold kernelTorusFactorOfGenericUnipotentKernels
  exact kernelTorusFactorOfUnipotentKernels_comp _ _ _ _ _ _ _ _ _

include hG hT hi ν hν hplus hminus in
/-- If every source root is pulled back through the supplied split-torus map,
the full ambient kernel is central once the two unipotent kernels are trivial. -/
theorem isCentral_kernelι_of_generic_unipotent_kernels
    (hT' : IsSplitTorus T'.toGrp) (i' : T'.toGrp ⟶ H) (hi' : IsClosedSubgroup i')
    (t : T.toGrp ⟶ T'.toGrp) (ht : i ≫ q = t ≫ i')
    (hroots : ∀ α ∈ roots i, ∃ ψ : characterLattice T',
      α = characterLattice.comapHom t ψ) :
    IsCentral (kernelι q) := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let κ := kernelTorusFactorOfGenericUnipotentKernels hG q hT i hi ν hν hplus hminus
  have hκ : κ ≫ i = kernelι q :=
    kernelTorusFactorOfGenericUnipotentKernels_comp _ _ _ _ _ _ _ _ _
  exact isCentral_kernelι_of_torusFactor q i i' t ht κ hκ
    (isCentral_kernelι_comp_of_roots_comapHom hT hT' i t hroots)

end Field

end Langlands.GroupScheme
