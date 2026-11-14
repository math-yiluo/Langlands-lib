import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeight
import Langlands.GroupScheme.Torus.NumberedCharacterDescent

/-! # Scheme-kernel alignment under scalar extension of split pinnings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace characterLattice

variable {S S' : Scheme.{u}} {T : CommGroupScheme S} {H H' : GroupScheme S}

/-- An actual character kills the full kernel of a supplied torus homomorphism,
tested over every relative scheme. -/
def TrivialOnKernel (chi : characterLattice T) (f : T.toGrp ⟶ H) : Prop :=
  ∀ (U : Over S) (t : U ⟶ T.X),
    t ≫ f.hom.hom = 1 → t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1

theorem TrivialOnKernel.of_postcomp (chi : characterLattice T)
    (f : T.toGrp ⟶ H) (g : H ⟶ H')
    (h : TrivialOnKernel chi (f ≫ g)) : TrivialOnKernel chi f := by
  intro U t ht
  apply h U t
  simp only [Grp.comp_hom_hom, ← Category.assoc, ht, MonObj.one_comp]

theorem TrivialOnKernel.comp_mono (chi : characterLattice T)
    (f : T.toGrp ⟶ H) (g : H ⟶ H') [Mono g.hom.hom]
    (h : TrivialOnKernel chi f) : TrivialOnKernel chi (f ≫ g) := by
  intro U t ht
  apply h U t
  apply (cancel_mono g.hom.hom).mp
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.one_comp] using ht

/-- The all-test-scheme kernel condition ascends under arbitrary base change.
No smoothness, reducedness or field-points test is used. -/
theorem TrivialOnKernel.baseChange (b : S' ⟶ S)
    (chi : characterLattice T) (f : T.toGrp ⟶ H)
    (h : TrivialOnKernel chi f) :
    TrivialOnKernel (baseChange b T chi) ((GroupScheme.baseChange b).map f) := by
  intro U t ht
  have ht' : baseChangePointsEquiv b T.toGrp U t ≫ f.hom.hom = 1 := by
    rw [← baseChangePointsEquiv_comp, ht, map_one]
  have hc := h ((Over.map b).obj U) (baseChangePointsEquiv b T.toGrp U t) ht'
  change (t ≫ ((GroupScheme.baseChange b).map
    (CommGroupScheme.groupHom chi)).hom.hom) ≫
      (Gm.baseChangeIso b).hom.hom.hom = 1
  have hc' : t ≫ ((GroupScheme.baseChange b).map
      (CommGroupScheme.groupHom chi)).hom.hom = 1 := by
    apply (baseChangePointsEquiv b (Gm S).toGrp U).injective
    simpa only [baseChangePointsEquiv_comp, map_one] using hc
  rw [hc', MonObj.one_comp]

end characterLattice

namespace SplitPinning

variable {k : Type u} [Field k]
    {G H H' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (p : SplitPinning G)

/-- The fundamental weight at the supplied simple vertex kills the actual
torus kernel of the supplied map. -/
def FundamentalWeightTrivialOnKernel (v : p.base.support) (pi : G ⟶ H) : Prop :=
  ∀ chi : characterLattice p.torus,
    latticePairing _ chi (p.rootDatum.coroot v.val) = 1 →
    (∀ w : p.base.support, w ≠ v →
      latticePairing _ chi (p.rootDatum.coroot w.val) = 0) →
    characterLattice.TrivialOnKernel chi (p.inclusion ≫ pi)

theorem FundamentalWeightTrivialOnKernel.of_postcomp
    (v : p.base.support) (pi : G ⟶ H) (f : H ⟶ H')
    (h : p.FundamentalWeightTrivialOnKernel v (pi ≫ f)) :
    p.FundamentalWeightTrivialOnKernel v pi := by
  intro chi hv hw
  exact characterLattice.TrivialOnKernel.of_postcomp chi (p.inclusion ≫ pi) f
    (by simpa only [Category.assoc] using h chi hv hw)

theorem FundamentalWeightTrivialOnKernel.comp_mono
    (v : p.base.support) (pi : G ⟶ H) (f : H ⟶ H') [Mono f.hom.hom]
    (h : p.FundamentalWeightTrivialOnKernel v pi) :
    p.FundamentalWeightTrivialOnKernel v (pi ≫ f) := by
  intro chi hv hw
  simpa only [Category.assoc] using
    characterLattice.TrivialOnKernel.comp_mono chi (p.inclusion ≫ pi) f (h chi hv hw)

variable {F : Type u} [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]

local instance alignedPinningBaseChangeIsAffineHom : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k F)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k F))
  infer_instance

/-- Kernel alignment ascends with the actual split pinning, retaining the
original simple index and every relative kernel point. -/
theorem FundamentalWeightTrivialOnKernel.baseChange
    (v : p.base.support) (pi : G ⟶ H)
    (h : p.FundamentalWeightTrivialOnKernel v pi) :
    (p.baseChange (F := F)).FundamentalWeightTrivialOnKernel
      (p.baseChangeSimpleEquiv (F := F) v)
      ((GroupScheme.baseChange (algebraBaseMap k F)).map pi) := by
  intro chi hv hw
  let chi0 := (characterLattice.baseChangeEquiv
    (algebraBaseMap k F) p.torus p.isSplitTorus).symm chi
  have hchi : characterLattice.baseChange (algebraBaseMap k F) p.torus chi0 = chi :=
    (characterLattice.baseChangeEquiv
      (algebraBaseMap k F) p.torus p.isSplitTorus).apply_symm_apply chi
  have hpair (a : p.base.support) :
      latticePairing p.torus chi0 (p.rootDatum.coroot a.val) =
        latticePairing (p.baseChange (F := F)).torus chi
          ((p.baseChange (F := F)).rootDatum.coroot
            (p.baseChangeSimpleEquiv (F := F) a).val) := by
    rw [← latticePairing_baseChange (algebraBaseMap k F) p.torus, hchi]
    rfl
  have h0 := h chi0 (by rw [hpair v]; exact hv) (by
    intro a ha
    rw [hpair a]
    exact hw _ (fun hEq => ha ((p.baseChangeSimpleEquiv (F := F)).injective hEq)))
  have hbc := characterLattice.TrivialOnKernel.baseChange (algebraBaseMap k F)
    chi0 (p.inclusion ≫ pi) h0
  rw [hchi] at hbc
  change characterLattice.TrivialOnKernel chi
    ((GroupScheme.baseChange (algebraBaseMap k F)).map p.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k F)).map pi)
  simpa only [Functor.map_comp] using hbc

end SplitPinning

namespace TitsIndexData

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)

/-- The host index's alignment is precisely the alignment of its actual split
pinning over the separable closure. -/
theorem fundamentalWeightTrivialOnKernel_iff (v : d.Vertex) (pi : G ⟶ H) :
    d.FundamentalWeightTrivialOnKernel v pi ↔
      d.pinning.toSplitPinning.FundamentalWeightTrivialOnKernel v
        ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map pi) := by
  simp only [FundamentalWeightTrivialOnKernel,
    SplitPinning.FundamentalWeightTrivialOnKernel, characterLattice.TrivialOnKernel,
    GaloisPinningData.toSplitPinning, ← Functor.map_comp]

end TitsIndexData

end Langlands.GroupScheme
