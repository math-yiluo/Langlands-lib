import Langlands.Geometry.Building.SplitTorusNormalizerBaseChange
import Langlands.GroupScheme.Rational.RingEquivBaseChange

/-! # Reflection of rational normalizer points under field extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

/-- An original rational point normalizes the torus exactly when its extension does. -/
theorem mem_normalizerPoints_rationalExtend_iff (n : rationalPoints G) :
    rationalExtend k K G n ∈ normalizerPoints (T := S_K) i_K ↔
      n ∈ normalizerPoints i := by
  constructor
  · rintro ⟨τ, hτ⟩
    have hfpqc := fieldExtension_fpqc k K
    have : Surjective b := hfpqc.1
    have : Flat b := hfpqc.2.1
    have : QuasiCompact b := hfpqc.2.2
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    let eK : (GroupScheme.baseChange b).obj S.toGrp ≅
        (GroupScheme.baseChange b).obj S.toGrp :=
      { hom := CommGroupScheme.groupHom τ.hom
        inv := CommGroupScheme.groupHom τ.inv
        hom_inv_id := congrArg Additive.toMul τ.hom_inv_id
        inv_hom_id := congrArg Additive.toMul τ.inv_hom_id }
    have heK : i_K ≫ (((GroupScheme.baseChange b).obj G).innerIso
        (baseChangeBasePoint b G n)).hom = eK.hom ≫ i_K := by
      simpa only [IsNormalizingPoint,
        ← rationalExtend_eq_baseChangeBasePoint k K G] using hτ
    let e : S.toGrp ≅ S.toGrp :=
      subgroupConjugacyIsoOfBaseChange b i i n eK heK
    let σ : S ≅ S := CommGroupScheme.isoOfGroupIso e
    refine ⟨σ, ?_⟩
    exact (subgroupConjugacyIsoOfBaseChange_hom_comp b i i n eK heK).symm
  · rintro ⟨σ, hσ⟩
    exact ⟨(CommGroupScheme.baseChange b).mapIso σ, hσ.rationalExtend (K := K) i⟩

/-- Bijective field extension gives a bijection on the actual normalizer subgroups. -/
theorem normalizerPointsFieldExtend_bijective
    (h : Function.Bijective (algebraMap k K)) :
    Function.Bijective (normalizerPointsFieldExtend (K := K) i) := by
  have hθ := rationalExtend_bijective_of_bijective k K G h
  constructor
  · intro n m hnm
    apply Subtype.ext
    exact hθ.injective (congrArg Subtype.val hnm)
  · intro n
    obtain ⟨g, hg⟩ := hθ.surjective n.val
    have hgn : g ∈ normalizerPoints i :=
      (mem_normalizerPoints_rationalExtend_iff (K := K) i g).mp (hg.symm ▸ n.property)
    exact ⟨⟨g, hgn⟩, Subtype.ext hg⟩

/-- The actual normalizer-point equivalence under a bijective extension of fields. -/
def normalizerPointsFieldEquiv (h : Function.Bijective (algebraMap k K)) :
    normalizerPoints i ≃* normalizerPoints (T := S_K) i_K :=
  MulEquiv.ofBijective (normalizerPointsFieldExtend (K := K) i)
    (normalizerPointsFieldExtend_bijective i h)

@[simp]
theorem normalizerPointsFieldEquiv_coe (h : Function.Bijective (algebraMap k K))
    (n : normalizerPoints i) :
    (normalizerPointsFieldEquiv (K := K) i h n : rationalPoints (baseChanged k K G)) =
      rationalExtend k K G n.val := rfl

end Langlands.GroupScheme
