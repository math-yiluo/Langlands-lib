import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Rational.RootFactorPairConsequences

/-! # Coefficient conjugation of actual normalizing opposite pairs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

section Descent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    {T : CommGroupScheme B} {G : GroupScheme B} {i : T.toGrp ⟶ G}

/-- Canonical descent preserves the normalizer point subgroup, with the
specified transported point. -/
theorem mem_normalizerPoints_descentBaseChange
    {n : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X}
    (hn : n ∈ normalizerPoints (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i)) :
    GroupScheme.baseChangeBasePoint a ((GroupScheme.baseChange b).obj G) n ≫
      (descentBaseChangeIso b a ha G).hom.hom.hom ∈
        normalizerPoints (T := (CommGroupScheme.baseChange b).obj T)
          ((GroupScheme.baseChange b).map i) := by
  obtain ⟨τ, hτ⟩ := hn
  exact ⟨_, hτ.baseChange_descent b a ha i⟩

end Descent

section Galois

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "GK" => Functor.obj (GroupScheme.baseChange b) G
local notation "TK" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "iK" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

namespace RelativeRoot

/-- Actual coefficient conjugation transports both ordered opposite
factors, the middle point, and the normalizing triple. -/
theorem IsOppositeFactorPair.rationalConjugate
    {a : characterLattice TK} {x : rationalPoints GK}
    {q : rationalPoints GK × rationalPoints GK}
    (hq : IsOppositeFactorPair (T := TK) iK a x q) (σ : K ≃ₐ[k] K) :
    IsOppositeFactorPair (T := TK) iK
      (characterLattice.galoisRepresentation k K T σ a)
      (rationalConjugate k K G σ x)
      (rationalConjugate k K G σ q.1, rationalConjugate k K G σ q.2) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_neg] using
      (rationalConjugate_mem_subgroup_iff k K i σ (-a) q.1).mpr hq.1
  · simpa only [map_neg] using
      (rationalConjugate_mem_subgroup_iff k K i σ (-a) q.2).mpr hq.2.1
  · simpa only [map_mul] using
      rationalConjugate_mem_normalizerPoints k K i σ hq.2.2

/-- The actual map on ordered opposite factor pairs induced by coefficient
conjugation, with no additional choice of factors. -/
def oppositeFactorPairsGaloisMap (σ : K ≃ₐ[k] K)
    (a : characterLattice TK) (x : rationalPoints GK) :
    {q // IsOppositeFactorPair (T := TK) iK a x q} →
      {q // IsOppositeFactorPair (T := TK) iK
        (characterLattice.galoisRepresentation k K T σ a)
        (rationalConjugate k K G σ x) q} :=
  fun q => ⟨(rationalConjugate k K G σ q.val.1,
    rationalConjugate k K G σ q.val.2), q.property.rationalConjugate k K i σ⟩

@[simp] theorem oppositeFactorPairsGaloisMap_val (σ : K ≃ₐ[k] K)
    (a : characterLattice TK) (x : rationalPoints GK)
    (q : {q // IsOppositeFactorPair (T := TK) iK a x q}) :
    (oppositeFactorPairsGaloisMap k K i σ a x q).val =
      (rationalConjugate k K G σ q.val.1,
        rationalConjugate k K G σ q.val.2) := rfl

end RelativeRoot

end Galois

end Langlands.GroupScheme
