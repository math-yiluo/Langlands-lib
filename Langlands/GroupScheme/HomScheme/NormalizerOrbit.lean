import Langlands.GroupScheme.HomScheme.ClosedEmbeddingAction
import Langlands.GroupScheme.HomScheme.NormalizerConjugationFibers
import Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotientOver
import Langlands.GroupScheme.SmoothNormalizer.Global

/-! # Normalizer orbit maps from quotients of closed-embedding schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S} {K : Type u}

/-- All source automorphisms on every relative test are locally among the
indexed constant source isomorphisms. -/
def LocallyExhaustSourceIsomorphisms (H : GroupScheme S) (α : K → (H ≅ H)) : Prop :=
  ∀ (T : Over S) (e : (GroupScheme.baseChange T.hom).obj H ≅
      (GroupScheme.baseChange T.hom).obj H) (x : T.left),
    ∃ (W : Over S) (a : W ⟶ T) (k : K),
      IsOpenImmersion a.left ∧ x ∈ Set.range a.left ∧
        evaluate a e.hom = (GroupScheme.baseChange W.hom).map (α k).hom

private theorem evaluate_compHom {A B C : GroupScheme S} {T T' : Over S}
    (a : T' ⟶ T) (f : RelativeHom A B T) (g : RelativeHom B C T) :
    evaluate a (f ≫ g) = evaluate a f ≫ evaluate a g :=
  Descent.pullHom_comp a.left (Over.w a) (Over.w a) (Over.w a) f g

namespace ClosedEmbeddingModel

variable [Group K] (M : ClosedEmbeddingModel H G) (α : K → (H ≅ H))
  (h1 : (α 1).hom = 𝟙 H)
  (hmul : ∀ g h, (α (g * h)).hom = (α h).hom ≫ (α g).hom)
  (hfaithful : ∀ (T : Over S) [Nonempty T.left],
    Function.Injective (fun k => (GroupScheme.baseChange T.hom).map (α k).hom))
  (Q : (M.precompositionAction α h1 hmul hfaithful).EffectiveQuotient)

open Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineActionOver

/-- The quotient of all closed embeddings by the indexed source automorphisms. -/
def normalizerOrbitTarget : Over S :=
  quotientOver M.scheme (M.precompositionAction α h1 hmul hfaithful)
    (M.precompositionAction_over α h1 hmul hfaithful) Q

/-- The projection from closed embeddings to the source-automorphism quotient. -/
def normalizerOrbitProjection :
    M.scheme ⟶ M.normalizerOrbitTarget α h1 hmul hfaithful Q :=
  quotientMapOver M.scheme (M.precompositionAction α h1 hmul hfaithful)
    (M.precompositionAction_over α h1 hmul hfaithful) Q

theorem normalizerOrbitProjection_invariant (k : K) :
    M.precompose (α k) ≫ M.normalizerOrbitProjection α h1 hmul hfaithful Q =
      M.normalizerOrbitProjection α h1 hmul hfaithful Q :=
  Over.OverMorphism.ext (Q.invariant k)

/-- Conjugate the fixed subgroup, then forget its chosen source coordinates. -/
def normalizerOrbitMap (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    G.X ⟶ M.normalizerOrbitTarget α h1 hmul hfaithful Q :=
  M.conjugationMap i hi ≫ M.normalizerOrbitProjection α h1 hmul hfaithful Q

theorem normalizerOrbitTarget_isQuasiAffine [Finite K] [M.scheme.left.IsQuasiAffine] :
    (M.normalizerOrbitTarget α h1 hmul hfaithful Q).left.IsQuasiAffine :=
  Q.isQuasiAffine

end ClosedEmbeddingModel

namespace ClosedEmbeddingModel

variable {A : CommGroupScheme S} [Group K] (M : ClosedEmbeddingModel A.toGrp G)
  (α : K → (A.toGrp ≅ A.toGrp))
  (h1 : (α 1).hom = 𝟙 A.toGrp)
  (hmul : ∀ g h, (α (g * h)).hom = (α h).hom ≫ (α g).hom)
  (hfaithful : ∀ (T : Over S) [Nonempty T.left],
    Function.Injective (fun k => (GroupScheme.baseChange T.hom).map (α k).hom))
  (Q : (M.precompositionAction α h1 hmul hfaithful).EffectiveQuotient)
  (hlocal : LocallyExhaustSourceIsomorphisms A.toGrp α)
  (i : A.toGrp ⟶ G) (hi : IsClosedSubgroup i)

include hlocal in
/-- The orbit map has exactly full normalizer cosets on every scheme test. -/
theorem normalizerOrbitMap_fibers (T : Over S) (g h : T ⟶ G.X) :
    g ≫ M.normalizerOrbitMap α h1 hmul hfaithful Q i hi =
      h ≫ M.normalizerOrbitMap α h1 hmul hfaithful Q i hi ↔
        g⁻¹ * h ∈ (torusNormalizer i).carrier T := by
  let : Mono i.hom.hom.left := hi.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let q := M.normalizerOrbitProjection α h1 hmul hfaithful Q
  change (g ≫ M.conjugationMap i hi) ≫ q =
    (h ≫ M.conjugationMap i hi) ≫ q ↔ _
  constructor
  · intro he
    have he' : (g ≫ M.conjugationMap i hi).left ≫ Q.map =
        (h ≫ M.conjugationMap i hi).left ≫ Q.map :=
      congrArg Over.Hom.left he
    obtain ⟨𝒰, k, hk⟩ := (Q.eq_iff_locally_act _ _).mp he'
    apply SmoothNormalizer.mem_normalizer_of_openCover i 𝒰 (g⁻¹ * h)
    intro j
    let a := SubgroupFunctor.coverMap 𝒰 j
    change a ≫ (g⁻¹ * h) ∈ (torusNormalizer i).carrier (SubgroupFunctor.coverObj 𝒰 j)
    have hp : (a ≫ g) ≫ M.conjugationMap i hi =
        ((a ≫ h) ≫ M.conjugationMap i hi) ≫ M.precompose (α (k j)) := by
      apply Over.OverMorphism.ext
      change (𝒰.f j ≫ g.left) ≫ (M.conjugationMap i hi).left =
        ((𝒰.f j ≫ h.left) ≫ (M.conjugationMap i hi).left) ≫
          (M.precompose (α (k j))).left
      have hh : 𝒰.f j ≫ (g ≫ M.conjugationMap i hi).left =
          𝒰.f j ≫ (h ≫ M.conjugationMap i hi).left ≫
            (M.precompose (α (k j))).left := hk j
      simpa only [Over.comp_left, Category.assoc] using hh
    have hev := congrArg (fun f => evaluate f M.family) hp
    rw [M.evaluate_conjugationMap, M.evaluate_precompose,
      M.evaluate_conjugationMap] at hev
    have hn := (exists_sourceIso_conjugationFamily_eq_iff i (a ≫ g) (a ≫ h)).mp
      ⟨(GroupScheme.baseChange (SubgroupFunctor.coverObj 𝒰 j).hom).mapIso (α (k j)), hev⟩
    simpa only [MonObj.comp_mul, GrpObj.comp_inv] using hn
  · intro hn
    let E := normalizerPairSourceIso i g h hn
    apply Over.OverMorphism.ext
    apply Scheme.hom_ext_of_forall
    intro x
    obtain ⟨W, a, k, ha, hx, hα⟩ := hlocal T E.val x
    let : IsOpenImmersion a.left := ha
    have hev := congrArg (evaluate a) E.property
    rw [evaluate_conjugationFamily, evaluate_compHom, hα,
      evaluate_conjugationFamily] at hev
    have hp : (a ≫ g) ≫ M.conjugationMap i hi =
        ((a ≫ h) ≫ M.conjugationMap i hi) ≫ M.precompose (α k) := by
      apply M.parameter_ext
      rw [M.evaluate_conjugationMap, M.evaluate_precompose,
        M.evaluate_conjugationMap]
      exact hev
    have hq : a ≫ (g ≫ M.conjugationMap i hi) ≫ q =
        a ≫ (h ≫ M.conjugationMap i hi) ≫ q := by
      have hh := congrArg (fun f => f ≫ q) hp
      have hinv : M.precompose (α k) ≫ q = q :=
        M.normalizerOrbitProjection_invariant α h1 hmul hfaithful Q k
      simpa only [Category.assoc, hinv] using hh
    have hleft := congrArg Over.Hom.left hq
    refine ⟨a.left.opensRange, hx, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp]
    simpa only [Over.comp_left, Category.assoc] using
      congrArg (fun f => a.left.isoOpensRange.inv ≫ f) hleft

end ClosedEmbeddingModel
end Langlands.GroupScheme.HomScheme
