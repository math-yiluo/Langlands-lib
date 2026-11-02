import Langlands.AlgebraicGeometry.Modules.AffinePushforwardBaseChange
import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatPullbackDescent
import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback

/-! # Descent of compatible ordinary module morphisms -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules

/-- Compatibility with the actual canonical overlap comparisons on every scheme test. -/
def PullbackHomCompatible {X Y : Scheme.{u}} (p : X ⟶ Y) {M N : Y.Modules}
    (a : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N) : Prop :=
  ∀ (U : Scheme.{u}) (s t : U ⟶ X) (h : s ≫ p = t ≫ p),
    (Scheme.Modules.pullback s).map a ≫ (equalCompositeIso p s t h N).hom =
      (equalCompositeIso p s t h M).hom ≫ (Scheme.Modules.pullback t).map a

namespace FaithfullyFlatHomDescent

open DerivedSections

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The canonical pullback of any module morphism satisfies every overlap equation. -/
lemma compatible_pullback {M N : Y.Modules} (a : M ⟶ N) :
    PullbackHomCompatible p ((Scheme.Modules.pullback p).map a) := by
  intro U s t h
  exact equalCompositeIso_hom_naturality p s t h a

/-- Geometric kernel-pair compatibility gives the coalgebra-morphism equation. -/
lemma coalgebra_hom_condition [IsAffineHom p] {M N : Y.Modules} [N.IsQuasicoherent]
    (a : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N)
    (ha : (Scheme.Modules.pullback (pullback.fst p p)).map a ≫
        (equalCompositeIso p (pullback.fst p p) (pullback.snd p p) pullback.condition N).hom =
      (equalCompositeIso p (pullback.fst p p) (pullback.snd p p) pullback.condition M).hom ≫
        (Scheme.Modules.pullback (pullback.snd p p)).map a) :
    (Scheme.Modules.pullback p).map
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pushforward p).map a) =
      a ≫ (Scheme.Modules.pullback p).map
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N) := by
  let s : pullback p p ⟶ X := pullback.fst p p
  let t : pullback p p ⟶ X := pullback.snd p p
  let E (Q : Y.Modules) := equalCompositeIso p s t pullback.condition Q
  let B (Q : X.Modules) := pushforwardBaseChange p p t s pullback.condition Q
  have hB : IsIso (B ((Scheme.Modules.pullback p).obj N)) :=
    isIso_pushforwardBaseChange_of_isAffineHom p p t s (IsPullback.of_hasPullback p p) _
  have hunit (Q : Y.Modules) :
      (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app Q) ≫
        B ((Scheme.Modules.pullback p).obj Q) ≫
        (Scheme.Modules.pushforward t).map (E Q).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction t).unit.app
        ((Scheme.Modules.pullback p).obj Q) :=
    pullback_map_unit_comp_pushforwardBaseChange p p t s pullback.condition Q
  rw [← cancel_mono (B ((Scheme.Modules.pullback p).obj N) ≫
    (Scheme.Modules.pushforward t).map (E N).hom)]
  have hnat := pushforwardBaseChange_naturality p p t s pullback.condition a
  change (Scheme.Modules.pullback p).map ((Scheme.Modules.pushforward p).map a) ≫
      B ((Scheme.Modules.pullback p).obj N) =
    B ((Scheme.Modules.pullback p).obj M) ≫
      (Scheme.Modules.pushforward t).map ((Scheme.Modules.pullback s).map a) at hnat
  change (Scheme.Modules.pullback s).map a ≫ (E N).hom =
    (E M).hom ≫ (Scheme.Modules.pullback t).map a at ha
  simp only [Category.assoc]
  rw [reassoc_of% hnat, ← Functor.map_comp, ha, Functor.map_comp]
  rw [reassoc_of% (hunit M), hunit N]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.naturality a).symm

/-- Compatibility on the actual kernel pair suffices for unique descent. -/
lemma existsUnique_hom_of_kernelPair [IsAffineHom p] [Flat p] [Surjective p]
    {M N : Y.Modules} [N.IsQuasicoherent]
    (a : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N)
    (ha : (Scheme.Modules.pullback (pullback.fst p p)).map a ≫
        (equalCompositeIso p (pullback.fst p p) (pullback.snd p p) pullback.condition N).hom =
      (equalCompositeIso p (pullback.fst p p) (pullback.snd p p) pullback.condition M).hom ≫
        (Scheme.Modules.pullback (pullback.snd p p)).map a) :
    ∃! b : M ⟶ N, (Scheme.Modules.pullback p).map b = a := by
  have := isEquivalence_modulePullbackComparison p
  have := faithful_pullback_of_flat_surjective p
  let A : (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction p)).obj M ⟶
      (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction p)).obj N :=
    ⟨a, coalgebra_hom_condition p a ha⟩
  let b := (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction p)).preimage A
  have hb : (Scheme.Modules.pullback p).map b = a :=
    congrArg Comonad.Coalgebra.Hom.f (Functor.map_preimage _ A)
  exact ⟨b, hb, fun c hc => (Scheme.Modules.pullback p).map_injective (hc.trans hb.symm)⟩

/-- A compatible morphism on an affine flat surjective cover descends uniquely. -/
lemma existsUnique_hom [IsAffineHom p] [Flat p] [Surjective p]
    {M N : Y.Modules} [N.IsQuasicoherent]
    (a : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N)
    (ha : PullbackHomCompatible p a) :
    ∃! b : M ⟶ N, (Scheme.Modules.pullback p).map b = a :=
  existsUnique_hom_of_kernelPair p a (ha _ _ _ _)

/-- A compatible isomorphism descends uniquely, with its actual pullback prescribed. -/
lemma existsUnique_iso [IsAffineHom p] [Flat p] [Surjective p]
    {M N : Y.Modules} [N.IsQuasicoherent]
    (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N)
    (he : PullbackHomCompatible p e.hom) :
    ∃! b : M ≅ N, (Scheme.Modules.pullback p).mapIso b = e := by
  obtain ⟨b, hb, huniq⟩ := existsUnique_hom p e.hom he
  have := pullback_reflectsIsomorphisms_of_flat_surjective p
  have : IsIso ((Scheme.Modules.pullback p).map b) := by
    rw [hb]
    infer_instance
  have : IsIso b := isIso_of_reflects_iso b (Scheme.Modules.pullback p)
  refine ⟨asIso b, ?_, ?_⟩
  · apply Iso.ext
    exact hb
  · intro c hc
    apply Iso.ext
    exact huniq c.hom (congrArg Iso.hom hc)

end FaithfullyFlatHomDescent

end Langlands.AlgebraicGeometry.Modules
