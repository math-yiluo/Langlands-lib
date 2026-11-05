import Langlands.GroupScheme.HomScheme.Universal

/-! # Recovering actual fibre inclusions from Hom parameters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Evaluation agrees with raw base change through the actual source and target
pullback comparisons. -/
theorem evaluate_comparison {T T' : Over S} (a : T' ⟶ T)
    (i : RelativeHom H G T) :
    (baseChange a.left).map i ≫
        (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) G).hom =
      (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) H).hom ≫
        evaluate a i := by
  simp [evaluate, Descent.pullHom]

/-- Evaluation is a closed immersion exactly when its raw base change is one. -/
theorem isClosedImmersion_evaluate_iff {T T' : Over S} (a : T' ⟶ T)
    (i : RelativeHom H G T) :
    IsClosedImmersion (evaluate a i).hom.hom.left ↔
      IsClosedImmersion ((baseChange a.left).map i).hom.hom.left := by
  constructor
  · intro h
    have heq : (baseChange a.left).map i =
        (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) H).hom ≫
          evaluate a i ≫
          (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) G).inv := by
      simp [evaluate, Descent.pullHom]
    rw [heq]
    change IsClosedImmersion
      ((Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) H).hom.hom.hom.left ≫
        (evaluate a i).hom.hom.left ≫
        (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) G).inv.hom.hom.left)
    infer_instance
  · intro h
    change IsClosedImmersion
      ((Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) H).inv.hom.hom.left ≫
        ((baseChange a.left).map i).hom.hom.left ≫
        (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) G).hom.hom.hom.left)
    infer_instance

/-- Compose the actual iterated-pullback comparison with a chosen direct-fibre
isomorphism. -/
def fibreComparisonIso {U K : Scheme.{u}} (p : U ⟶ S) (c : K ⟶ S)
    (b : K ⟶ U) (hb : b ≫ p = c)
    {T₀ : GroupScheme K} (e₀ : (baseChange c).obj H ≅ T₀) :
    (baseChange b).obj ((baseChange p).obj H) ≅ T₀ :=
  Descent.pullbackComparison p b c hb H ≪≫ e₀

/-- A chosen equality of evaluated actual homomorphisms gives the exact
raw-base-change fibre square, including the equality-of-base-map comparison. -/
theorem recover_fibre_inclusion {U K : Scheme.{u}} (p : U ⟶ S) (c : K ⟶ S)
    (b : K ⟶ U) (hb : b ≫ p = c)
    (T₀ : GroupScheme K) (e₀ : (baseChange c).obj H ≅ T₀)
    (i : RelativeHom H G (Over.mk p))
    (i₀ : T₀ ⟶ (baseChange c).obj G)
    (hi : evaluate (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) i =
      e₀.hom ≫ i₀) :
    ∃ e : (baseChange b).obj ((baseChange p).obj H) ≅ T₀,
      (baseChange b).map i ≫ (baseChangeCompIso p b G).inv ≫
          (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom =
        e.hom ≫ i₀ := by
  refine ⟨fibreComparisonIso p c b hb e₀, ?_⟩
  have h := evaluate_comparison (H := H) (G := G)
    (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) i
  rw [hi] at h
  simpa only [fibreComparisonIso, Descent.pullbackComparison, Iso.trans_hom, Iso.symm_hom,
    Over.mk_hom, Over.homMk_left, Category.assoc] using h

end Langlands.GroupScheme.HomScheme
