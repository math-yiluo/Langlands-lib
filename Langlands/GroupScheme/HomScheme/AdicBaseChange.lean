import Langlands.GroupScheme.HomScheme.MultiplicativeTargetEtale
import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.Descent.PullHomCoherence
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Change of base for actual relative Hom families -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {S T : Scheme.{u}} (p : T ⟶ S) {H G : GroupScheme S}

/-- Express a family over the changed base as a family over the original base. -/
def flatten (V : Over T)
    (f : RelativeHom ((baseChange p).obj H) ((baseChange p).obj G) V) :
    RelativeHom H G ((Over.map p).obj V) :=
  (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).inv ≫ f ≫
    (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl G).hom

/-- Re-express a family as a family for the base-changed groups. -/
def unflatten (V : Over T) (f : RelativeHom H G ((Over.map p).obj V)) :
    RelativeHom ((baseChange p).obj H) ((baseChange p).obj G) V :=
  (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).hom ≫ f ≫
    (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl G).inv

@[simp] theorem flatten_unflatten (V : Over T)
    (f : RelativeHom H G ((Over.map p).obj V)) :
    flatten p V (unflatten p V f) = f := by
  simp [flatten, unflatten]

@[simp] theorem unflatten_flatten (V : Over T)
    (f : RelativeHom ((baseChange p).obj H) ((baseChange p).obj G) V) :
    unflatten p V (flatten p V f) = f := by
  simp [flatten, unflatten]

/-- Changing the base does not change the actual family of homomorphisms. -/
def flattenEquiv (V : Over T) :
    RelativeHom ((baseChange p).obj H) ((baseChange p).obj G) V ≃
      RelativeHom H G ((Over.map p).obj V) :=
  (baseChangeEquiv (H := H) (G := G) p V).symm

@[reassoc] theorem flatten_fst (V : Over T)
    (f : RelativeHom ((baseChange p).obj H) ((baseChange p).obj G) V) :
    (flatten p V f).hom.hom.left ≫ pullback.fst G.X.hom (V.hom ≫ p) =
      (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).inv.hom.hom.left ≫
        f.hom.hom.left ≫ pullback.fst ((baseChange p).obj G).X.hom V.hom ≫
          pullback.fst G.X.hom p := by
  simp only [flatten, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_hom_fst]

@[reassoc] private theorem flatten_projection {V W : Over T} (a : W ⟶ V) :
    (Descent.pullbackComparison p W.hom (W.hom ≫ p) rfl H).inv.hom.hom.left ≫
        baseChangeProj ((baseChange p).obj H) a =
      baseChangeProj H ((Over.map p).map a) ≫
        (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).inv.hom.hom.left := by
  apply (cancel_mono
    (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).hom.hom.hom.left).mp
  simp only [Category.assoc]
  apply pullback.hom_ext
  · simp only [Category.assoc, Descent.pullbackComparison_hom_fst,
      baseChangeProj_fst_assoc, Descent.pullbackComparison_inv_fst]
    exact (baseChangeProj_fst H ((Over.map p).map a)).symm
  · have hV := Over.w
      (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).hom.hom.hom
    have hW := Over.w
      (Descent.pullbackComparison p W.hom (W.hom ≫ p) rfl H).inv.hom.hom
    change _ ≫ pullback.snd H.X.hom (V.hom ≫ p) =
      pullback.snd ((baseChange p).obj H).X.hom V.hom at hV
    change _ ≫ pullback.snd ((baseChange p).obj H).X.hom W.hom =
      pullback.snd H.X.hom (W.hom ≫ p) at hW
    have hVi := Over.w
      (Descent.pullbackComparison p V.hom (V.hom ≫ p) rfl H).inv.hom.hom
    change _ ≫ pullback.snd ((baseChange p).obj H).X.hom V.hom =
      pullback.snd H.X.hom (V.hom ≫ p) at hVi
    simp only [Category.assoc, hV, baseChangeProj_snd, hVi,
      reassoc_of% hW]
    exact (baseChangeProj_snd H ((Over.map p).map a)).symm

/-- Re-expressing a family commutes with restriction to any test scheme. -/
theorem flatten_evaluate {V W : Over T} (a : W ⟶ V)
    (f : RelativeHom ((baseChange p).obj H) ((baseChange p).obj G) V) :
    flatten p W (evaluate a f) =
      evaluate ((Over.map p).map a) (flatten p V f) := by
  apply relativeHom_ext
  rw [evaluate_fst]
  simp only [Over.map_obj_hom]
  rw [flatten_fst, evaluate_fst_assoc, flatten_projection_assoc]
  exact congrArg (baseChangeProj H ((Over.map p).map a) ≫ ·) (flatten_fst p V f).symm

/-- Constant families flatten to direct pullbacks. -/
@[simp] theorem flatten_baseChange (V : Over T)
    (f : (baseChange p).obj H ⟶ (baseChange p).obj G) :
    flatten p V ((baseChange V.hom).map f) =
      evaluate (Over.homMk V.hom rfl : (Over.map p).obj V ⟶ Over.mk p) f := by
  rfl

/-- Restriction along a flat surjective test map detects actual homomorphisms. -/
theorem evaluate_injective_of_flat_surjective {V W : Over S} (a : W ⟶ V)
    [Flat a.left] [Surjective a.left] [QuasiCompact a.left] :
    Function.Injective (evaluate (H := H) (G := G) a) := by
  intro f g h
  have he : (baseChange a.left).map f = (baseChange a.left).map g := by
    apply (cancel_epi (Descent.pullbackComparison V.hom a.left W.hom (Over.w a) H).inv).mp
    apply (cancel_mono (Descent.pullbackComparison V.hom a.left W.hom (Over.w a) G).hom).mp
    exact h
  apply Grp.hom_ext
  apply (Over.pullback a.left).map_injective
  exact congrArg (fun k => k.hom.hom) he

end Langlands.GroupScheme.HomScheme
