import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Mathlib.Algebra.Group.Units.Equiv

/-! # Global units on relative abelian-scheme families -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Every actual projection `T ×_S A → T` induces an isomorphism on global functions. -/
def UniversalGlobalFunctions : Prop :=
  ∀ T : Over S, IsIso ((relativeProjection A.X.hom).app T).appTop

/-- Universal constancy follows from smoothness, properness and geometric connectedness. -/
theorem universalGlobalFunctions : UniversalGlobalFunctions A := by
  intro T
  exact Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
    (pullback.fst T.hom A.X.hom) inferInstance inferInstance inferInstance ⊤

/-- Pulling back a global unit along the actual projection. -/
def relativeUnitsPullback (T : Over S) :
    Γ(T.left, ⊤)ˣ →* Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ :=
  Units.map ((relativeProjection A.X.hom).app T).appTop.hom.toMonoidHom

/-- The equivalence on actual global units induced by the actual projection. -/
def relativeGlobalUnitsEquiv (h : UniversalGlobalFunctions A) (T : Over S) :
    Γ(T.left, ⊤)ˣ ≃* Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ := by
  letI := h T
  exact Units.mapEquiv
    (asIso ((relativeProjection A.X.hom).app T).appTop).commRingCatIsoToRingEquiv.toMulEquiv

@[simp]
lemma relativeGlobalUnitsEquiv_apply (h : UniversalGlobalFunctions A) (T : Over S)
    (c : Γ(T.left, ⊤)ˣ) :
    relativeGlobalUnitsEquiv A h T c = relativeUnitsPullback A T c := rfl

/-- The unique base unit inducing a unit on the relative family. -/
def relativeUnitDescend (h : UniversalGlobalFunctions A) (T : Over S) :
    Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ →* Γ(T.left, ⊤)ˣ :=
  (relativeGlobalUnitsEquiv A h T).symm.toMonoidHom

@[simp]
lemma relativeUnitsPullback_descend (h : UniversalGlobalFunctions A) (T : Over S)
    (c : Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ) :
    relativeUnitsPullback A T (relativeUnitDescend A h T c) = c :=
  (relativeGlobalUnitsEquiv A h T).apply_symm_apply c

@[simp]
lemma relativeUnitDescend_pullback (h : UniversalGlobalFunctions A) (T : Over S)
    (c : Γ(T.left, ⊤)ˣ) :
    relativeUnitDescend A h T (relativeUnitsPullback A T c) = c :=
  (relativeGlobalUnitsEquiv A h T).symm_apply_apply c

/-- Pullback of base units is injective. -/
lemma relativeUnitsPullback_injective (h : UniversalGlobalFunctions A) (T : Over S) :
    Function.Injective (relativeUnitsPullback A T) :=
  (relativeGlobalUnitsEquiv A h T).injective

/-- The inverse of the projection on units can be evaluated at the actual unit section. -/
lemma relativeUnitDescend_eq_section (h : UniversalGlobalFunctions A) (T : Over S)
    (c : Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ) :
    relativeUnitDescend A h T c =
      Units.map ((relativeSection A.X.hom (unitSection A)
        (unitSection_comp A)).app T).appTop.hom.toMonoidHom c := by
  have hs := congrArg Scheme.Hom.appTop
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hs
  have hb (d : Γ(T.left, ⊤)ˣ) :
      Units.map ((relativeSection A.X.hom (unitSection A)
        (unitSection_comp A)).app T).appTop.hom.toMonoidHom
        (relativeUnitsPullback A T d) = d := by
    apply Units.ext
    exact congrArg (fun m ↦ m (d : Γ(T.left, ⊤))) hs
  have hc := hb (relativeUnitDescend A h T c)
  rw [relativeUnitsPullback_descend] at hc
  exact hc.symm

/-- Any map of relative families lying over `a` has the same effect on base units. -/
lemma relativeUnitsPullback_map {U T : Over S} (a : U ⟶ T)
    (r : (relativeSpace A.X.hom).obj U ⟶ (relativeSpace A.X.hom).obj T)
    (hr : r ≫ (relativeProjection A.X.hom).app T =
      (relativeProjection A.X.hom).app U ≫ a.left) (c : Γ(T.left, ⊤)ˣ) :
    Units.map r.appTop.hom.toMonoidHom (relativeUnitsPullback A T c) =
      relativeUnitsPullback A U (Units.map a.left.appTop.hom.toMonoidHom c) := by
  have he := congrArg Scheme.Hom.appTop hr
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at he
  apply Units.ext
  exact congrArg (fun m ↦ m (c : Γ(T.left, ⊤))) he

/-- Descent of units is natural for every actual map of families over a parameter map. -/
lemma relativeUnitDescend_map (h : UniversalGlobalFunctions A) {U T : Over S}
    (a : U ⟶ T)
    (r : (relativeSpace A.X.hom).obj U ⟶ (relativeSpace A.X.hom).obj T)
    (hr : r ≫ (relativeProjection A.X.hom).app T =
      (relativeProjection A.X.hom).app U ≫ a.left)
    (c : Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ) :
    relativeUnitDescend A h U (Units.map r.appTop.hom.toMonoidHom c) =
      Units.map a.left.appTop.hom.toMonoidHom (relativeUnitDescend A h T c) := by
  apply relativeUnitsPullback_injective A h U
  rw [relativeUnitsPullback_descend, ← relativeUnitsPullback_map A a r hr,
    relativeUnitsPullback_descend]

/-- In particular the descended unit is natural under change of test scheme. -/
lemma relativeUnitDescend_naturality (h : UniversalGlobalFunctions A) {U T : Over S}
    (a : U ⟶ T) (c : Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ) :
    relativeUnitDescend A h U
      (Units.map ((relativeSpace A.X.hom).map a).appTop.hom.toMonoidHom c) =
      Units.map a.left.appTop.hom.toMonoidHom (relativeUnitDescend A h T c) :=
  relativeUnitDescend_map A h a _ ((relativeProjection A.X.hom).naturality a) c

end Langlands.AbelianScheme
