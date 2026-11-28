import Langlands.AlgebraicGeometry.AffineCechDeRham
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Relative form maps for a change of coefficient algebra -/

noncomputable section

universe u

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

namespace Langlands.AlgebraicGeometry.AffineCechDeRham.RelativeForms

variable {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] [Algebra R A] [Algebra T B]
  (e : A →+* B) (he : ∀ r : R, e (algebraMap R A r) = algebraMap T B (algebraMap R T r))

/-- Pullback on relative Kähler differentials in a commuting square of rings. -/
def mapOneAcross : Ω[A⁄R] →ₛₗ[e] Ω[B⁄T] := by
  let : Algebra A B := e.toAlgebra
  let : Algebra R B := ((algebraMap T B).comp (algebraMap R T)).toAlgebra
  let : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (he r).symm)
  let F := KaehlerDifferential.map R T A B
  exact
    { F.toAddMonoidHom with
      map_smul' := fun a ω => by
        change F (a • ω) = e a • F ω
        rw [F.map_smul, ← IsScalarTower.algebraMap_smul B a]
        rfl }

@[simp]
lemma mapOneAcross_d (a : A) :
    mapOneAcross e he (KaehlerDifferential.D R A a) = KaehlerDifferential.D T B (e a) := by
  let : Algebra A B := e.toAlgebra
  let : Algebra R B := ((algebraMap T B).comp (algebraMap R T)).toAlgebra
  let : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (he r).symm)
  exact KaehlerDifferential.map_D R T A B a

private def alternatingTwoAcross :
    letI : Module A (Two T B) := Module.compHom (Two T B) e
    Ω[A⁄R] [⋀^Fin 2]→ₗ[A] Two T B := by
  letI : Module A (Two T B) := Module.compHom (Two T B) e
  exact
    { toFun := fun v => exteriorPower.ιMulti B 2 (mapOneAcross e he ∘ v)
      map_update_add' := by
        intro _ v i x y
        simp only [Function.comp_update, (mapOneAcross e he).map_add, AlternatingMap.map_update_add]
      map_update_smul' := by
        intro _ v i a x
        change exteriorPower.ιMulti B 2 (mapOneAcross e he ∘ Function.update v i (a • x)) =
          e a • exteriorPower.ιMulti B 2 (mapOneAcross e he ∘ Function.update v i x)
        rw [Function.comp_update, Function.comp_update, (mapOneAcross e he).map_smulₛₗ,
          AlternatingMap.map_update_smul]
      map_eq_zero_of_eq' := fun v _ _ h hne =>
        (exteriorPower.ιMulti B 2).map_eq_zero_of_eq _ (congrArg (mapOneAcross e he) h) hne }

/-- Pullback on relative two-forms across the same coefficient square. -/
def mapTwoAcross : Two R A →ₛₗ[e] Two T B := by
  letI : Module A (Two T B) := Module.compHom (Two T B) e
  let F := exteriorPower.alternatingMapLinearEquiv (alternatingTwoAcross e he)
  exact { F.toAddMonoidHom with map_smul' := F.map_smul }

@[simp]
lemma mapTwoAcross_ιMulti (v : Fin 2 → Ω[A⁄R]) :
    mapTwoAcross e he (exteriorPower.ιMulti A 2 v) =
      exteriorPower.ιMulti B 2 (mapOneAcross e he ∘ v) := by
  let : Module A (Two T B) := Module.compHom (Two T B) e
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (alternatingTwoAcross e he) v

@[simp]
lemma mapTwoAcross_wedge (x y : Ω[A⁄R]) :
    mapTwoAcross e he (wedge x y) = wedge (mapOneAcross e he x) (mapOneAcross e he y) := by
  rw [wedge, mapTwoAcross_ιMulti, wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The pullback on relative forms commutes with the exterior differential. -/
lemma mapTwoAcross_dOne (x : Ω[A⁄R]) :
    mapTwoAcross e he (dOne R A x) = dOne T B (mapOneAcross e he x) := by
  obtain ⟨x, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, (mapOneAcross e he).map_smulₛₗ, mapOneAcross_d,
      dOne_smul_d, dOne_smul_d, mapTwoAcross_wedge, mapOneAcross_d, mapOneAcross_d]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, map_add, hx, hy]

section Restriction

variable {A' B' : Type u} [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra T B']
  (e' : A' →+* B') (he' : ∀ r : R, e' (algebraMap R A' r) = algebraMap T B' (algebraMap R T r))
  (a : A →ₐ[R] A') (b : B →ₐ[T] B') (h : b.toRingHom.comp e = e'.comp a.toRingHom)

include h in
/-- One-form pullback is natural under compatible restrictions on the two bases. -/
lemma mapOneAcross_natural (x : Ω[A⁄R]) :
    mapOne b (mapOneAcross e he x) = mapOneAcross e' he' (mapOne a x) := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ =>
    mapOne b (mapOneAcross e he x) = mapOneAcross e' he' (mapOne a x)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, rfl⟩
    simp only [mapOneAcross_d, mapOne_d]
    exact congrArg (KaehlerDifferential.D T B') (DFunLike.congr_fun h z)
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro r z _ hz
    simp only [LinearMap.map_smulₛₗ, hz]
    exact congrArg (· • mapOneAcross e' he' (mapOne a z)) (DFunLike.congr_fun h r)

include h in
/-- Two-form pullback is natural under the same compatible restrictions. -/
lemma mapTwoAcross_natural (x : Two R A) :
    mapTwo b (mapTwoAcross e he x) = mapTwoAcross e' he' (mapTwo a x) := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ =>
    mapTwo b (mapTwoAcross e he x) = mapTwoAcross e' he' (mapTwo a x)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨v, rfl⟩
    simp only [mapTwoAcross_ιMulti, mapTwo_ιMulti]
    exact congrArg (exteriorPower.ιMulti B' 2)
      (funext fun i => mapOneAcross_natural e he e' he' a b h (v i))
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro r z _ hz
    simp only [LinearMap.map_smulₛₗ, hz]
    exact congrArg (· • mapTwoAcross e' he' (mapTwo a z)) (DFunLike.congr_fun h r)

end Restriction

end Langlands.AlgebraicGeometry.AffineCechDeRham.RelativeForms
