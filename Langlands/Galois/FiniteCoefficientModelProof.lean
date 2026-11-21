import Langlands.Galois.FiniteCoefficientModelStatement
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BaseChange
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite coefficient models from the representation trace -/

noncomputable section

open scoped MonoidAlgebra Matrix
open Module

universe uE uL uV

namespace Langlands.GaloisRepresentation

private theorem image_isSemisimpleRing {C G V : Type*} [Field C] [Monoid G]
    [AddCommGroup V] [Module C V] [FiniteDimensional C V] (ρ : Representation C G V)
    (hρ : ρ.IsSemisimpleRepresentation) : IsSemisimpleRing ρ.asAlgebraHom.range := by
  let B := ρ.asAlgebraHom.range
  let f := ρ.asAlgebraHom.rangeRestrict
  let : Module B V := Module.compHom V B.val.toRingHom
  have : RingHomSurjective f.toRingHom := ⟨ρ.asAlgebraHom.rangeRestrict_surjective⟩
  let equiv : ρ.asModule →ₛₗ[f.toRingHom] V :=
    { ρ.asModuleEquiv.toAddMonoidHom with
      map_smul' := ρ.asModuleEquiv_map_smul }
  have : IsSemisimpleModule B V :=
    (equiv.isSemisimpleModule_iff_of_bijective ρ.asModuleEquiv.bijective).mp
      (ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mp hρ)
  let b := Module.finBasis C V
  have : IsSemisimpleModule B (Fin (finrank C V) → V) :=
    IsSemisimpleModule.congr (Finsupp.linearEquivFunOnFinite B V _).symm
  let eval : B →ₗ[B] (Fin (finrank C V) → V) := {
    toFun := fun x i => B.val x (b i)
    map_add' x y := by
      funext i
      change B.val (x + y) (b i) = B.val x (b i) + B.val y (b i)
      rw [map_add, LinearMap.add_apply]
    map_smul' _ _ := rfl }
  exact IsSemisimpleModule.of_injective (R := B) eval fun x y hxy =>
    Subtype.val_injective (b.ext fun i => congrFun hxy i)

/-- The trace is taken on the original carrier, with its given action of the image algebra. -/
private def representationTraceForm {C V : Type*} [Field C] [AddCommGroup V] [Module C V]
    (B : Subalgebra C (Module.End C V)) : LinearMap.BilinForm C B :=
  (LinearMap.mul C B).compr₂ ((LinearMap.trace C V).comp B.val.toLinearMap)

private theorem representationTraceForm_nondegenerate {C V : Type*} [Field C] [CharZero C]
    [AddCommGroup V] [Module C V] [FiniteDimensional C V]
    (B : Subalgebra C (Module.End C V)) [IsSemisimpleRing B] :
    (representationTraceForm B).Nondegenerate := by
  have hsymm : (representationTraceForm B).IsSymm := ⟨fun x y => by
    change LinearMap.trace C V (B.val (x * y)) = LinearMap.trace C V (B.val (y * x))
    simp only [map_mul, LinearMap.trace_mul_comm]⟩
  apply hsymm.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  obtain ⟨e, he, hspan⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have he_mem : e ∈ Ideal.span ({x} : Set B) := hspan ▸ Ideal.mem_span_singleton_self e
  obtain ⟨y, hye⟩ := Ideal.mem_span_singleton'.mp he_mem
  have htrace : LinearMap.trace C V (B.val e) = 0 := by
    rw [← hye, map_mul, LinearMap.trace_mul_comm, ← map_mul]
    exact hx y
  have he' : IsIdempotentElem (B.val e) := he.map B.val
  have he_zero : e = 0 :=
    Subtype.val_injective ((LinearMap.IsIdempotentElem.trace_eq_zero_iff he').mp htrace)
  have hx_mem := Ideal.mem_span_singleton_self x
  rwa [hspan, he_zero, Ideal.span_singleton_zero, Submodule.mem_bot] at hx_mem

/-- Simultaneous finite coefficient field for the matrices of the given representation. -/
theorem finiteCoefficientModel : FiniteCoefficientModelStatement.{uE, uL, uV} := by
  classical
  intro E _ K C _ _ _ _ _ _ _ A
  unfold Objects at A
  intro Λ₀ hΛ₀ hss htrace
  have : FiniteDimensional K Λ₀ := hΛ₀
  let G := Field.absoluteGaloisGroup E
  let ρ : Representation C G A.val := A.val.representation
  let B := ρ.asAlgebraHom.range
  let f := ρ.asAlgebraHom.rangeRestrict
  let action (g : G) : B := f (MonoidAlgebra.basis G C g)
  have haction (g : G) : B.val (action g) = ρ g := ρ.asAlgebraHom_single_one g
  have hgenerate : Submodule.span C (Set.range action) = ⊤ := by
    change Submodule.span C (Set.range (f.toLinearMap ∘ MonoidAlgebra.basis G C)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
      LinearMap.range_eq_top]
    exact ρ.asAlgebraHom.rangeRestrict_surjective
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent C (Set.range action)
  let d : Basis s C B := Basis.mk hli (by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hspan, hgenerate])
  have : Finite s := Module.Finite.finite_basis d
  let : Fintype s := Fintype.ofFinite s
  have hd (k : s) : ∃ g, action g = d k := by
    simpa only [d, Basis.mk_apply, Set.mem_range] using hs k.property
  choose g hg using hd
  have : IsSemisimpleRing B := image_isSemisimpleRing ρ hss
  let form := representationTraceForm B
  let dual := form.dualBasis (representationTraceForm_nondegenerate B) d
  have hdual (x : B) (k : s) : dual.repr x k = form x (d k) :=
    LinearMap.BilinForm.dualBasis_repr_apply _ d x k
  have hpair (γ δ : G) : form (action γ) (action δ) ∈ (algebraMap K C).fieldRange := by
    change LinearMap.trace C A.val (B.val (action γ * action δ)) ∈ (algebraMap K C).range
    rw [map_mul, haction, haction, ← map_mul]
    exact htrace (γ * δ)
  have hgram (k l : s) : dual.toMatrix d k l ∈ (algebraMap K C).fieldRange := by
    rw [Basis.toMatrix_apply, hdual, ← hg l, ← hg k]
    exact hpair (g l) (g k)
  have hgram_inv := Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left
    (Equiv.refl s) _ (d.toMatrix_mul_toMatrix_flip dual) hgram
  have hcoeff (γ : G) (k : s) : d.repr (action γ) k ∈ (algebraMap K C).fieldRange := by
    have h := dual.toMatrix_mulVec_repr d (action γ)
    rw [← congrFun h k, Matrix.mulVec, dotProduct]
    apply sum_mem
    intro l _
    refine mul_mem (hgram_inv k l) ?_
    rw [hdual, ← hg l]
    exact hpair γ (g l)
  let b : Basis (Fin A.val.rank) C A.val := Module.finBasis C A.val
  let M := (LinearMap.toMatrix b b).toLinearMap.comp B.val.toLinearMap
  let S := Set.range fun t : s × Fin A.val.rank × Fin A.val.rank => M (d t.1) t.2.1 t.2.2
  have : Finite S := (Set.finite_range _).to_subtype
  let Λ₁ := IntermediateField.adjoin K S
  have : FiniteDimensional K Λ₁ :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  refine ⟨b, Λ₀ ⊔ Λ₁, le_sup_left, inferInstance, ?_⟩
  intro γ i j
  change LinearMap.toMatrix b b (ρ γ) i j ∈ Λ₀ ⊔ Λ₁
  rw [← haction γ]
  change M (action γ) i j ∈ Λ₀ ⊔ Λ₁
  have hsum : M (action γ) = ∑ k, d.repr (action γ) k • M (d k) := by
    calc
      M (action γ) = M (∑ k, d.repr (action γ) k • d k) :=
        congrArg M (d.sum_repr (action γ)).symm
      _ = ∑ k, d.repr (action γ) k • M (d k) := by simp only [map_sum, map_smul]
  rw [hsum, Matrix.sum_apply]
  apply (Λ₀ ⊔ Λ₁).sum_mem
  intro k _
  rw [Matrix.smul_apply, smul_eq_mul]
  obtain ⟨c, hc⟩ := hcoeff γ k
  rw [← hc]
  have hle : Λ₁ ≤ Λ₀ ⊔ Λ₁ := le_sup_right
  exact mul_mem ((Λ₀ ⊔ Λ₁).algebraMap_mem c)
    (hle (IntermediateField.subset_adjoin K S ⟨(k, i, j), rfl⟩))

end Langlands.GaloisRepresentation
