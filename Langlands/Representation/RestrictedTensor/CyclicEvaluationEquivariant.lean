import Langlands.Representation.RestrictedTensor.CyclicEvaluationInjective

/-! # Full restricted-product equivariance of cyclic evaluation -/

noncomputable section
open scoped Classical TensorProduct

namespace Langlands.RestrictedTensor.CyclicEvaluation

universe uK uI uG uV

variable {K : Type uK} [Field K] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable (H : ∀ i, Subgroup (G i))
variable (π : Representation K (RestrictedGroup G H) V)

/-- An element trivial at a coordinate commutes with that coordinate action. -/
theorem commute_localAction (t : RestrictedGroup G H) (i : ι) (ht : t i = 1)
    (g : G i) : Commute (π t) (localAction H π i g) := by
  apply LinearMap.ext
  intro x
  change π t (π _ x) = π _ (π t x)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  apply congrArg (fun a : RestrictedGroup G H => π a x)
  ext j
  by_cases hj : j = i
  · subst j
    simp [RestrictedProduct.mulSingleMonoidHom, ht]
  · simp [RestrictedProduct.mulSingleMonoidHom, hj]

/-- The same commutation holds for all coordinate group-algebra operators. -/
theorem commute_localAlgebra (t : RestrictedGroup G H) (i : ι) (ht : t i = 1)
    (a : MonoidAlgebra K (G i)) :
    Commute (π t) ((localAction H π i).asAlgebraHom a) := by
  apply LinearMap.ext
  intro x
  change π t ((localAction H π i).asAlgebraHom a x) =
    (localAction H π i).asAlgebraHom a (π t x)
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g c =>
    have h := LinearMap.congr_fun (commute_localAction H π t i ht g).eq x
    simpa [Representation.asAlgebraHom_single, Module.End.mul_apply] using
      congrArg (fun y : V => c • y) h

/-- A complementary element commutes with the finite product of algebra operators. -/
theorem commute_evalProduct (S : Finset ι) (t : RestrictedGroup G H)
    (ht : ∀ i ∈ S, t i = 1) (a : ∀ i, MonoidAlgebra K (G i)) :
    Commute (π t) (algebraProduct (localAction H π) (localAction_commuting H π) S a) := by
  apply Finset.noncommProd_commute
  intro i hi
  exact commute_localAlgebra H π t i (ht i hi) (a i)

variable (v : V)

/-- A complementary element fixing the generator fixes every finite-stage image. -/
theorem evalStage_fixed (S : Finset ι) (t : RestrictedGroup G H)
    (ht : ∀ i ∈ S, t i = 1) (hv : π t v = v)
    (x : Stage K (Factor (localAction H π) v) S) :
    π t (evalStage (localAction H π) (localAction_commuting H π) v S x) =
      evalStage (localAction H π) (localAction_commuting H π) v S x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    have hc := LinearMap.congr_fun (commute_evalProduct H π S t ht
      (tupleAlgebra (localAction H π) v S x)).eq v
    change π t (algebraProduct _ _ S _ v) = algebraProduct _ _ S _ (π t v) at hc
    simpa only [map_smul, evalStage_tprod, tupleEval, hv] using
      congrArg (fun y : V => c • y) hc
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Enlarging the exceptional set preserves full-tail fixedness of stage images. -/
theorem evalStage_tail_fixed (E : Finset ι)
    (hv : ∀ t ∈ tailReferenceSubgroup H E, π t v = v)
    (S : Index E) (x : Stage K (Factor (localAction H π) v) S.1)
    (t : RestrictedGroup G H) (ht : t ∈ tailReferenceSubgroup H S.1) :
    π t (evalStage (localAction H π) (localAction_commuting H π) v S.1 x) =
      evalStage (localAction H π) (localAction_commuting H π) v S.1 x := by
  apply evalStage_fixed H π v S.1 t ht.1
  apply hv t
  exact ⟨fun i hi => ht.1 i (S.2 hi),
    fun i _ => tailReferenceSubgroup_integral H S.1 ht i⟩

/-- Finite insertion of a restricted tuple is its finite projection. -/
theorem finiteInsertion_restrict (S : Finset ι) (g : RestrictedGroup G H) :
    finiteInsertion H S (fun i : S => g i) = finiteProjection H S g := rfl

variable (E : Finset ι)
variable (he : ∀ i ∉ E, ∀ g ∈ H i,
  (Cyclic.orbitSpan (localAction H π i) v).toRepresentation g
    (Cyclic.generator (localAction H π i) v) = Cyclic.generator (localAction H π i) v)
variable (hv : ∀ t ∈ tailReferenceSubgroup H E, π t v = v)

/-- The restricted-product action on the actual cyclic tensor space. -/
abbrev tensorAction :=
  representation H (fun i => (Cyclic.orbitSpan (localAction H π i) v).toRepresentation)
    E (fun i => Cyclic.generator (localAction H π i) v) he

include hv in
/-- Full-group equivariance on a stage containing all nonreference coordinates. -/
theorem eval_pure_intertwines (g : RestrictedGroup G H) (S : Index E)
    (hg : ∀ i ∉ S.1, g i ∈ H i) (x : ∀ i : S.1, Factor (localAction H π) v i) :
    eval (localAction H π) (localAction_commuting H π) v E
        (tensorAction H π v E he g
          (pure E (fun i => Cyclic.generator (localAction H π i) v) S x)) =
      π g (eval (localAction H π) (localAction_commuting H π) v E
        (pure E (fun i => Cyclic.generator (localAction H π i) v) S x)) := by
  rw [tensorAction, representation_pure_of_mem H _ E _ he g S hg, eval_pure, eval_pure]
  have hf := LinearMap.congr_fun (evalStage_intertwines H π v S.1
    (fun i : S.1 => g i)) (PiTensorProduct.tprod K x)
  have hf' : tupleEval (localAction H π) (localAction_commuting H π) v S.1
      (fun i => (Cyclic.orbitSpan (localAction H π i) v).toRepresentation (g i) (x i)) =
      π (finiteProjection H S.1 g)
        (tupleEval (localAction H π) (localAction_commuting H π) v S.1 x) := by
    simpa only [LinearMap.comp_apply, stageAction, FiniteTensor.external_tprod,
      evalStage_tprod, finiteInsertion_restrict] using hf
  rw [hf']
  symm
  apply apply_eq_finiteProjection_of_tail_fixed H π S.1 _ _ g hg
  intro t ht
  simpa only [evalStage_tprod] using
    evalStage_tail_fixed H π v E hv S (PiTensorProduct.tprod K x) t ht

include hv in
/-- Enlarging to a cofinal stage gives equivariance on the whole direct limit. -/
theorem eval_intertwines (g : RestrictedGroup G H) :
    (eval (localAction H π) (localAction_commuting H π) v E).comp
        (tensorAction H π v E he g) =
      (π g).comp (eval (localAction H π) (localAction_commuting H π) v E) := by
  obtain ⟨F, _, hF⟩ := exists_finset_reference_outside H E g
  apply hom_ext_cofinal F
  intro S hFS x
  exact eval_pure_intertwines H π v E he hv g S
    (fun i hi => hF i (fun hiF => hi (hFS hiF))) x

/-- Evaluation as an intertwiner for the entire actual restricted product. -/
def evalIntertwiner : (tensorAction H π v E he).IntertwiningMap π where
  toLinearMap := eval (localAction H π) (localAction_commuting H π) v E
  isIntertwining' := eval_intertwines H π v E he hv

/-- The all-generator tensor shows that this full-group intertwiner is nonzero. -/
theorem evalIntertwiner_ne_zero (hv0 : v ≠ 0) :
    evalIntertwiner H π v E he hv ≠ 0 := by
  intro h
  have hh := congrArg (fun f : (tensorAction H π v E he).IntertwiningMap π =>
    f (pure E (fun i => Cyclic.generator (localAction H π i) v)
      ⟨E, Finset.Subset.refl E⟩ (fun i => Cyclic.generator (localAction H π i) v))) h
  exact hv0 (by simpa [evalIntertwiner] using hh)

include he hv in
/-- Ambient irreducibility makes the nonzero full-group evaluation surjective. -/
theorem eval_surjective [π.IsIrreducible] (hv0 : v ≠ 0) :
    Function.Surjective (eval (localAction H π) (localAction_commuting H π) v E) :=
  (Representation.IsIrreducible.surjective_or_eq_zero
    (evalIntertwiner H π v E he hv)).resolve_right
      (evalIntertwiner_ne_zero H π v E he hv hv0)

/-- With irreducible scalar-ended local factors, evaluation is a representation equivalence. -/
def evalEquiv [π.IsIrreducible] (hv0 : v ≠ 0)
    (hirr : ∀ i, (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IsIrreducible)
    (hscalar : ∀ i, ∀ f :
      (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IntertwiningMap
        (Cyclic.orbitSpan (localAction H π i) v).toRepresentation,
      ∃ c : K, f = c • Representation.IntertwiningMap.id _) :
    (tensorAction H π v E he).Equiv π :=
  Representation.IntertwiningMap.ofBijective (evalIntertwiner H π v E he hv)
    ⟨eval_injective H π v hv0 hirr hscalar E, eval_surjective H π v E he hv hv0⟩

end Langlands.RestrictedTensor.CyclicEvaluation
