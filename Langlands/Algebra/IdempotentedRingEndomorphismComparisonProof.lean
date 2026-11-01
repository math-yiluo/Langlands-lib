import Langlands.Algebra.IdempotentedRingEndomorphismComparison
import Langlands.Algebra.IdempotentedRingTopologyProof

/-!
# Proofs of the comparison and closure targets for the right-linear model

Renard I.1.4, printed p.10/PDF16, and I.1.6, printed pp.11-12/PDF17-18.
Each of the five published component targets is proved separately, and the
aggregate is their conjunction.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Filter Set IdempotentedRingEndomorphism
open scoped Uniformity Topology

universe uA

namespace IdempotentedRingEndomorphismComparisonProof

variable {A : Type uA} [NonUnitalRing A]

/-- A left local unit for one original element. -/
theorem exists_leftLocalUnit (hA : IsIdempotented A) (a : A) :
    ∃ e : Idempotent A, (e : A) * a = a := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a}
  exact ⟨e, (he a (by simp)).1⟩

/-- Evaluating the actual endomorphism of a family at the idempotents recovers it. -/
theorem idempotentEvaluation_toRightLinearEnd (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) :
    idempotentEvaluation (toRightLinearEnd hA x) = x := by
  apply Subtype.ext
  funext e
  exact toRightLinearEnd_idempotent hA x e

/-- A right-linear endomorphism is determined by its values at idempotents:
`β a = β (e * a) = β e * a` for a left local unit `e` of `a`. -/
theorem toRightLinearEnd_idempotentEvaluation (hA : IsIdempotented A)
    (β : RightLinearEnd A) :
    toRightLinearEnd hA (idempotentEvaluation β) = β := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨e, he⟩ := exists_leftLocalUnit hA a
  calc (toRightLinearEnd hA (idempotentEvaluation β)).val a
      = (idempotentEvaluation β).val e * a := toRightLinearEnd_apply_eq hA _ a e he
    _ = β.val ((e : A) * a) := (rightLinearEnd_apply_mul β (e : A) a).symm
    _ = β.val a := by rw [he]

/-- The restricted pointwise uniformity, pulled back along the forward map, is the
pullback of the value-function product along `applyOriginal hA`. -/
theorem comap_toRightLinearEnd_eq (hA : IsIdempotented A) :
    UniformSpace.comap
        (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
        (rightLinearEndUniformSpace A) =
      UniformSpace.comap (IdempotentedRingRightLimit.applyOriginal hA)
        (functionUniformSpace A) := by
  rw [rightLinearEndUniformSpace_eq_function_comap, ← UniformSpace.comap_comap]
  rfl

/-- Every coordinate `x ↦ x(e)` is uniformly continuous from the pulled-back
pointwise uniformity to the discrete uniformity, since `x(e) = (x · e) e`. -/
theorem uniformContinuous_coordinate_of_comap (hA : IsIdempotented A) (e : Idempotent A) :
    @UniformContinuous (IdempotentedRingRightLimit A) A
      (UniformSpace.comap (IdempotentedRingRightLimit.applyOriginal hA)
        (functionUniformSpace A))
      (⊥ : UniformSpace A) (fun x : IdempotentedRingRightLimit A => x.val e) := by
  have hfun : (fun x : IdempotentedRingRightLimit A => x.val e) =
      (fun a : A => a * (e : A)) ∘ (fun g : A → A => g (e : A)) ∘
        IdempotentedRingRightLimit.applyOriginal hA := by
    funext x
    change x.val e = IdempotentedRingRightLimit.applyOriginal hA x (e : A) * (e : A)
    rw [IdempotentedRingRightLimit.applyOriginal_idempotent, x.property.1 e]
  rw [hfun]
  have hproj : @UniformContinuous (A → A) A (functionUniformSpace A)
      (idempotentedRingUniformSpace A) (fun g : A → A => g (e : A)) := by
    let : UniformSpace A := idempotentedRingUniformSpace A
    exact Pi.uniformContinuous_proj (fun _ : A => A) (e : A)
  exact @UniformContinuous.comp _ _ _
    (UniformSpace.comap (IdempotentedRingRightLimit.applyOriginal hA)
      (functionUniformSpace A))
    (idempotentedRingUniformSpace A) (⊥ : UniformSpace A) _ _
    (idempotentedRing_uniformContinuous_rightCoordinate e)
    (@UniformContinuous.comp _ _ _
      (UniformSpace.comap (IdempotentedRingRightLimit.applyOriginal hA)
        (functionUniformSpace A))
      (functionUniformSpace A) (idempotentedRingUniformSpace A) _ _ hproj
      (@uniformContinuous_comap _ _ _ (functionUniformSpace A)))

/-- Conversely, `applyOriginal hA` is uniformly continuous from the family
uniformity: `x(a) f = (x(e) a) f` for a left local unit `e` of `a`. -/
theorem uniformContinuous_applyOriginal (hA : IsIdempotented A) :
    @UniformContinuous (IdempotentedRingRightLimit A) (A → A)
      (IdempotentedRingRightLimit.uniformSpace A) (functionUniformSpace A)
      (IdempotentedRingRightLimit.applyOriginal hA) := by
  let : UniformSpace A := idempotentedRingUniformSpace A
  let : UniformSpace (IdempotentedRingRightLimit A) :=
    IdempotentedRingRightLimit.uniformSpace A
  apply uniformContinuous_pi.mpr
  intro a
  obtain ⟨e, he⟩ := exists_leftLocalUnit hA a
  change @UniformContinuous (IdempotentedRingRightLimit A) A
    (IdempotentedRingRightLimit.uniformSpace A)
    (⨅ f : Idempotent A,
      UniformSpace.comap (fun b : A => b * (f : A)) (⊥ : UniformSpace A))
    (fun x => IdempotentedRingRightLimit.applyOriginal hA x a)
  refine uniformContinuous_iInf_rng.mpr (fun f => ?_)
  apply @uniformContinuous_comap' _ _ _ _ _ (⊥ : UniformSpace A)
  have hfun : ((fun b : A => b * (f : A)) ∘
      fun x : IdempotentedRingRightLimit A =>
        IdempotentedRingRightLimit.applyOriginal hA x a) =
      (fun c : A => c * a * (f : A)) ∘ IdempotentedRingRightLimit.coordinate e := by
    funext x
    change IdempotentedRingRightLimit.applyOriginal hA x a * (f : A) =
      x.val e * a * (f : A)
    rw [IdempotentedRingRightLimit.applyOriginal_eq hA x a e he]
  rw [hfun]
  have hdisc : @UniformContinuous A A (⊥ : UniformSpace A) (⊥ : UniformSpace A)
      (fun c : A => c * a * (f : A)) :=
    uniformContinuous_iff_le_comap.mpr bot_le
  exact @UniformContinuous.comp _ _ _
    (IdempotentedRingRightLimit.uniformSpace A) (⊥ : UniformSpace A)
    (⊥ : UniformSpace A) _ _ hdisc
    (IdempotentedRingRightLimit.uniformContinuous_coordinate e)

/-- The uniformity comparison for one original ring. -/
theorem comap_toRightLinearEnd (hA : IsIdempotented A) :
    UniformSpace.comap
        (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
        (rightLinearEndUniformSpace A) =
      IdempotentedRingRightLimit.uniformSpace A := by
  rw [comap_toRightLinearEnd_eq hA]
  apply le_antisymm
  · change _ ≤ ⨅ e : Idempotent A,
      UniformSpace.comap (fun x : IdempotentedRingRightLimit A => x.val e)
        (⊥ : UniformSpace A)
    exact le_iInf fun e =>
      uniformContinuous_iff_le_comap.mp (uniformContinuous_coordinate_of_comap hA e)
  · exact uniformContinuous_iff_le_comap.mp (uniformContinuous_applyOriginal hA)

/-- The right-linear subset is closed: it is an intersection of equalizers of
continuous maps into the Hausdorff original carrier. -/
theorem rightLinearEnd_isClosed (hA : IsIdempotented A) :
    @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
      (rightLinearEnd A : Set (AddMonoid.End A)) := by
  let : UniformSpace A := idempotentedRingUniformSpace A
  let : UniformSpace (AddMonoid.End A) := pointwiseUniformSpace A
  have : T2Space A := idempotentedRing_hausdorff hA
  have hset : (rightLinearEnd A : Set (AddMonoid.End A)) =
      ⋂ a : A, ⋂ b : A, {β : AddMonoid.End A | β (a * b) = β a * b} := by
    ext β
    simp only [SetLike.mem_coe, mem_rightLinearEnd, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
  exact isClosed_eq (uniformContinuous_evaluation (a * b)).continuous
    ((idempotentedRing_rightMultiplicationUniform hA b).continuous.comp
      (uniformContinuous_evaluation a).continuous)

/-- The closure lemma for one original ring. The left multiplications by `β e`
converge to `β` along the directed set of idempotents. -/
theorem closure_range_leftMultiplication (hA : IsIdempotented A) :
    @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
      (rightLinearEnd A : Set (AddMonoid.End A)) := by
  classical
  let : UniformSpace A := idempotentedRingUniformSpace A
  let : UniformSpace (AddMonoid.End A) := pointwiseUniformSpace A
  apply Set.Subset.antisymm
  · apply closure_minimal _ (rightLinearEnd_isClosed hA)
    rintro _ ⟨a, rfl⟩
    exact (mem_rightLinearEnd _).mpr fun b c => (mul_assoc a b c).symm
  · intro β hβ
    have hβ' : ∀ a b : A, β (a * b) = β a * b := (mem_rightLinearEnd β).mp hβ
    have : IsDirectedOrder (Idempotent A) := ⟨fun e f => by
      obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
      exact ⟨g, hg e (by simp), hg f (by simp)⟩⟩
    have : Nonempty (Idempotent A) := ⟨⟨0, IsIdempotentElem.zero⟩⟩
    have hind : @Topology.IsInducing (AddMonoid.End A) (A → A)
        (pointwiseUniformSpace A).toTopologicalSpace
        (functionUniformSpace A).toTopologicalSpace
        (fun γ : AddMonoid.End A => (γ : A → A)) := ⟨rfl⟩
    refine mem_closure_of_tendsto (b := atTop)
      (f := fun e : Idempotent A => leftMultiplication (β (e : A))) ?_
      (Eventually.of_forall fun e => ⟨β (e : A), rfl⟩)
    apply hind.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_nhds_of_eventually_eq
    obtain ⟨e₀, he₀⟩ := exists_leftLocalUnit hA a
    refine eventually_atTop.mpr ⟨e₀, fun e he => ?_⟩
    have hea : (e : A) * a = a := Idempotent.mul_eq_of_le he he₀
    change β (e : A) * a = β a
    rw [← hβ', hea]

end IdempotentedRingEndomorphismComparisonProof

open IdempotentedRingEndomorphismComparisonProof

/-- Both inverse identities hold for every original ring with finite local units. -/
theorem idempotentedRingEndomorphismInverseIdentities_proof :
    IdempotentedRingEndomorphismInverseIdentities.{uA} :=
  fun _ _ hA => ⟨idempotentEvaluation_toRightLinearEnd hA,
    toRightLinearEnd_idempotentEvaluation hA⟩

/-- The fixed maps assemble into an actual ring equivalence for the published
family ring. -/
theorem idempotentedRingEndomorphismRingEquivalence_proof :
    IdempotentedRingEndomorphismRingEquivalence.{uA} := by
  intro A _ hA
  let := IdempotentedRingRightLimit.ring hA
  exact ⟨{ toFun := toRightLinearEnd hA
           invFun := idempotentEvaluation
           left_inv := idempotentEvaluation_toRightLinearEnd hA
           right_inv := toRightLinearEnd_idempotentEvaluation hA
           map_mul' := map_mul (toRightLinearEnd hA)
           map_add' := map_add (toRightLinearEnd hA) }, rfl, rfl⟩

/-- The named uniformities agree along the actual forward map. -/
theorem idempotentedRingEndomorphismUniformityComparison_proof :
    IdempotentedRingEndomorphismUniformityComparison.{uA} :=
  fun _ _ hA => comap_toRightLinearEnd hA

/-- The right-linear subset is closed for the specified pointwise topology. -/
theorem idempotentedRingEndomorphismRightLinearClosed_proof :
    IdempotentedRingEndomorphismRightLinearClosed.{uA} :=
  fun _ _ hA => rightLinearEnd_isClosed hA

/-- Renard's I.1.6 closure lemma in all additive endomorphisms. -/
theorem idempotentedRingEndomorphismClosureLemma_proof :
    IdempotentedRingEndomorphismClosureLemma.{uA} :=
  fun _ _ hA => closure_range_leftMultiplication hA

/-- The aggregate comparison and closure target. -/
theorem idempotentedRingEndomorphismComparisonTheorem_proof :
    IdempotentedRingEndomorphismComparisonTheorem.{uA} :=
  ⟨idempotentedRingEndomorphismInverseIdentities_proof,
    idempotentedRingEndomorphismRingEquivalence_proof,
    idempotentedRingEndomorphismUniformityComparison_proof,
    idempotentedRingEndomorphismRightLinearClosed_proof,
    idempotentedRingEndomorphismClosureLemma_proof⟩

end Langlands.Algebra
