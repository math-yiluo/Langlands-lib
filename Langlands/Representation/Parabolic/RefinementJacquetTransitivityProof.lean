import Langlands.Representation.Parabolic.RefinementTransitivityStatement

/-! The actual iterated and composed upper coinvariant quotients. -/

noncomputable section

namespace Langlands.Parabolic.JacquetTransitivity

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

section Vectors

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)

/-- The outer radical class map, descended from the full composed class map. -/
private def firstMap : B.JacquetModule ρ →ₗ[ℂ] ComposedJacquetModule B S ρ :=
  Jacquet.lift (ρ.comp (B.parabolic F.Carrier).subtype) (B.unipotentRadical F.Carrier)
    (composedJacquetMk B S ρ) (by
      intro u
      ext v
      exact Jacquet.mk_apply_subgroup ρ (composedUnipotent F.Carrier B S)
        (radicalInPreimage F.Carrier B (refinedUnipotent F.Carrier B S) u) v)

private theorem firstMap_mk (v : V) :
    firstMap B S ρ (B.jacquetMk ρ v) = composedJacquetMk B S ρ v := rfl

/-- The inner radical acts on outer classes without a normalizing scalar. -/
private theorem normalizedJacquet_refinedUnipotent
    (u : refinedUnipotent F.Carrier B S) (v : V) :
    T.normalizedJacquet B ρ u.val (B.jacquetMk ρ v) =
      B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier u.val) v) := by
  rw [T.normalizedJacquet_mk_eq_inv_halfModulus,
    T.leviHalfModulus_refinedUnipotent B S u, inv_one, one_smul]

/-- The iterated class map descends from the outer classes to the full quotient. -/
private def forward :
    RefinedJacquetModule B S (T.normalizedJacquet B ρ) →ₗ[ℂ]
      ComposedJacquetModule B S ρ :=
  Jacquet.lift (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S)
    (firstMap B S ρ) (by
      intro u
      apply LinearMap.ext
      intro x
      obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
      change firstMap B S ρ (T.normalizedJacquet B ρ u.val (B.jacquetMk ρ v)) = _
      rw [normalizedJacquet_refinedUnipotent T B S ρ u, firstMap_mk, firstMap_mk]
      exact Jacquet.mk_apply_subgroup ρ (composedUnipotent F.Carrier B S)
        (preimageSection F.Carrier B (refinedUnipotent F.Carrier B S) u) v)

private theorem forward_mk (v : V) :
    forward T B S ρ (refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v)) =
      composedJacquetMk B S ρ v := rfl

/-- The composite of the two quotient maps. -/
private def iteratedMk : V →ₗ[ℂ] RefinedJacquetModule B S (T.normalizedJacquet B ρ) :=
  (refinedJacquetMk B S (T.normalizedJacquet B ρ)).comp (B.jacquetMk ρ)

/-- Every element of the full radical factors as an outer radical element times an
embedded inner radical element, and both factors fix iterated classes. -/
private theorem iteratedMk_invariant (g : composedUnipotent F.Carrier B S) :
    iteratedMk T B S ρ ∘ₗ ρ g.val = iteratedMk T B S ρ := by
  ext v
  let H := refinedUnipotent F.Carrier B S
  let u := preimageUnipotentPart F.Carrier B H g
  let m := preimageProjection F.Carrier B H g
  have hdecomp : (radicalInPreimage F.Carrier B H u * preimageSection F.Carrier B H m) = g :=
    (preimageDecomposition F.Carrier B H).left_inv g
  have hout : B.jacquetMk ρ (ρ g.val v) =
      B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m.val) v) := by
    rw [← hdecomp]
    change B.jacquetMk ρ (ρ (u.val.val * B.leviEmbedding F.Carrier m.val) v) = _
    rw [map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F.Carrier).subtype)
      (B.unipotentRadical F.Carrier) u _
  change refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ (ρ g.val v)) = _
  rw [hout, ← normalizedJacquet_refinedUnipotent T B S ρ m]
  exact Jacquet.mk_apply_subgroup (T.normalizedJacquet B ρ) H m _

private def backward :
    ComposedJacquetModule B S ρ →ₗ[ℂ]
      RefinedJacquetModule B S (T.normalizedJacquet B ρ) :=
  Jacquet.lift ρ (composedUnipotent F.Carrier B S)
    (iteratedMk T B S ρ) (iteratedMk_invariant T B S ρ)

private theorem backward_mk (v : V) :
    backward T B S ρ (composedJacquetMk B S ρ v) =
      refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v) := rfl

/-- The forward map intertwines the iterated and direct inverse-half actions. -/
private theorem forward_action (m : refinedLevi F.Carrier B S) (v : V) :
    forward T B S ρ (T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ) m
        (refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v))) =
      T.normalizedComposedJacquet B S ρ m (composedJacquetMk B S ρ v) := by
  rw [T.normalizedRefinedJacquet_mk, T.normalizedJacquet_mk_eq_inv_halfModulus,
    Units.smul_def, map_smul, map_smul, map_smul, forward_mk,
    T.normalizedComposedJacquet_mk, T.inverseHalf_composedLeviModulus,
    MonoidHom.mul_apply, MonoidHom.inv_apply, T.refinedOuterHalfModulus_apply,
    smul_smul, Units.val_mul, mul_comm]

private theorem backward_forward
    (x : RefinedJacquetModule B S (T.normalizedJacquet B ρ)) :
    backward T B S ρ (forward T B S ρ x) = x := by
  obtain ⟨y, rfl⟩ := Jacquet.mk_surjective (T.normalizedJacquet B ρ)
    (refinedUnipotent F.Carrier B S) x
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ y
  rfl

private theorem forward_backward (x : ComposedJacquetModule B S ρ) :
    forward T B S ρ (backward T B S ρ x) = x := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (composedUnipotent F.Carrier B S) x
  rfl

private theorem forward_comp (m : refinedLevi F.Carrier B S) :
    forward T B S ρ ∘ₗ T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ) m =
      T.normalizedComposedJacquet B S ρ m ∘ₗ forward T B S ρ := by
  apply Representation.Coinvariants.hom_ext
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro v
  exact forward_action T B S ρ m v

/-- The objectwise equivariant linear equivalence, with the explicit inverse. -/
private def transitivityEquiv :
    (T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)).Equiv
      (T.normalizedComposedJacquet B S ρ) where
  toLinearEquiv :=
    { forward T B S ρ with
      invFun := backward T B S ρ
      left_inv := backward_forward T B S ρ
      right_inv := forward_backward T B S ρ }
  isIntertwining' := forward_comp T B S ρ

private theorem transitivityEquiv_mk (v : V) :
    transitivityEquiv T B S ρ
        (refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v)) =
      composedJacquetMk B S ρ v := rfl

end Vectors

/-- The categorical natural isomorphism with these components. -/
private def transitivityIso :
    letI := T.topology
    (T.normalizedJacquetFunctor.{uF, uV} B ⋙ T.normalizedRefinedJacquetFunctor B S) ≅
      T.normalizedComposedJacquetFunctor.{uF, uV} B S := by
  letI := T.topology
  refine NatIso.ofComponents
    (fun A => SmoothRep.mkIso (transitivityEquiv T B S A.representation)) ?_
  intro A A' f
  ext x
  obtain ⟨y, rfl⟩ := Jacquet.mk_surjective (T.normalizedJacquet B A.representation)
    (refinedUnipotent F.Carrier B S) x
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective A.representation y
  rfl

end Langlands.Parabolic.JacquetTransitivity

namespace Langlands.Parabolic

universe uF uV

/-- Natural normalized Jacquet transitivity for the actual composed radical of every
block refinement: iterated classes go to full composed-radical classes. -/
theorem normalizedRefinementJacquetTransitivity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    NormalizedRefinementJacquetTransitivityClause.{uF, uV} F T B S := by
  let := T.topology
  exact ⟨JacquetTransitivity.transitivityIso T B S, fun A v => rfl⟩

end Langlands.Parabolic
