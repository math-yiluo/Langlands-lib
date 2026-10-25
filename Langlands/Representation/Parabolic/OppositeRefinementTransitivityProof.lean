import Langlands.Representation.Parabolic.OppositeRefinementTransitivityStatement

/-! The actual iterated and composed opposite coinvariant quotients. -/

noncomputable section

namespace Langlands.Parabolic.OppositeTransitivity

open GeneralLinear Geometric

universe uF uV

private theorem lower_determinant_one {R : Type*} [CommRing R] {n : ℕ}
    (B : BlockShape n) {g : GeneralLinear n R}
    (hg : g ∈ B.oppositeUnipotentSubgroup R) : determinant g = 1 := by
  obtain ⟨hp, hd⟩ := (B.mem_oppositeUnipotentSubgroup_iff R g).mp hg
  let M : Matrix B.Index B.Index R :=
    (g : Matrix (Fin n) (Fin n) R).submatrix B.indexEquiv B.indexEquiv
  have hM : M.BlockTriangular (fun x => OrderDual.toDual x.1) := hp
  have hentry : ∀ (i : Fin B.length) (a b : Fin (B.size i)),
      M ⟨i, a⟩ ⟨i, b⟩ = if a = b then 1 else 0 := hd
  have hblock : ∀ k, M.toSquareBlock (fun x => OrderDual.toDual x.1) k = 1 := by
    intro k
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    change i = OrderDual.ofDual k at hi
    change j = OrderDual.ofDual k at hj
    subst i
    subst j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply, hentry]
    congr 1
    apply propext
    constructor
    · intro hab
      subst b
      rfl
    · intro he
      have he' : (⟨OrderDual.ofDual k, a⟩ : B.Index) =
          ⟨OrderDual.ofDual k, b⟩ := congrArg Subtype.val he
      exact eq_of_heq (Sigma.mk.inj_iff.mp he').2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    ← Matrix.det_submatrix_equiv_self B.indexEquiv, hM.det_fintype]
  simp [hblock]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem outer_full_trivial (u : refinedOppositeUnipotent F.Carrier B S) :
    T.leviModulus B u.val = 1 := by
  apply T.normOneLevi_le_ker_leviModulus B
  apply (T.mem_normOneLevi B u.val).mpr
  intro i
  change T.normalizedAbsUnits (determinant (u.val i)) = 1
  rw [lower_determinant_one (S i)
    ((mem_refinedOppositeUnipotent F.Carrier B S u.val).mp u.property i), map_one]

private theorem outer_half_trivial (u : refinedOppositeUnipotent F.Carrier B S) :
    T.leviHalfModulus B u.val = 1 :=
  (T.leviHalfModulus_eq_one B u.val).mpr (outer_full_trivial T B S u)

private theorem outer_full_projection (q : refinedOppositeParabolic F.Carrier B S) :
    T.refinedOuterModulus B S (refinedOppositeLeviProjection F.Carrier B S q) =
      T.leviModulus B q.val := by
  let u := q * (refinedOppositeLeviSection F.Carrier B S
    (refinedOppositeLeviProjection F.Carrier B S q))⁻¹
  have hu : u.val ∈ refinedOppositeUnipotent F.Carrier B S :=
    (mem_refinedOppositeUnipotentRadical F.Carrier B S u).mp (by
      change refinedOppositeLeviProjection F.Carrier B S u = 1
      simp [u])
  have he := outer_full_trivial T B S ⟨u.val, hu⟩
  change T.leviModulus B
    (q.val * (refinedOppositeLeviProjection F.Carrier B S q).val⁻¹) = 1 at he
  rw [map_mul, map_inv, mul_inv_eq_one] at he
  exact he.symm

private theorem outer_half_projection (q : refinedOppositeParabolic F.Carrier B S) :
    T.refinedOuterHalfModulus B S (refinedOppositeLeviProjection F.Carrier B S q) =
      T.leviHalfModulus B q.val := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.leviModulus B))
    (refinedOppositeLeviProjection F.Carrier B S q).val = _
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom)
      (T.refinedOuterModulus B S (refinedOppositeLeviProjection F.Carrier B S q))) = _
  rw [outer_full_projection T B S]
  rfl

private abbrev outer (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :=
  Rep.of ((Jacquet.normalizedActionOfModulus A.ρ
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹).comp
      (B.leviEquiv F.Carrier).toMonoidHom)

variable (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))

private theorem outer_mk (m : B.Levi F.Carrier) (v : A) :
    (outer T B A).ρ m (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v) =
      (T.leviHalfModulus B m : ℂ) •
        Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier)
          (A.ρ (B.leviEmbedding F.Carrier m) v) := by
  change (Jacquet.inverseHalfCharacter
      ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
      (B.leviEquiv F.Carrier m) : ℂ) •
      Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier)
        (A.ρ (B.leviEmbedding F.Carrier m) v) = _
  congr 1
  simp [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, PadicField.TopologicalData.leviHalfModulus]

private def firstMap :
    outer T B A →ₗ[ℂ] ComposedOppositeJacquetModule B S A.ρ :=
  Jacquet.lift A.ρ (B.oppositeUnipotentSubgroup F.Carrier)
    (composedOppositeJacquetMk B S A.ρ) (by
      intro u
      ext v
      exact Jacquet.mk_apply_subgroup A.ρ (composedOppositeUnipotent F.Carrier B S)
        ⟨u.val, oppositeUnipotentSubgroup_le_composedOppositeUnipotent
          F.Carrier B S u.property⟩ v)

private theorem firstMap_mk (v : A) :
    firstMap T B S A (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v) =
      composedOppositeJacquetMk B S A.ρ v := rfl

private def forward :
    RefinedOppositeJacquetModule B S (outer T B A).ρ →ₗ[ℂ]
      ComposedOppositeJacquetModule B S A.ρ :=
  Jacquet.lift (outer T B A).ρ (refinedOppositeUnipotent F.Carrier B S)
    (firstMap T B S A) (by
      intro u
      apply LinearMap.ext
      intro x
      obtain ⟨v, rfl⟩ := Jacquet.mk_surjective A.ρ
        (B.oppositeUnipotentSubgroup F.Carrier) x
      change firstMap T B S A ((outer T B A).ρ u.val
        (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v)) = _
      rw [outer_mk, outer_half_trivial T B S u, Units.val_one, one_smul,
        firstMap_mk, firstMap_mk]
      exact Jacquet.mk_apply_subgroup A.ρ (composedOppositeUnipotent F.Carrier B S)
        ⟨B.leviEmbedding F.Carrier u.val,
          refinedOppositeUnipotent_map_le_composedOppositeUnipotent F.Carrier B S
            ⟨u.val, u.property, rfl⟩⟩ v)

private theorem forward_mk (v : A) :
    forward T B S A (refinedOppositeJacquetMk B S (outer T B A).ρ
      (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v)) =
        composedOppositeJacquetMk B S A.ρ v := rfl

private def iteratedMk :
    A →ₗ[ℂ] RefinedOppositeJacquetModule B S (outer T B A).ρ :=
  (refinedOppositeJacquetMk B S (outer T B A).ρ).comp
    (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier))

private theorem iteratedMk_invariant (g : composedOppositeUnipotent F.Carrier B S) :
    iteratedMk T B S A ∘ₗ A.ρ g.val = iteratedMk T B S A := by
  ext v
  obtain ⟨hp, hm⟩ :=
    (mem_oppositeLeviPreimage_iff F.Carrier B
      (refinedOppositeUnipotent F.Carrier B S) g.val).mp g.property
  let q : B.oppositeParabolic F.Carrier := ⟨g.val, hp⟩
  let u := B.oppositeUnipotentPart F.Carrier q
  let m : refinedOppositeUnipotent F.Carrier B S :=
    ⟨B.oppositeLeviProjection F.Carrier q, hm⟩
  have hdecomp : u.val.val * B.leviEmbedding F.Carrier m.val = g.val :=
    congrArg Subtype.val ((B.oppositeDecomposition F.Carrier).left_inv q)
  have hout :
      Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) (A.ρ g.val v) =
        Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier)
          (A.ρ (B.leviEmbedding F.Carrier m.val) v) := by
    rw [← hdecomp, map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup A.ρ (B.oppositeUnipotentSubgroup F.Carrier)
      ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩ _
  change refinedOppositeJacquetMk B S (outer T B A).ρ
    (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) (A.ρ g.val v)) = _
  rw [hout]
  have hmact := outer_mk T B A m.val v
  rw [outer_half_trivial T B S m, Units.val_one, one_smul] at hmact
  rw [← hmact]
  exact Jacquet.mk_apply_subgroup (outer T B A).ρ
    (refinedOppositeUnipotent F.Carrier B S) m _

private def backward :
    ComposedOppositeJacquetModule B S A.ρ →ₗ[ℂ]
      RefinedOppositeJacquetModule B S (outer T B A).ρ :=
  Jacquet.lift A.ρ (composedOppositeUnipotent F.Carrier B S)
    (iteratedMk T B S A) (iteratedMk_invariant T B S A)

private theorem backward_mk (v : A) :
    backward T B S A (composedOppositeJacquetMk B S A.ρ v) =
      refinedOppositeJacquetMk B S (outer T B A).ρ
        (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v) := rfl

private def forwardIntertwiner :
    (T.normalizedRefinedOppositeJacquet B S (outer T B A).ρ).IntertwiningMap
      (T.normalizedComposedOppositeJacquet B S A.ρ) where
  toLinearMap := forward T B S A
  isIntertwining' m := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := refinedOppositeJacquetMk_surjective B S (outer T B A).ρ x
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective A.ρ
      (B.oppositeUnipotentSubgroup F.Carrier) y
    change forward T B S A
      (T.normalizedRefinedOppositeJacquet B S (outer T B A).ρ m
        (refinedOppositeJacquetMk B S (outer T B A).ρ
          (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v))) =
      T.normalizedComposedOppositeJacquet B S A.ρ m
        (forward T B S A (refinedOppositeJacquetMk B S (outer T B A).ρ
          (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v)))
    rw [T.normalizedRefinedOppositeJacquet_mk, outer_mk T B A,
      map_smul, map_smul, map_smul, forward_mk, forward_mk,
      T.normalizedComposedOppositeJacquet_mk, T.composedLeviHalfModulus_eq]
    change (T.refinedLeviHalfModulus B S m : ℂ) •
        (T.leviHalfModulus B m.val : ℂ) • _ =
      ((T.leviHalfModulus B m.val : ℂ) *
        (T.refinedLeviHalfModulus B S m : ℂ)) • _
    rw [smul_smul, mul_comm]

private theorem equivalence :
    ∃ E : (T.normalizedRefinedOppositeJacquet B S (outer T B A).ρ).Equiv
        (T.normalizedComposedOppositeJacquet B S A.ρ),
      ∀ v : A,
        E (refinedOppositeJacquetMk B S (outer T B A).ρ
          (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v)) =
            composedOppositeJacquetMk B S A.ρ v := by
  have hgf : Function.LeftInverse (backward T B S A) (forwardIntertwiner T B S A) := by
    intro x
    obtain ⟨y, rfl⟩ := refinedOppositeJacquetMk_surjective B S (outer T B A).ρ x
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective A.ρ
      (B.oppositeUnipotentSubgroup F.Carrier) y
    exact backward_mk T B S A v
  have hfg : Function.RightInverse (backward T B S A) (forwardIntertwiner T B S A) := by
    intro x
    obtain ⟨v, rfl⟩ := composedOppositeJacquetMk_surjective B S A.ρ x
    exact forward_mk T B S A v
  exact ⟨(forwardIntertwiner T B S A).ofBijective ⟨hgf.injective, hfg.surjective⟩,
    forward_mk T B S A⟩

end Langlands.Parabolic.OppositeTransitivity

namespace Langlands.Parabolic

universe uF uV

theorem normalizedOppositeRefinementTransitivity :
    NormalizedOppositeRefinementTransitivityStatement.{uF, uV} := by
  intro p hp F T n B S A
  exact OppositeTransitivity.equivalence T B S A

end Langlands.Parabolic
