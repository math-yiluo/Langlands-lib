import Langlands.BaseChange.TwistedInducedCharacterFormulaStatement

/-! # The ordinary induced character formula from the twisted one in degree one

The case `E = F`, `σ = 1`, `l = 1` of `TwistedInducedCharacterFormulaStatement`, with the
identity intertwiners, is `InducedCharacterFormulaStatement`. The twisted formula is a premise
here, not a theorem of this module. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands

universe u uV uW

/-- The identity intertwiner of a representation of `GL_n(F)` with its pullback along the
entrywise action of `σ = 1`. -/
def oneSigmaIntertwiner {F : Type u} [CommRing F] (n : ℕ) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GeneralLinear n F) V) :
    SigmaIntertwiner (1 : F ≃ₐ[F] F) n π :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => by
    ext v
    simp [entrywiseAut_one_apply])

@[simp]
theorem oneSigmaIntertwiner_toLinearMap {F : Type u} [CommRing F] (n : ℕ) {V : Type uV}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GeneralLinear n F) V) :
    (oneSigmaIntertwiner n π).toLinearMap = LinearMap.id :=
  rfl

/-- The tensor product of the identity intertwiners of the blocks is the identity. -/
theorem leviTensorIntertwiner_one_toLinearMap {F : Type u} [CommRing F] {n : ℕ}
    (B : BlockShape n) {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] (P : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)) :
    (leviTensorIntertwiner (1 : F ≃ₐ[F] F) B
        (fun i => oneSigmaIntertwiner (B.size i) (P i))).toLinearMap = 1 :=
  PiTensorProduct.map_id

/-- The induced intertwiner `ι(A)` of the identity intertwiners, for `σ = 1`, is the
identity of the normalized product induction. -/
theorem inducedSigmaIntertwiner_one_toLinearMap {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ} (B : BlockShape n)
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (P : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)) :
    (inducedSigmaIntertwiner (1 : F ≃ₐ[F] F) B
        (fun i => oneSigmaIntertwiner (B.size i) (P i))).toLinearMap = 1 := by
  apply LinearMap.ext
  intro ξ
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : entrywiseAut (1 : F ≃ₐ[F] F).symm n x = x := by
    ext i j
    rfl
  have hT : (leviTensorIntertwiner (1 : F ≃ₐ[F] F) B
      (fun i => oneSigmaIntertwiner (B.size i) (P i))).toLinearEquiv =
        LinearEquiv.refl ℂ _ := by
    apply LinearEquiv.toLinearMap_injective
    exact leviTensorIntertwiner_one_toLinearMap B P
  change (leviTensorIntertwiner (1 : F ≃ₐ[F] F) B
      (fun i => oneSigmaIntertwiner (B.size i) (P i))).toLinearEquiv
        (Induction.eval (B.parabolic F) _ ξ (entrywiseAut (1 : F ≃ₐ[F] F).symm n x)) =
    Induction.eval (B.parabolic F) _ ξ x
  rw [hx, hT]
  rfl

/-- The degree-one twisted formula implies the ordinary formula. -/
def InducedCharacterFormulaFromTwistedStatement : Prop :=
  TwistedInducedCharacterFormulaStatement.{u, u, uV} → InducedCharacterFormulaStatement.{u, uV}

/-- Apply the twisted formula with `E = F`, `σ = 1`, `l = 1`, `δ = γ`, `d = m` and the
identity intertwiners, whose tensor product and induced intertwiner are identities. -/
theorem inducedCharacterFormula_of_twisted :
    InducedCharacterFormulaFromTwistedStatement.{u, uV} := by
  intro h F _ _ _ _ n hn B V _ _ π hπ hirr γ hγ k m hm a ha
  have : ∀ i, T2Space (GeneralLinear (B.size i) F) := fun i =>
    LocalFieldTopology.generalLinear_t2Space F (B.size i)
  have : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) F) := fun i =>
    LocalFieldTopology.generalLinear_locallyCompactSpace F (B.size i)
  have : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) F) := fun i =>
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (B.size i)
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have hbase : ∀ {r : ℕ} (g : GeneralLinear r F), baseChange F F r g = g := fun g => by
    apply Units.ext
    ext i j
    simp [baseChange_apply_apply]
  have hnorm1 : ∀ {r : ℕ} (g : GeneralLinear r F), cyclicNorm (1 : F ≃ₐ[F] F) 1 g = g :=
    fun g => by
      rw [cyclicNorm_succ, cyclicNorm_zero, pow_zero, entrywiseAut_one_apply, one_mul]
  have hnorm : IsNormAssociated (1 : F ≃ₐ[F] F) 1 γ γ :=
    ⟨1, by rw [inv_one, one_mul, mul_one, hnorm1, hbase]⟩
  have hd : ∀ j, (∃ x : GeneralLinear n F,
      x⁻¹ * γ * entrywiseAut (1 : F ≃ₐ[F] F) n x = B.leviEmbedding F (m j)) ∧
      ∀ i, cyclicNorm (1 : F ≃ₐ[F] F) 1 (m j i) = baseChange F F (B.size i) (m j i) := by
    intro j
    refine ⟨?_, fun i => by rw [hnorm1, hbase]⟩
    obtain ⟨x, hx⟩ := hm.1 j
    exact ⟨x, by rw [entrywiseAut_one_apply, hx]⟩
  have hb : ∀ j,
      HasTwistedCharacterValue (B.blockTensor π) (FiniteTensor.isAdmissible_external π hπ)
        (leviTensorIntertwiner (1 : F ≃ₐ[F] F) B
          (fun i => oneSigmaIntertwiner (B.size i) (π i))).toLinearMap (m j) (a j) := by
    intro j
    rw [leviTensorIntertwiner_one_toLinearMap]
    exact (hasTwistedCharacterValue_one_iff _ _ _ _).2 (ha j)
  have hT := h F F (1 : F ≃ₐ[F] F) 1 n isCyclicAlgebra_one hn B V π hπ
    (fun i => oneSigmaIntertwiner (B.size i) (π i)) hirr γ γ hnorm hγ k m hm m hd a hb
  rw [inducedSigmaIntertwiner_one_toLinearMap] at hT
  exact (hasTwistedCharacterValue_one_iff _ _ _ _).1 hT

end Langlands.BaseChange
