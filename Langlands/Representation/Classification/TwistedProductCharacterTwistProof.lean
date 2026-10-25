import Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.Induction.CharacterTwistProof

noncomputable section

open scoped BigOperators

namespace Langlands.Classification

open GeneralLinear

universe uF uV

private theorem determinant_parabolic {R : Type uF} [CommRing R]
    {n : ℕ} (B : BlockShape n) (g : B.parabolic R) :
    determinant g.val = ∏ i, determinant (B.leviProjection R g i) := by
  let M : Matrix B.Index B.Index R := g.val.val.submatrix B.indexEquiv B.indexEquiv
  have hM : M.BlockTriangular Sigma.fst := g.property
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_submatrix_equiv_self B.indexEquiv]
  change M.det = _
  rw [hM.det_fintype, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  let e : Fin (B.size i) ≃ {a : B.Index // a.1 = i} :=
    Equiv.ofBijective (fun a => ⟨⟨i, a⟩, rfl⟩) (by
      constructor
      · intro a b h
        exact Sigma.mk.inj_iff.mp (congrArg Subtype.val h) |>.2 |> eq_of_heq
      · rintro ⟨⟨j, a⟩, h⟩
        dsimp only at h
        subst j
        exact ⟨a, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

private theorem determinant_leviEmbedding {R : Type uF} [CommRing R]
    {n : ℕ} (B : BlockShape n) (m : B.Levi R) :
    determinant (B.leviEmbedding R m) = ∏ i, determinant (m i) := by
  simpa only [BlockShape.leviInParabolic_val, BlockShape.leviProjection_section] using
    determinant_parabolic B (B.leviInParabolic R m)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem blockTensor_determinant_twist {n : ℕ} (B : BlockShape n)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i)) =
      twist ((χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F.Carrier))
        (B.blockTensor σ) := by
  let := T.topology
  let χL : Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
    ⟨(χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F.Carrier),
      χ.isOpen_ker.preimage ((T.generalLinearDeterminant n).continuous.comp
        (T.blockLeviEmbedding B).continuous)⟩
  have hcoord (i : Fin B.length) :
      (χL.coordinate i).toMonoidHom = χ.toMonoidHom.comp
        (determinant : GeneralLinear (B.size i) F.Carrier →* F.Carrierˣ) := by
    apply MonoidHom.ext
    intro g
    change χ.toMonoidHom (determinant (B.leviEmbedding F.Carrier (Pi.mulSingle i g))) =
      χ.toMonoidHom (determinant g)
    rw [determinant_leviEmbedding]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.mulSingle_eq_of_ne hji]
    · simp
  simpa only [hcoord] using χL.external_coordinate_twist σ

/-- Common smooth determinant characters commute with normalized block products. -/
theorem twistedProductCharacterTwist :
    TwistedProductCharacterTwistClause.{uF,uV} F T := by
  let := T.topology
  intro n _ B χ
  dsimp only
  intro δ s
  let := T.generalLinearTopologicalGroup n
  let σ := fun i => (T.segmentFactor (δ i) (s i)).representation
  let χn : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) :=
    ⟨χ.toMonoidHom.comp determinant,
      χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous⟩
  let ρ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
  have hρ : IsSmooth ρ := by
    apply (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
    apply isSmooth_comp _ (T.blockLeviProjection B).continuous
    exact FiniteTensor.isSmooth_external σ (fun i => (T.segmentFactor (δ i) (s i)).isSmooth)
  obtain ⟨e, _⟩ := (Induction.inductionTwist (B.parabolic F.Carrier) χn ρ hρ).1
  let δχ := fun i => (δ i).twist (χ.toMonoidHom.comp determinant)
    (χ.isOpen_ker.preimage (T.generalLinearDeterminant (B.size i)).continuous)
  let τ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor (fun i => (T.segmentFactor (δχ i) (s i)).representation)).comp
      (B.leviProjection F.Carrier))
  have hblock (i : Fin B.length) :
      (T.segmentFactor (δχ i) (s i)).representation =
        twist (χ.toMonoidHom.comp determinant) (σ i) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change (T.determinantPowerCharacter (B.size i) (s i) g : ℂ) •
        ((χ.toMonoidHom (determinant g) : ℂ) • (δ i).representation g v) =
      (χ.toMonoidHom (determinant g) : ℂ) •
        ((T.determinantPowerCharacter (B.size i) (s i) g : ℂ) •
          (δ i).representation g v)
    exact smul_comm _ _ _
  have hτ : twist (χn.toMonoidHom.comp (B.parabolic F.Carrier).subtype) ρ = τ := by
    dsimp only [τ]
    simp_rw [hblock]
    rw [blockTensor_determinant_twist F T B χ σ]
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change (χ.toMonoidHom (determinant g.val) : ℂ) •
        ((T.parabolicHalfModulus B g : ℂ) • B.blockTensor σ (B.leviProjection F.Carrier g) v) =
      (T.parabolicHalfModulus B g : ℂ) •
        ((χ.toMonoidHom (determinant
          (B.leviEmbedding F.Carrier (B.leviProjection F.Carrier g))) : ℂ) •
            B.blockTensor σ (B.leviProjection F.Carrier g) v)
    rw [determinant_parabolic, determinant_leviEmbedding]
    exact smul_comm _ _ _
  exact ⟨e.trans (Induction.smoothInducedEquiv _ (equivOfRepresentationEq hτ))⟩

end Langlands.Classification
