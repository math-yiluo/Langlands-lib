import Langlands.Correspondence.AssemblyRelation
import Langlands.Representation.Classification.MultisegmentConstituentCompatibilityStatement
import Langlands.Weil.Representation.RankDeterminantProof
import Langlands.Representation.Exponents.Chambers
import Langlands.Weil.Local.AssemblyProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof

/-!
# Determinant compatibility of the assembly

Given the multisegment central-character formula
`Classification.MultisegmentConstituentCentralCharacter`, the Henniart assembly of a
supercuspidal map compatible with determinants is compatible with determinants
(`determinantCompatibility_of_assembly`). The determinant of a block sum
`⊕ σ_i ⊗ S_(m_i)` is computed directly from the chosen decomposition.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uM

namespace AssemblyDeterminant

open scoped TensorProduct

section LinearAlgebra

variable {K : Type*} [Field K]

/-- The determinant of a product of endomorphisms over `Fin r` is the product of
the determinants; the factors may have different carriers. -/
theorem det_piMap_fin : ∀ (r : ℕ) (M : Fin r → Type uM) [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [∀ i, Module.Finite K (M i)] (f : ∀ i, Module.End K (M i)),
    LinearMap.det (LinearMap.piMap f) = ∏ i, LinearMap.det (f i)
  | 0, M, _, _, _, f => by
    rw [Fin.prod_univ_zero]
    exact LinearMap.det_eq_one_of_subsingleton _
  | r + 1, M, _, _, _, f => by
    let e := Fin.consLinearEquiv K M
    have h : LinearMap.piMap f =
        (e : _ →ₗ[K] _) ∘ₗ LinearMap.prodMap (f 0) (LinearMap.piMap fun i : Fin r => f i.succ) ∘ₗ
          (e.symm : _ →ₗ[K] _) := by
      apply LinearMap.ext
      intro x
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e]
      · simp [e, Fin.tail]
    rw [h, LinearMap.det_conj, LinearMap.det_prodMap, det_piMap_fin r, Fin.prod_univ_succ]

/-- The determinant of a componentwise endomorphism of a direct sum over `Fin r`. -/
theorem det_directSum_lmap {r : ℕ} (M : Fin r → Type uM) [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [∀ i, Module.Finite K (M i)] (f : ∀ i, Module.End K (M i)) :
    LinearMap.det (DirectSum.lmap f) = ∏ i, LinearMap.det (f i) := by
  let e := DirectSum.linearEquivFunOnFintype K (Fin r) M
  have h : (e : _ →ₗ[K] _) ∘ₗ DirectSum.lmap f ∘ₗ (e.symm : _ →ₗ[K] _) =
      LinearMap.piMap f := by
    apply LinearMap.ext
    intro x
    funext i
    have hx : ((e.symm x : DirectSum (Fin r) M) : ∀ i, M i) i = x i :=
      congrFun (e.apply_symm_apply x) i
    simp [e, hx]
  rw [← LinearMap.det_conj (DirectSum.lmap f) e, h, det_piMap_fin]

variable {G : Type*} [Group G]

/-- The weights `1, ν, …, ν^(m-1)` of the special block multiply to its determinant. -/
theorem det_special_action (ν : G →* Kˣ) (m : ℕ) (g : G) :
    LinearMap.det (WeilDeligneRepresentation.Special.action ν m g) =
      ∏ j : Fin m, (ν g : K) ^ (j : ℕ) := by
  rw [← LinearMap.det_toMatrix']
  have h : LinearMap.toMatrix' (WeilDeligneRepresentation.Special.action ν m g) =
      Matrix.diagonal fun j : Fin m => (ν g : K) ^ (j : ℕ) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, WeilDeligneRepresentation.Special.action_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [h, Matrix.det_diagonal]

/-- The determinant of an uncentered block `A ⊗ S_m`. -/
theorem det_block_apply (ν : G →* Kˣ) (A : FiniteRepresentation K G) (m : ℕ) (g : G) :
    LinearMap.det ((WeilDeligneRepresentation.block ν A m).representation g) =
      LinearMap.det (A.representation g) ^ m *
        (∏ j : Fin m, (ν g : K) ^ (j : ℕ)) ^ A.rank := by
  change LinearMap.det (TensorProduct.map (A.representation g)
    (WeilDeligneRepresentation.Special.action ν m g)) = _
  rw [Langlands.det_tensorProduct_map, Module.finrank_fin_fun, det_special_action]
  rfl

/-- The determinant of a direct sum of uncentered blocks `⊕_i A_i ⊗ S_(m_i)`. -/
theorem det_directSum_block_apply {r : ℕ} (ν : G →* Kˣ) (A : Fin r → FiniteRepresentation K G)
    (m : Fin r → ℕ) (g : G) :
    LinearMap.det ((WeilDeligneRepresentation.directSum fun i =>
        WeilDeligneRepresentation.block ν (A i) (m i)).representation g) =
      ∏ i, LinearMap.det ((A i).representation g) ^ m i *
        (∏ j : Fin (m i), (ν g : K) ^ (j : ℕ)) ^ (A i).rank := by
  exact (det_directSum_lmap _ fun i =>
      (WeilDeligneRepresentation.block ν (A i) (m i)).representation g).trans
    (Finset.prod_congr rfl fun i _ => det_block_apply ν (A i) (m i) g)

end LinearAlgebra


section Main

open PadicField.TopologicalData
open scoped NNReal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyDeterminantFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyDeterminantGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

omit [Fact p.Prime] in
/-- A scalar action transfers along an equivalence of representations. -/
theorem smul_of_equiv {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (φ : ρ.Equiv τ) {g : G} {z : ℂ} (h : ∀ v, ρ g v = z • v) (w : W) : τ g w = z • w := by
  have hw := Representation.IntertwiningMap.isIntertwining ρ τ φ.toIntertwiningMap g (φ.symm w)
  rw [Representation.Equiv.coe_toIntertwiningMap, h, map_smul, φ.apply_symm_apply] at hw
  exact hw.symm

omit [Fact p.Prime] in
/-- A scalar `z` acting on a nonzero vector as the identity is `1`. -/
theorem eq_one_of_smul_eq {V : Type*} [AddCommGroup V] [Module ℂ V] {v : V} (hv : v ≠ 0)
    {z : ℂ} (h : v = z • v) : z = 1 := by
  have h0 : (z - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hv)

omit [Fact p.Prime] in
/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra! h
  have := hρ
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext v
  rw [h v]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- A central action on a class is the central action on each of its representatives. -/
theorem centralActsBy_apply {n : ℕ+} {π : AutomorphicClass.{uF, uA} F n} {a : F.Carrierˣ}
    {z : ℂˣ} (h : CentralActsBy F π a z) (A : AutomorphicObject.{uF, uA} F n)
    (hA : automorphicClassOf F A = π) (v : A.obj) :
    A.obj.representation (GeneralLinear.scalar a) v = (z : ℂ) • v := by
  obtain ⟨A', hA', hact⟩ := h
  obtain ⟨φ⟩ := (automorphicClassOf_eq_iff F A' A).1 (hA'.trans hA.symm)
  exact smul_of_equiv φ hact v

/-- The reciprocity homomorphism is surjective. -/
theorem reciprocityHom_surjective (e : ReciprocityCandidate F) :
    Function.Surjective (reciprocityHom F e) := by
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm z)
  refine ⟨x, ?_⟩
  change e (QuotientGroup.mk x) = z
  rw [hx]
  exact e.apply_symm_apply z

/-- Under geometric reciprocity, the normalized absolute value of `rec w` is the norm
character at `w`. -/
theorem normalizedAbs_reciprocityHom (e : ReciprocityCandidate F)
    (he : IsGeometricReciprocity F e) (w : Weil.Local.localWeilGroup F) :
    ((((F.canonicalTopologicalData.normalizedAbsUnits (reciprocityHom F e w) : ℝ≥0) : ℝ)) :
        ℂ) = (Weil.Local.localNormCharacter F w : ℂ) := by
  have h := DFunLike.congr_fun he.1
    (LocalClassField.WeilQuotients.projection (Weil.Local.localResidueDegree F) w)
  have hord : F.canonicalTopologicalData.ord (reciprocityHom F e w : F.Carrier) =
      Weil.Local.localDegreeInt F w :=
    congrArg Multiplicative.toAdd h
  rw [normalizedAbsUnits_coe, normalizedAbs_eq_zpow_logAbs, Weil.Local.localNormCharacter_apply,
    logAbs, hord]
  push_cast
  rfl

/-- On `rec w`, the determinant power of a segment of length `m + 1` with base of rank
`d + 1` is the product of the special-block weights at `w`. -/
theorem determinantPowerCharacter_reciprocityHom (e : ReciprocityCandidate F)
    (he : IsGeometricReciprocity F e) (w : Weil.Local.localWeilGroup F) (d m : ℕ) :
    (F.canonicalTopologicalData.determinantPowerCharacter ((m + 1) * (d + 1))
        ((((m + 1 : ℕ) : ℝ) - 1) / 2) (GeneralLinear.scalar (reciprocityHom F e w)) : ℂ) =
      (∏ j : Fin (m + 1), (Weil.Local.localNormCharacter F w : ℂ) ^ (j : ℕ)) ^ (d + 1) := by
  set S := ∑ j ∈ Finset.range (m + 1), j with hSdef
  have hS : (S : ℝ) * 2 = ((m : ℝ) + 1) * m := by
    have h2 := Finset.sum_range_id_mul_two (m + 1)
    rw [Nat.add_sub_cancel] at h2
    rw [hSdef]
    exact_mod_cast h2
  have hexp : (((m + 1) * (d + 1) : ℕ) : ℝ) * ((((m + 1 : ℕ) : ℝ) - 1) / 2) =
      ((S * (d + 1) : ℕ) : ℝ) := by
    push_cast
    linear_combination (-((d : ℝ) + 1) / 2) * hS
  rw [coe_determinantPowerCharacter_scalar, hexp, Real.rpow_natCast, Complex.ofReal_pow,
    normalizedAbs_reciprocityHom F e he w, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j => j) (m + 1), ← hSdef, pow_mul]

/-- The character `a ↦ ω(a)^m · |det(a · 1)|^((m-1)/2)` of `Fˣ`, where `m` is the length
of the segment `Δ` and `a · 1` is the scalar matrix in `GL_(deg Δ)`. It is the factor `ωΔ`
of `Classification.MultisegmentConstituentCentralCharacter`: the central character of `Δ`
when its base has central character `ω`. -/
def segmentCentralCharacter (Δ : F.canonicalTopologicalData.Segment.{uA, uF})
    (ω : F.Carrierˣ →* ℂˣ) : F.Carrierˣ →* ℂˣ :=
  ω ^ Δ.length *
    (F.canonicalTopologicalData.determinantPowerCharacter Δ.degree
      (((Δ.length : ℝ) - 1) / 2)).comp GeneralLinear.scalar

/-- On `rec w`, the central character of the segment `[c0 σ, ν^m c0 σ]` built from a
character `ω` of `Fˣ`. -/
theorem segmentCentralCharacter_reciprocityHom (c0 : SupercuspidalMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (he : IsGeometricReciprocity F e) {d : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat) (m : ℕ) (ω : F.Carrierˣ →* ℂˣ)
    (w : Weil.Local.localWeilGroup F) :
    ((segmentCentralCharacter F (segmentOf F c0 σ m) ω (reciprocityHom F e w) : ℂˣ) : ℂ) =
      (ω (reciprocityHom F e w) : ℂ) ^ (m + 1) *
        (∏ j : Fin (m + 1), (Weil.Local.localNormCharacter F w : ℂ) ^ (j : ℕ)) ^ (d + 1) := by
  rw [segmentCentralCharacter, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply,
    Units.val_mul, Units.val_pow_eq_pow_val]
  exact congrArg _ (determinantPowerCharacter_reciprocityHom F e he w d m)

/-- The determinant of a parameter class is the determinant character of any
representative. -/
theorem parameterDeterminant_eq {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n)
    (A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F)
    (hA : WeilDeligneRepresentation.classOf A = parameterForget F D) :
    parameterDeterminant F D =
      FiniteRepresentation.determinantCharacter A.toFiniteRepresentation := by
  obtain ⟨c, hc⟩ := D
  induction c using Quotient.inductionOn with
  | h A' =>
    obtain ⟨e⟩ := (WeilDeligneRepresentation.classOf_eq_iff A A'.val).1 hA
    exact (FiniteRepresentation.determinantCharacter_eq e.representationEquiv).symm

/-- The determinant of an irreducible Weil class is the determinant character of any
representative. -/
theorem irreducibleWeilDeterminant_eq {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n)
    (B : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hB : FiniteRepresentation.classOf B = weilClassForget F σ) :
    irreducibleWeilDeterminant F σ = FiniteRepresentation.determinantCharacter B := by
  unfold irreducibleWeilDeterminant
  rw [← hB]
  rfl

/-- A representative of an irreducible Weil class of rank `n` has rank `n`. -/
theorem rank_eq_of_classOf_eq {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n)
    (B : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hB : FiniteRepresentation.classOf B = weilClassForget F σ) : B.rank = n := by
  have h : FiniteRepresentation.classRank (weilClassForget F σ) = n := σ.property
  rw [← hB, FiniteRepresentation.classRank_classOf] at h
  exact h

/-- Under supercuspidal determinant compatibility, the determinant of `σ` factors
through reciprocity. -/
theorem exists_centralCharacter (c0 : SupercuspidalMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hdet : SupercuspidalDeterminantCompatibility F e c0)
    {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n) :
    ∃ ω : F.Carrierˣ →* ℂˣ,
      ∀ w, ω (reciprocityHom F e w) = irreducibleWeilDeterminant F σ w := by
  have hker : (reciprocityHom F e).ker ≤ (irreducibleWeilDeterminant F σ).ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    obtain ⟨A, -, hact⟩ := hdet n σ w
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible A.property.1
    have h := hact v
    rw [hw, map_one, map_one, Module.End.one_apply] at h
    exact Units.ext (eq_one_of_smul_eq hv h)
  exact ⟨(reciprocityHom F e).liftOfSurjective (reciprocityHom_surjective F e) ⟨_, hker⟩,
    fun w => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ w⟩

/-- A supercuspidal representative of `c0 σ` has central character `ω` when
`ω ∘ rec` is the determinant of `σ`. -/
theorem hasScalarCharacter_of_isoClass (c0 : SupercuspidalMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hdet : SupercuspidalDeterminantCompatibility F e c0)
    {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n) (ω : F.Carrierˣ →* ℂˣ)
    (hω : ∀ w, ω (reciprocityHom F e w) = irreducibleWeilDeterminant F σ w)
    (A : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := (n : ℕ)))
    (hA : A.isoClass = c0 n σ) :
    Classification.HasScalarCharacter A.obj.representation GeneralLinear.scalar ω := by
  intro a v
  obtain ⟨w, rfl⟩ := reciprocityHom_surjective F e a
  rw [hω]
  refine centralActsBy_apply F (hdet n σ w) A.toIrreducibleAdmissible ?_ v
  rw [← hA]
  rfl

/-- **Determinant compatibility of the assembly.** Given the multisegment central
character formula, the assembly of a supercuspidal map compatible with determinants
is compatible with determinants. -/
theorem determinantCompatibility_of_assembly
    (hcc : Classification.MultisegmentConstituentCentralCharacter.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hc : IsAssemblyOf F c0 c) (he : IsGeometricReciprocity F e)
    (hdet : SupercuspidalDeterminantCompatibility F e c0) : DeterminantCompatibility F e c := by
  intro n D w
  obtain ⟨r, d, m, σ, ⟨B, A, hB, hA, ⟨φ⟩⟩, ⟨A0, J, hA0, hJ, ⟨ψ⟩⟩⟩ := hc n D
  choose ω hω using fun i => exists_centralCharacter F c0 e hdet (σ i)
  have hex : ∀ i, ∃ R : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier)
      (n := (segmentOf F c0 (σ i) (m i)).rank), R.isoClass = c0 (d i).succPNat (σ i) :=
    fun i => Quotient.exists_rep (c0 (d i).succPNat (σ i) : Quotient _)
  choose R hR using hex
  have hscalar : ∀ i, Classification.HasScalarCharacter (R i).obj.representation
      GeneralLinear.scalar (ω i) := fun i =>
    hasScalarCharacter_of_isoClass F c0 e hdet (σ i) (ω i) (hω i) (R i) (hR i)
  have hJc := hcc r (fun i => segmentOf F c0 (σ i) (m i)) R ω hR hscalar (n : ℕ) n.pos J
    (Or.inr hJ)
  refine ⟨A0, hA0, fun v => ?_⟩
  rw [smul_of_equiv ψ (hJc (reciprocityHom F e w)) v]
  congr 1
  rw [parameterDeterminant_eq F D A hA,
    ← FiniteRepresentation.determinantCharacter_eq φ.representationEquiv,
    FiniteRepresentation.determinantCharacter_apply, det_directSum_block_apply,
    MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ =>
    (segmentCentralCharacter_reciprocityHom F c0 e he (σ i) (m i) (ω i) w).trans ?_
  rw [hω i w,
    irreducibleWeilDeterminant_eq F (σ i) (B i) (hB i),
    FiniteRepresentation.determinantCharacter_apply, rank_eq_of_classOf_eq F (σ i) (B i) (hB i)]
  rfl

end Main

end AssemblyDeterminant

end Langlands.Correspondence
