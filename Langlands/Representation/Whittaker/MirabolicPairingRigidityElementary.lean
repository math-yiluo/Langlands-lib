import Langlands.Representation.Whittaker.MirabolicPairingStatement
import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Schur.CountableDimensionProof
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.Uniformizer

/-!
# Elementary cases of mirabolic twisted pairing rigidity

For an irreducible representation of the mirabolic group, the radical either
acts trivially or the vectors `ξ u x - x` span the whole space. This module
proves the rank-one case and the cases in which at least one representation has
trivial radical action. Only the case of two radical-generated representations
remains, recorded as `RadicalGeneratedPairingRigidity`.
-/

noncomputable section

namespace Langlands.Whittaker.MirabolicRigidity

open GeneralLinear HarmonicAnalysis RankinSelberg

universe uF uV uW

/-! ### The radical dichotomy -/

section Radical

variable {F : Type uF} [CommRing F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The radical of the mirabolic group acts trivially. -/
def IsRadicalTrivial (ξ : Representation ℂ (mirabolic n F) V) : Prop :=
  ∀ (u : Mirabolic.radical n F) (x : V), ξ (u : mirabolic n F) x = x

/-- The vectors `ξ u x - x`, for `u` in the radical, span the whole space. -/
def IsRadicalGenerated (ξ : Representation ℂ (mirabolic n F) V) : Prop :=
  Submodule.span ℂ (Set.range fun p : Mirabolic.radical n F × V =>
    ξ (p.1 : mirabolic n F) p.2 - p.2) = ⊤

/-- The span of the vectors `ξ u x - x` is a subrepresentation because the radical
is normal. -/
def radicalSpan (ξ : Representation ℂ (mirabolic n F) V) : Subrepresentation ξ where
  toSubmodule := Submodule.span ℂ (Set.range fun p : Mirabolic.radical n F × V =>
    ξ (p.1 : mirabolic n F) p.2 - p.2)
  apply_mem_toSubmodule := by
    intro g x hx
    have hle : Submodule.span ℂ (Set.range fun p : Mirabolic.radical n F × V =>
        ξ (p.1 : mirabolic n F) p.2 - p.2) ≤
        (Submodule.span ℂ (Set.range fun p : Mirabolic.radical n F × V =>
          ξ (p.1 : mirabolic n F) p.2 - p.2)).comap (ξ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨u, y⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have hu : g * (u : mirabolic n F) * g⁻¹ ∈ Mirabolic.radical n F :=
        (inferInstance : (Mirabolic.radical n F).Normal).conj_mem _ u.property g
      refine Submodule.subset_span ⟨(⟨_, hu⟩, ξ g y), ?_⟩
      change ξ (g * (u : mirabolic n F) * g⁻¹) (ξ g y) - ξ g y =
        ξ g (ξ (u : mirabolic n F) y - y)
      rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]
    exact hle hx

/-- An irreducible mirabolic representation is either radical-trivial or
radical-generated. -/
theorem radicalTrivial_or_radicalGenerated (ξ : Representation ℂ (mirabolic n F) V)
    (hirr : ξ.IsIrreducible) : IsRadicalTrivial ξ ∨ IsRadicalGenerated ξ := by
  rcases hirr.eq_bot_or_eq_top (radicalSpan ξ) with h | h
  · left
    intro u x
    have hmem : ξ (u : mirabolic n F) x - x ∈ (radicalSpan ξ).toSubmodule :=
      Submodule.subset_span ⟨(u, x), rfl⟩
    rw [h] at hmem
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem)
  · right
    exact congrArg Subrepresentation.toSubmodule h

/-- If the covariance character is trivial on the radical, a form pairing a
radical-trivial representation with a radical-generated one vanishes. -/
theorem forms_eq_zero_of_trivial_of_generated {χ : mirabolic n F → ℂ}
    {ξ : Representation ℂ (mirabolic n F) V} {ξ' : Representation ℂ (mirabolic n F) W}
    (hχ : ∀ u : Mirabolic.radical n F, χ u = 1)
    (hξ : IsRadicalTrivial ξ) (hξ' : IsRadicalGenerated ξ')
    (β : InvariantBilinear.forms ξ ξ' χ) : β = 0 := by
  apply Subtype.ext
  ext v w
  have hker : Submodule.span ℂ (Set.range fun p : Mirabolic.radical n F × W =>
      ξ' (p.1 : mirabolic n F) p.2 - p.2) ≤ LinearMap.ker (β.val v) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨u, y⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    change β.val v (ξ' (u : mirabolic n F) y - y) = 0
    have h := β.property u v y
    rw [hξ u v, hχ u, one_mul] at h
    rw [map_sub, h, sub_self]
  have hw : β.val v w = 0 := LinearMap.mem_ker.mp (hker (by rw [hξ']; exact Submodule.mem_top))
  simp [hw]

/-- The symmetric mixed case. -/
theorem forms_eq_zero_of_generated_of_trivial {χ : mirabolic n F → ℂ}
    {ξ : Representation ℂ (mirabolic n F) V} {ξ' : Representation ℂ (mirabolic n F) W}
    (hχ : ∀ u : Mirabolic.radical n F, χ u = 1)
    (hξ : IsRadicalGenerated ξ) (hξ' : IsRadicalTrivial ξ')
    (β : InvariantBilinear.forms ξ ξ' χ) : β = 0 := by
  apply Subtype.ext
  ext v w
  have hker : Submodule.span ℂ (Set.range fun p : Mirabolic.radical n F × V =>
      ξ (p.1 : mirabolic n F) p.2 - p.2) ≤ LinearMap.ker (β.val.flip w) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨u, y⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    change β.val (ξ (u : mirabolic n F) y - y) w = 0
    have h := β.property u y w
    rw [hξ' u w, hχ u, one_mul] at h
    rw [map_sub, LinearMap.sub_apply, h, sub_self]
  have hv : β.val.flip w v = 0 := LinearMap.mem_ker.mp (hker (by rw [hξ]; exact Submodule.mem_top))
  simp only [LinearMap.flip_apply] at hv
  simp [hv]

end Radical

/-- The determinant weight is trivial on the radical. -/
theorem determinantWeight_radical {F : Type uF} [Field F] {n : ℕ}
    (abv : AbsoluteValue F ℝ) (u : Mirabolic.radical n F) (s : ℂ) :
    determinantWeight abv (u : mirabolic n F).val s = 1 := by
  have hu : ((u : mirabolic n F) : Langlands.GeneralLinear (n + 1) F) ∈
      GeneralLinear.upperUnipotent (n + 1) F :=
    Mirabolic.radical_le_upperUnipotent u.property
  have h := determinantWeight_unipotent_mul abv ⟨_, hu⟩ 1 s
  rw [mul_one] at h
  rw [show (u : mirabolic n F).val = ((⟨_, hu⟩ : GeneralLinear.upperUnipotent (n + 1) F) :
    Langlands.GeneralLinear (n + 1) F) from rfl, h]
  simp [determinantWeight]

/-! ### Rank one -/

section RankOne

variable {G : Type*} [Group G] [Subsingleton G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

theorem apply_eq_self_of_subsingleton (ρ : Representation ℂ G V) (g : G) (x : V) :
    ρ g x = x := by
  rw [Subsingleton.elim g 1, map_one]
  rfl

/-- Over a trivial group, every linear equivalence is an equivalence of representations. -/
def equivOfSubsingleton (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : V ≃ₗ[ℂ] W) : ρ.Equiv σ :=
  { toLinearMap := e.toLinearMap
    isIntertwining' := fun g => by
      ext x
      simp [apply_eq_self_of_subsingleton]
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible {H : Type*} [Monoid H]
    (ρ : Representation ℂ H V) (hirr : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra! h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext v
  rw [h v]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- An irreducible representation of a trivial group is one-dimensional. -/
theorem nonempty_linearEquiv_of_subsingleton (ρ : Representation ℂ G V)
    (hirr : ρ.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible ρ hirr
  let S : Subrepresentation ρ :=
    { toSubmodule := ℂ ∙ v
      apply_mem_toSubmodule := fun g x hx => by
        rwa [apply_eq_self_of_subsingleton] }
  have hS : S = ⊤ := by
    refine (hirr.eq_bot_or_eq_top S).resolve_left fun h => hv ?_
    have hmem : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hspan : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
  exact ⟨((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans
    (LinearEquiv.ofTop _ hspan)).symm⟩

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]

/-- Evaluation at the identity on the rank-one compact model. -/
def rankOneEval (ψ : UnitaryAdditiveCharacter F) :
    MirabolicCompactFunctions ψ 0 →ₗ[ℂ] ℂ where
  toFun f := mirabolicCompactEval ψ 0 f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The constant function with value `c` on the rank-one mirabolic group. -/
def rankOneConstant (ψ : UnitaryAdditiveCharacter F) (c : ℂ) :
    MirabolicCompactFunctions ψ 0 :=
  Induction.compactFunctionOf (Mirabolic.upperUnipotent 0 F)
    (mirabolicCharacterRepresentation ψ 0) (fun _ => c)
    (fun p x => by simp [mirabolicCharacter_rankOne])
    ⊤ (fun _ _ => rfl)
    (by
      apply Set.Subsingleton.isCompact
      intro a _ b _
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      rw [Subsingleton.elim x y])

theorem rankOneEval_bijective (ψ : UnitaryAdditiveCharacter F) :
    Function.Bijective (rankOneEval ψ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [Subsingleton.elim g 1]
    exact hf
  · intro c
    exact ⟨rankOneConstant ψ c, rfl⟩

/-- Rank one: every irreducible representation is equivalent to the compact model. -/
theorem rankOne_equiv (ψ : UnitaryAdditiveCharacter F)
    (ξ : Representation ℂ (mirabolic 0 F) V) (hirr : ξ.IsIrreducible) :
    Nonempty (ξ.Equiv (mirabolicCompactInduced ψ 0)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_subsingleton ξ hirr
  exact ⟨equivOfSubsingleton _ _
    (e.trans (LinearEquiv.ofBijective (rankOneEval ψ) (rankOneEval_bijective ψ)).symm)⟩

end RankOne

/-! ### Two radical-trivial representations -/

section Spectral

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Schur's lemma for an operator commuting with the whole representation. -/
theorem exists_scalar_of_commute {G : Type*} [Group G] (ρ : Representation ℂ G V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) (hirr : ρ.IsIrreducible) (z : G)
    (hz : ∀ g, ρ (g * z) = ρ (z * g)) : ∃ c : ℂ, ∀ v, ρ z v = c • v := by
  let f : ρ.IntertwiningMap ρ :=
    { toLinearMap := ρ z
      isIntertwining' := fun g => by
        ext v
        change ρ z (ρ g v) = ρ g (ρ z v)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hz] }
  obtain ⟨c, hc, -⟩ := countableDimensionalSchur ρ hrank hirr f
  refine ⟨c, fun v => ?_⟩
  have h := congrArg (fun φ : ρ.IntertwiningMap ρ => φ v) hc
  simpa [f, Representation.IntertwiningMap.smul_apply] using h

/-- Irreducible smooth representations of a separable group have countable dimension. -/
theorem rank_le_aleph0 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace.SeparableSpace G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hirr : ρ.IsIrreducible) : Module.rank ℂ V ≤ Cardinal.aleph0 := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible ρ hirr
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun g => ρ g v)) := by
      rw [span_range_orbit_eq_top hirr hv]
    _ ≤ Cardinal.mk (Set.range fun g => ρ g v) := rank_span_le _
    _ ≤ Cardinal.aleph0 :=
      Cardinal.mk_le_aleph0_iff.mpr (countable_range_orbit (hρ v)).to_subtype

variable {F : Type uF} [Field F] {n : ℕ}

/-- The element `diag(a I_n, 1)` of the mirabolic group. -/
def leviScalar (a : Fˣ) : mirabolic n F :=
  Mirabolic.levi (GeneralLinear.scalar a)

/-- `leviScalar a` is central modulo the radical. -/
theorem leviScalar_commutator_mem (a : Fˣ) (g : mirabolic n F) :
    g * leviScalar a * (leviScalar a * g)⁻¹ ∈ Mirabolic.radical n F := by
  rw [← Mirabolic.ker_projection, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
    leviScalar, Mirabolic.projection_levi,
    ← Matrix.GeneralLinearGroup.scalar_commute a (Mirabolic.projection g), mul_inv_cancel]

/-- On a radical-trivial representation, `leviScalar a` commutes with every operator. -/
theorem apply_mul_leviScalar {ξ : Representation ℂ (mirabolic n F) V}
    (hξ : IsRadicalTrivial ξ) (a : Fˣ) (g : mirabolic n F) :
    ξ (g * leviScalar a) = ξ (leviScalar a * g) := by
  ext x
  have h : ξ (g * leviScalar a * (leviScalar a * g)⁻¹) (ξ (leviScalar a * g) x) =
      ξ (leviScalar a * g) x := hξ ⟨_, leviScalar_commutator_mem a g⟩ _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at h
  exact h

private theorem det_levi (g : Langlands.GeneralLinear n F) :
    Matrix.det (Mirabolic.levi g).val.val = Matrix.det g.val := by
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 0 (1 : Langlands.GeneralLinear 1 F).val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one, Matrix.det_one,
    mul_one]

theorem det_leviScalar (a : Fˣ) :
    Matrix.det (leviScalar (n := n) a).val.val = (a : F) ^ n := by
  rw [leviScalar, det_levi]
  simp [Matrix.det_diagonal]

/-- With `abv a = q⁻¹`, the twisted determinant weight of `leviScalar a` is
`(q^(-s))^(-n)`. -/
theorem determinantWeight_leviScalar (abv : AbsoluteValue F ℝ) (q : ℕ) (hq : 0 < q)
    (a : Fˣ) (ha : abv (a : F) = (q : ℝ) ^ (-1 : ℤ)) (s : ℂ) :
    determinantWeight abv (leviScalar (n := n) a).val (-s) = (spectralPoint q s ^ n)⁻¹ := by
  have hdet : abv (Matrix.det (leviScalar (n := n) a).val.val) = (q : ℝ) ^ (-(n : ℤ)) := by
    rw [det_leviScalar, map_pow, ha, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [determinantWeight_eq_spectralPoint_zpow q hq abv _ n hdet (-s), zpow_natCast]
  have hneg : spectralPoint q (-s) = (spectralPoint q s)⁻¹ := by
    rw [spectralPoint, spectralPoint, neg_neg, Complex.cpow_neg, inv_inv]
  rw [hneg, inv_pow]

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Two radical-trivial irreducible smooth representations admit nonzero twisted
forms only on the finite set of `n`-th roots of `(c c')⁻¹`, where `c` and `c'` are
the Schur scalars of `diag(ϖ I_n, 1)`. -/
theorem exists_finset_of_radicalTrivial [TopologicalSpace.SeparableSpace (mirabolic n F)]
    (hn : 0 < n) (abv : AbsoluteValue F ℝ) (q : ℕ) (hq : 0 < q) (ϖ : Fˣ)
    (hϖ : abv (ϖ : F) = (q : ℝ) ^ (-1 : ℤ))
    {ξ : Representation ℂ (mirabolic n F) V} {ξ' : Representation ℂ (mirabolic n F) W}
    (hs : IsSmooth ξ) (hirr : ξ.IsIrreducible) (hs' : IsSmooth ξ') (hirr' : ξ'.IsIrreducible)
    (ht : IsRadicalTrivial ξ) (ht' : IsRadicalTrivial ξ') :
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
      ∀ β : InvariantBilinear.forms ξ ξ' (fun g => determinantWeight abv g.val (-s)),
        β = 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_scalar_of_commute ξ (rank_le_aleph0 ξ hs hirr) hirr
    (leviScalar ϖ) (apply_mul_leviScalar ht ϖ)
  obtain ⟨c', hc'⟩ := exists_scalar_of_commute ξ' (rank_le_aleph0 ξ' hs' hirr') hirr'
    (leviScalar ϖ) (apply_mul_leviScalar ht' ϖ)
  refine ⟨(Polynomial.nthRoots n ((c * c')⁻¹)).toFinset, fun s hsE β => ?_⟩
  by_contra hβ
  obtain ⟨v, w, hvw⟩ : ∃ v w, β.val v w ≠ 0 := by
    by_contra! h
    exact hβ (Subtype.ext (LinearMap.ext fun v => LinearMap.ext fun w => by simp [h v w]))
  have h : β.val (ξ (leviScalar ϖ) v) (ξ' (leviScalar ϖ) w) =
      determinantWeight abv (leviScalar (n := n) ϖ).val (-s) * β.val v w :=
    β.property _ v w
  rw [hc v, hc' w, determinantWeight_leviScalar abv q hq ϖ hϖ s] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hcc : c * c' = (spectralPoint q s ^ n)⁻¹ :=
    mul_right_cancel₀ hvw (by rw [← h]; ring)
  apply hsE
  rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, hcc, inv_inv]

end Spectral

/-! ### Reduction of the rigidity statement to the radical-generated case -/

/-- The remaining case of `MirabolicTwistedPairingRigidityStatement`: both
representations are radical-generated. -/
def RadicalGeneratedPairingRigidity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ξ : Representation ℂ (mirabolic n F.Carrier) V)
      (ξ' : Representation ℂ (mirabolic n F.Carrier) W),
      IsSmooth ξ → Representation.IsIrreducible ξ →
      IsSmooth ξ' → Representation.IsIrreducible ξ' →
      IsRadicalGenerated ξ → IsRadicalGenerated ξ' →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ β : InvariantBilinear.forms ξ ξ'
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)),
          β ≠ 0 →
            Nonempty (ξ.Equiv (mirabolicCompactInduced ψ n)) ∧
            Nonempty (ξ'.Equiv (mirabolicCompactInduced ψ n))

/-- Rigidity follows from its radical-generated case. -/
theorem mirabolicTwistedPairingRigidity_of_radicalGenerated {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hgen : RadicalGeneratedPairingRigidity.{uF, uV, uW} F T n) :
    MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ ξ ξ' hs hirr hs' hirr'
  cases n with
  | zero =>
    exact ⟨∅, fun _ _ _ _ => ⟨rankOne_equiv ψ ξ hirr, rankOne_equiv ψ ξ' hirr'⟩⟩
  | succ m =>
    have : SecondCountableTopology
        (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) :=
      T.generalLinearSecondCountableTopology (m + 1 + 1)
    have : SecondCountableTopology (mirabolic (m + 1) F.Carrier) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have hχ : ∀ s : ℂ, ∀ u : Mirabolic.radical (m + 1) F.Carrier,
        (fun g : mirabolic (m + 1) F.Carrier =>
          determinantWeight (normalizedAbsoluteValue T) g.val (-s)) u = 1 :=
      fun s u => determinantWeight_radical _ u (-s)
    rcases radicalTrivial_or_radicalGenerated ξ hirr with ht | hg <;>
      rcases radicalTrivial_or_radicalGenerated ξ' hirr' with ht' | hg'
    · obtain ⟨E, hE⟩ := exists_finset_of_radicalTrivial (Nat.succ_pos m)
        (normalizedAbsoluteValue T) T.residueCardinality
        (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)
        (LocalFactor.PadicAbelian.uniformizerUnit T)
        (by rw [normalizedAbsoluteValue_apply, LocalFactor.PadicAbelian.uniformizerUnit_coe]
            exact T.normalizedAbs_uniformizer)
        hs hirr hs' hirr' ht ht'
      exact ⟨E, fun s hsE β hβ => absurd (hE s hsE β) hβ⟩
    · exact ⟨∅, fun s _ β hβ =>
        absurd (forms_eq_zero_of_trivial_of_generated (hχ s) ht hg' β) hβ⟩
    · exact ⟨∅, fun s _ β hβ =>
        absurd (forms_eq_zero_of_generated_of_trivial (hχ s) hg ht' β) hβ⟩
    · exact hgen ψ V W ξ ξ' hs hirr hs' hirr' hg hg'

end Langlands.Whittaker.MirabolicRigidity
