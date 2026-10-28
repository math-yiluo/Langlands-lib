import Langlands.Representation.Whittaker.MirabolicPairingStatement
import Langlands.Representation.Whittaker.MirabolicMinimalityProof
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.Representation.Schur.CountableDimensionProof
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.Padic
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.CanonicalProof

/-!
# Functional multiplicity for irreducible mirabolic representations

JPSS (1983), Section 1.5, Corollary 1: for the mirabolic group over a p-adic field,
the character-functional space of a smooth irreducible complex representation is at
most a line, and it is a line exactly when the representation is equivalent to the
compact standard model. The proof combines the Frobenius coefficient map with
compact minimality (BZ76, Proposition 5.15(c)) and countable-dimensional Schur.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

section Generic

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ξ : Representation ℂ (mirabolic n F) V}

/-- Frobenius reciprocity before taking smooth vectors: a character functional
gives the coefficient map into all covariant functions. -/
def mirabolicFrobeniusAlgebraic
    (ℓ : functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ) :
    ξ.IntertwiningMap (Induction.equivariantAction (Mirabolic.upperUnipotent n F)
      (mirabolicCharacterRepresentation ψ n)) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => ℓ.val (ξ g v), by
        intro u g
        change ℓ.val (ξ ((u : mirabolic n F) * g) v) =
          (mirabolicCharacter ψ n u : ℂ) * ℓ.val (ξ g v)
        rw [map_mul, Module.End.mul_apply]
        exact ℓ.property u (ξ g v)⟩
      map_add' := by intro v w; apply Subtype.ext; funext g; simp
      map_smul' := by intro a v; apply Subtype.ext; funext g; simp }
  isIntertwining' s := by
    ext v g
    change ℓ.val (ξ g (ξ s v)) = ℓ.val (ξ (g * s) v)
    rw [map_mul, Module.End.mul_apply]

/-- The coefficient map of a smooth representation lands in smooth induction. -/
def mirabolicFrobeniusMap (hξ : IsSmooth ξ)
    (ℓ : functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ) :
    ξ.IntertwiningMap (mirabolicSmoothInduced ψ n) :=
  smoothLift hξ (mirabolicFrobeniusAlgebraic ψ ℓ)

@[simp] theorem mirabolicFrobeniusMap_eval (hξ : IsSmooth ξ)
    (ℓ : functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ)
    (v : V) (g : mirabolic n F) :
    mirabolicEval ψ n (mirabolicFrobeniusMap ψ hξ ℓ v) g = ℓ.val (ξ g v) := rfl

theorem mirabolicFrobeniusMap_eval_one (hξ : IsSmooth ξ)
    (ℓ : functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ) (v : V) :
    mirabolicEval ψ n (mirabolicFrobeniusMap ψ hξ ℓ v) 1 = ℓ.val v := by
  rw [mirabolicFrobeniusMap_eval, map_one, Module.End.one_apply]

/-- A nonzero functional has a nonzero coefficient image. -/
theorem mirabolicFrobeniusMap_range_ne_bot (hξ : IsSmooth ξ)
    (ℓ : functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ)
    (hℓ : ℓ ≠ 0) : (mirabolicFrobeniusMap ψ hξ ℓ).range ≠ ⊥ := by
  intro h
  apply hℓ
  apply Subtype.ext
  ext v
  change ℓ.val v = 0
  have hv : mirabolicFrobeniusMap ψ hξ ℓ v ∈ (mirabolicFrobeniusMap ψ hξ ℓ).range :=
    ⟨v, rfl⟩
  rw [h] at hv
  have hz : mirabolicFrobeniusMap ψ hξ ℓ v = 0 := hv
  rw [← mirabolicFrobeniusMap_eval_one ψ hξ ℓ v, hz]
  rfl

/-- The preimage of the compact-support subrepresentation under an intertwiner. -/
def mirabolicCompactPreimage (A : ξ.IntertwiningMap (mirabolicSmoothInduced ψ n)) :
    Subrepresentation ξ where
  toSubmodule := (mirabolicCompactSubrepresentation ψ n).toSubmodule.comap A.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change A (ξ g v) ∈ mirabolicCompactSubrepresentation ψ n
    rw [A.isIntertwining]
    exact (mirabolicCompactSubrepresentation ψ n).apply_mem_toSubmodule g hv

/-- Under compact minimality, the image of an irreducible representation with
nonzero image is exactly the compact-support subrepresentation. -/
theorem range_eq_mirabolicCompact [Representation.IsIrreducible ξ]
    (hmin : ∀ W : Subrepresentation (mirabolicSmoothInduced ψ n), W ≠ ⊥ →
      mirabolicCompactSubrepresentation ψ n ≤ W)
    (hne : ∃ f : MirabolicCompactFunctions ψ n, f ≠ 0)
    (A : ξ.IntertwiningMap (mirabolicSmoothInduced ψ n)) (hA : A.range ≠ ⊥) :
    A.range = mirabolicCompactSubrepresentation ψ n := by
  have hle := hmin _ hA
  obtain ⟨f, hf⟩ := hne
  obtain ⟨v, hv⟩ := hle (show f.val ∈ mirabolicCompactSubrepresentation ψ n from f.property)
  replace hv : A v = f.val := hv
  have hQ : mirabolicCompactPreimage ψ A ≠ ⊥ := by
    intro h
    have hmem : v ∈ mirabolicCompactPreimage ψ A := by
      change A v ∈ mirabolicCompactSubrepresentation ψ n
      rw [hv]
      exact f.property
    rw [h] at hmem
    have hv0 : v = 0 := hmem
    apply hf
    apply Subtype.ext
    rw [← hv, hv0, map_zero]
    rfl
  have htop := (IsSimpleOrder.eq_bot_or_eq_top (mirabolicCompactPreimage ψ A)).resolve_left hQ
  refine le_antisymm ?_ hle
  rintro _ ⟨w, rfl⟩
  have hw : w ∈ mirabolicCompactPreimage ψ A := by
    rw [htop]
    trivial
  exact hw

/-- Corestriction of an intertwiner whose values have compact support. -/
def mirabolicCompactCorestrict (A : ξ.IntertwiningMap (mirabolicSmoothInduced ψ n))
    (hA : ∀ v, A v ∈ mirabolicCompactSubrepresentation ψ n) :
    ξ.IntertwiningMap (mirabolicCompactInduced ψ n) where
  toLinearMap := A.toLinearMap.codRestrict
    (mirabolicCompactSubrepresentation ψ n).toSubmodule hA
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    exact LinearMap.congr_fun (A.isIntertwining' g) v

@[simp] theorem mirabolicCompactCorestrict_val
    (A : ξ.IntertwiningMap (mirabolicSmoothInduced ψ n))
    (hA : ∀ v, A v ∈ mirabolicCompactSubrepresentation ψ n) (v : V) :
    (mirabolicCompactCorestrict ψ A hA v).val = A v := rfl

/-- A nonzero intertwiner from an irreducible representation onto the compact
subrepresentation gives an equivalence with the compact model. -/
def mirabolicCompactEquivOfRange [Representation.IsIrreducible ξ]
    (A : ξ.IntertwiningMap (mirabolicSmoothInduced ψ n))
    (hA : A.range = mirabolicCompactSubrepresentation ψ n) (hA0 : A ≠ 0) :
    ξ.Equiv (mirabolicCompactInduced ψ n) :=
  have hmem : ∀ v, A v ∈ mirabolicCompactSubrepresentation ψ n := fun v => by
    rw [← hA]
    exact ⟨v, rfl⟩
  (mirabolicCompactCorestrict ψ A hmem).ofBijective
    ⟨fun v w h => (Representation.IsIrreducible.injective_or_eq_zero A).resolve_right hA0
        (congrArg Subtype.val h),
      fun f => by
        obtain ⟨v, hv⟩ := (show f.val ∈ A.range by rw [hA]; exact f.property)
        exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem mirabolicCompactEquivOfRange_val [Representation.IsIrreducible ξ]
    (A : ξ.IntertwiningMap (mirabolicSmoothInduced ψ n))
    (hA : A.range = mirabolicCompactSubrepresentation ψ n) (hA0 : A ≠ 0) (v : V) :
    (mirabolicCompactEquivOfRange ψ A hA hA0 v).val = A v := rfl

/-- Evaluation at the identity after an equivalence with the compact model is a
character functional. -/
def mirabolicCompactEvalFunctional (E : ξ.Equiv (mirabolicCompactInduced ψ n)) :
    functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ :=
  ⟨{ toFun := fun v => mirabolicCompactEval ψ n (E v) 1
     map_add' := by intro v w; rw [map_add]; rfl
     map_smul' := by intro a v; rw [map_smul]; rfl }, by
    intro u v
    change mirabolicCompactEval ψ n (E (ξ u v)) 1 =
      (mirabolicCharacter ψ n u : ℂ) * mirabolicCompactEval ψ n (E v) 1
    have hE : E (ξ u v) = mirabolicCompactInduced ψ n u (E v) :=
      LinearMap.congr_fun (E.isIntertwining' u) v
    rw [hE, mirabolicCompactEval_translate, one_mul, ← mul_one (u : mirabolic n F),
      mirabolicCompactEval_covariance]⟩

@[simp] theorem mirabolicCompactEvalFunctional_apply
    (E : ξ.Equiv (mirabolicCompactInduced ψ n)) (v : V) :
    (mirabolicCompactEvalFunctional ψ E).val v = mirabolicCompactEval ψ n (E v) 1 := rfl

/-- The generic assembly: compact minimality, a compact function not vanishing at
the identity, and countable dimension of the representation give the three
clauses of JPSS Section 1.5, Corollary 1, for one smooth irreducible representation. -/
theorem mirabolicFunctionalMultiplicity_of_generic
    (hmin : ∀ W : Subrepresentation (mirabolicSmoothInduced ψ n), W ≠ ⊥ →
      mirabolicCompactSubrepresentation ψ n ≤ W)
    (hne : ∃ f : MirabolicCompactFunctions ψ n, mirabolicCompactEval ψ n f 1 ≠ 0)
    (hξ : IsSmooth ξ) (hirr : Representation.IsIrreducible ξ)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) :
    let L := functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n) ξ
    let τ := mirabolicCompactInduced ψ n
    (∀ ℓ ℓ' : L, ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ) ∧
    (Nonempty (L ≃ₗ[ℂ] ℂ) ↔ Nonempty (ξ.Equiv τ)) ∧
    (¬ Nonempty (ξ.Equiv τ) → ∀ ℓ : L, ℓ = 0) := by
  intro L τ
  have := hirr
  have hne' : ∃ f : MirabolicCompactFunctions ψ n, f ≠ 0 := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨f, fun h => hf (by rw [h]; rfl)⟩
  have hequiv : ∀ ℓ : L, ℓ ≠ 0 →
      ∃ E : ξ.Equiv τ, ∀ v, (E v).val = mirabolicFrobeniusMap ψ hξ ℓ v := by
    intro ℓ hℓ
    have hR := mirabolicFrobeniusMap_range_ne_bot ψ hξ ℓ hℓ
    have hA0 : mirabolicFrobeniusMap ψ hξ ℓ ≠ 0 := by
      intro h
      apply hℓ
      apply Subtype.ext
      ext v
      change ℓ.val v = 0
      rw [← mirabolicFrobeniusMap_eval_one ψ hξ ℓ v, h]
      rfl
    exact ⟨mirabolicCompactEquivOfRange ψ _ (range_eq_mirabolicCompact ψ hmin hne' _ hR) hA0,
      fun v => rfl⟩
  have hscalar : ∀ ℓ ℓ' : L, ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ := by
    intro ℓ ℓ' hℓ
    by_cases hℓ' : ℓ' = 0
    · exact ⟨0, by rw [hℓ', zero_smul]⟩
    obtain ⟨E, hE⟩ := hequiv ℓ hℓ
    obtain ⟨E', hE'⟩ := hequiv ℓ' hℓ'
    obtain ⟨c, hc, -⟩ := countableDimensionalSchur ξ hrank hirr
      (E.symm.toIntertwiningMap.comp E'.toIntertwiningMap)
    refine ⟨c, Subtype.ext (LinearMap.ext fun v => ?_)⟩
    have hv : E.symm (E' v) = c • v :=
      congrArg (fun φ : ξ.IntertwiningMap ξ => φ v) hc
    have hEv : E' v = c • E v := by
      rw [← map_smul, ← hv, E.apply_symm_apply]
    have key : mirabolicEval ψ n (E' v).val 1 = c * mirabolicEval ψ n (E v).val 1 := by
      rw [hEv]
      rfl
    rw [hE', hE, mirabolicFrobeniusMap_eval_one, mirabolicFrobeniusMap_eval_one] at key
    exact key
  have hforward : ∀ ℓ : L, ℓ ≠ 0 → Nonempty (ξ.Equiv τ) := fun ℓ hℓ =>
    ⟨(hequiv ℓ hℓ).choose⟩
  refine ⟨hscalar, ⟨fun ⟨e⟩ => ?_, fun ⟨E⟩ => ?_⟩, fun hE ℓ => ?_⟩
  · refine hforward (e.symm 1) fun h => one_ne_zero (α := ℂ) ?_
    rw [← e.apply_symm_apply 1, h, map_zero]
  · let ℓ0 : L := mirabolicCompactEvalFunctional ψ E
    have hℓ0 : ℓ0 ≠ 0 := by
      obtain ⟨f, hf⟩ := hne
      intro h
      apply hf
      have hv : (mirabolicCompactEvalFunctional ψ E).val (E.symm f) = 0 := by
        rw [show mirabolicCompactEvalFunctional ψ E = 0 from h]
        rfl
      rw [mirabolicCompactEvalFunctional_apply, E.apply_symm_apply] at hv
      exact hv
    let φ : ℂ →ₗ[ℂ] L := LinearMap.toSpanSingleton ℂ L ℓ0
    have hφ : Function.Bijective φ := by
      refine ⟨fun a b hab => ?_, fun ℓ => ?_⟩
      · exact smul_left_injective ℂ hℓ0 hab
      · obtain ⟨c, hc⟩ := hscalar ℓ0 ℓ hℓ0
        exact ⟨c, hc.symm⟩
    exact ⟨(LinearEquiv.ofBijective φ hφ).symm⟩
  · by_contra hℓ
    exact hE (hforward ℓ hℓ)

/-- The scalar character representation is smooth: its kernel is open. -/
theorem mirabolicCharacterRepresentation_smooth
    [NonarchimedeanGroup (mirabolic n F)] :
    IsSmooth (mirabolicCharacterRepresentation ψ n) := by
  intro z
  refine ⟨{ toSubgroup := (mirabolicCharacter ψ n).ker
            isOpen' := Langlands.isOpen_ker_of_continuous_complex_character _
              (mirabolicCharacterContinuous ψ n).continuous }, ?_⟩
  intro k
  change (mirabolicCharacter ψ n k : ℂ) * z = z
  rw [show mirabolicCharacter ψ n k = 1 from k.property, Units.val_one, one_mul]

/-- A compactly supported covariant function with value one at the identity. -/
theorem exists_mirabolicCompactEval_one_ne_zero
    [NonarchimedeanGroup (mirabolic n F)] [WeaklyLocallyCompactSpace (mirabolic n F)] :
    ∃ f : MirabolicCompactFunctions ψ n, mirabolicCompactEval ψ n f 1 ≠ 0 := by
  refine ⟨Induction.compactLocalSection _ _ (mirabolicCharacterRepresentation_smooth ψ)
    1 1 Set.univ isOpen_univ (Set.mem_univ _), ?_⟩
  have h := Induction.compactLocalSection_apply _ _ (mirabolicCharacterRepresentation_smooth ψ)
    (1 : mirabolic n F) (1 : ℂ) Set.univ isOpen_univ (Set.mem_univ _)
  change Induction.eval _ _ _ 1 ≠ 0
  rw [h]
  exact one_ne_zero

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The canonical-topology case, from compact minimality. -/
theorem mirabolicFunctionalMultiplicity_canonical
    (hmin : MirabolicCompactMinimalityStatement.{uF})
    (F : PadicField.{uF} p) (n : ℕ) :
    MirabolicFunctionalMultiplicityStatement.{uF, uV} F F.canonicalTopologicalData n := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let : NonarchimedeanGroup (GeneralLinear (n + 1) F.Carrier) :=
    Langlands.valuativeGeneralLinearNonarchimedean F.Carrier (n + 1)
  let : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  let : LocallyCompactSpace (mirabolic n F.Carrier) := Mirabolic.locallyCompactSpace
  have : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
  have : SecondCountableTopology (mirabolic n F.Carrier) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  intro ψ V _ _ ξ hξ hirr
  exact mirabolicFunctionalMultiplicity_of_generic ψ (hmin p inferInstance F n ψ)
    (exists_mirabolicCompactEval_one_ne_zero ψ) hξ hirr
    (MirabolicRigidity.rank_le_aleph0 ξ hξ hirr)

/-- The target for every supplied topology, which agrees with the canonical one. -/
theorem mirabolicFunctionalMultiplicity_of_minimality
    (hmin : MirabolicCompactMinimalityStatement.{uF})
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n := by
  have hT : T.topology = F.canonicalTopologicalData.topology :=
    T.topology_eq_canonicalModule.trans (PadicField.canonicalTopologicalData_topology F).symm
  have key := mirabolicFunctionalMultiplicity_canonical.{uF, uV} hmin F n
  obtain @⟨t, vr, ve, mt, lf⟩ := T
  change t = _ at hT
  subst hT
  exact key

end Padic

/-- JPSS (1983), Section 1.5, Corollary 1, for the actual mirabolic group over every
p-adic field and every supplied topological datum. -/
theorem mirabolicFunctionalMultiplicity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n :=
  mirabolicFunctionalMultiplicity_of_minimality mirabolicCompactMinimality F T n

end Langlands.Whittaker
