import Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessStatement
import Langlands.Representation.Whittaker.UnipotentOrbitProof
import Langlands.Representation.Whittaker.CompactLocalizationProof
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Jacquet.LocalizationTransport
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.LocalField.Normalization.Proof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof

/-!
# Proof that normalized parabolic induction preserves finite character coinvariants

The finite upper-unipotent orbit filtration of the normalized induced module,
compact localization on each orbit, and the embedded Levi upper-unipotent group
in each orbit stabilizer reduce the conclusion to the coefficient premise.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Whittaker

open GeneralLinear Geometric Jacquet.Localization

universe uF uV uG uA

section Propagation

variable {G : Type uG} [Group G]

private def stepEmbedding {A : Rep.{uA} ℂ G} (S : Subrepresentation A.ρ) :
    S.toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

private def stepInclusion {A : Rep.{uA} ℂ G} (S T : Subrepresentation A.ρ)
    (hST : S ≤ T) : S.toRepresentation.IntertwiningMap T.toRepresentation where
  toLinearMap := Submodule.inclusion hST
  isIntertwining' _ := rfl

private theorem adjacent_exact {A : Rep.{uA} ℂ G} {m : ℕ}
    (s : ObjectRepFiltration A m) (i : Fin m) :
    LinearMap.range
        (stepInclusion (s.subrepresentation i.castSucc)
          (s.subrepresentation i.succ)
          (s.monotone_subrepresentation (Nat.le_succ i.val))).toLinearMap =
      LinearMap.ker (s.gradedProjection i).hom.toLinearMap := by
  have hpzero (w : (s.subrepresentation i.succ).toSubmodule) :
      (s.gradedProjection i).hom w = 0 ↔ (w : A) ∈ s.subrepresentation i.castSucc :=
    Submodule.Quotient.mk_eq_zero _
  ext w
  change (∃ v, stepInclusion _ _ _ v = w) ↔ (s.gradedProjection i).hom w = 0
  rw [hpzero]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · intro hw
    exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩

/-- Right exactness of the character quotient propagates finite dimension
from the graded pieces of a finite filtration to the whole representation. -/
private theorem finiteDimensional_of_filtration {A : Rep.{uA} ℂ G} {m : ℕ}
    (s : ObjectRepFiltration A m) (U : Subgroup G) (θ : U →* ℂˣ)
    (hfin : ∀ i, FiniteDimensional ℂ (Coinvariants (s.gradedRepresentation i).ρ U θ)) :
    FiniteDimensional ℂ (Coinvariants A.ρ U θ) := by
  have hMU : (⊥ : Subgroup G) ≤ Subgroup.normalizer U := bot_le
  have hθinv : IsInvariant U ⊥ hMU θ := by
    intro a u
    apply congrArg θ
    apply Subtype.ext
    have ha : (a : G) = 1 := Subgroup.mem_bot.mp a.property
    simp [conjugate, ha]
  let C (k : Fin (m + 1)) :=
    Coinvariants (s.subrepresentation k).toRepresentation U θ
  let inc (i : Fin m) :=
    stepInclusion (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)
      (s.monotone_subrepresentation (Nat.le_succ i.val))
  have hC (k : Fin (m + 1)) : FiniteDimensional ℂ (C k) := by
    induction k using Fin.induction with
    | zero =>
        have : Subsingleton (s.subrepresentation 0).toSubmodule := by
          rw [s.subrepresentation_zero]
          change Subsingleton (⊥ : Submodule ℂ A)
          infer_instance
        have : Subsingleton (C 0) := inferInstance
        refine Module.finite_def.mpr ?_
        rw [Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule ℂ (C 0)))]
        exact Submodule.fg_bot
    | succ i ih =>
        have hex := map_range_eq_ker U θ ⊥ hMU hθinv (inc i) (s.gradedProjection i).hom
          (s.gradedProjection_surjective i) (adjacent_exact s i)
        have hq := map_surjective U θ ⊥ hMU hθinv (s.gradedProjection i).hom
          (s.gradedProjection_surjective i)
        have := hfin i
        refine Module.finite_def.mpr ?_
        apply Submodule.fg_of_fg_map_of_fg_inf_ker
          (map U θ ⊥ hMU hθinv (s.gradedProjection i).hom).toLinearMap
        · rw [Submodule.map_top, LinearMap.range_eq_top.mpr hq]
          exact Module.finite_def.mp inferInstance
        · rw [top_inf_eq, ← hex, LinearMap.range_eq_map]
          exact (Module.finite_def.mp ih).map _
  have hlast := hC (Fin.last m)
  let a := stepEmbedding (s.subrepresentation (Fin.last m))
  have ha : Function.Surjective a := by
    intro v
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [s.subrepresentation_last]
    trivial
  exact Module.Finite.of_surjective (map U θ ⊥ hMU hθinv a).toLinearMap
    (map_surjective U θ ⊥ hMU hθinv a ha)

end Propagation

/-- The target body for a field topology `τ`, a topological-group certificate
and a covariance character `χ`. -/
private def Body (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (τ : TopologicalSpace F.Carrier) (n : ℕ) (B : BlockShape n)
    (hG : letI := τ; IsTopologicalGroup (Langlands.GeneralLinear n F.Carrier))
    (χ : B.parabolic F.Carrier →* ℂˣ) : Prop :=
  letI := τ
  letI := hG
  ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    (∀ η : (Subgroup.pi Set.univ
        (fun i : Fin B.length => upperUnipotent (B.size i) F.Carrier)) →* ℂˣ,
      IsLocallyConstant (fun u => (η u : ℂ)) →
      FiniteDimensional ℂ
        (Coinvariants σ.representation
          (Subgroup.pi Set.univ
            (fun i : Fin B.length => upperUnipotent (B.size i) F.Carrier)) η)) →
    ∀ θ : upperUnipotent n F.Carrier →* ℂˣ,
      IsLocallyConstant (fun u => (θ u : ℂ)) →
      FiniteDimensional ℂ
        (Coinvariants
          (Induction.smoothInduced (B.parabolic F.Carrier)
            (twist χ (σ.representation.comp (B.leviProjection F.Carrier))))
          (upperUnipotent n F.Carrier) θ)

/-- The determinant of a unitriangular matrix is one. -/
private theorem determinant_upperUnipotent {R : Type*} [CommRing R] {k : ℕ}
    (g : upperUnipotent k R) : GeneralLinear.determinant (g : Langlands.GeneralLinear k R) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_isUpperTriangular g.property.1]
  exact Finset.prod_eq_one (fun a _ => g.property.2 a)

/-- Conjugating the block-diagonal unitriangular group by an inverse minimal
permutation lands in the full upper-unipotent group. -/
private theorem conj_leviEmbedding_mem {R : Type*} [CommRing R] {n : ℕ}
    (B : BlockShape n) (w : MinimalRepresentatives B (BlockShape.singletons n))
    (u : Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) R)) :
    permutation n R w.val * B.leviEmbedding R (u : B.Levi R) *
        (permutation n R w.val)⁻¹ ∈ upperUnipotent n R := by
  have hu (i : Fin B.length) : (u : B.Levi R) i ∈ upperUnipotent (B.size i) R :=
    u.property i (Set.mem_univ i)
  refine ⟨?_, ?_⟩
  · intro x y hyx
    rw [permutation_conjugate_entry]
    obtain ⟨⟨i, a⟩, ha⟩ := B.indexEquiv.surjective (w.val⁻¹ x)
    obtain ⟨⟨j, b⟩, hb⟩ := B.indexEquiv.surjective (w.val⁻¹ y)
    rw [← ha, ← hb]
    change B.leviEmbedding R (u : B.Levi R) (B.index i a) (B.index j b) = 0
    by_cases hij : i = j
    · subst hij
      rw [B.leviEmbedding_apply_same]
      have hxa : w.val (B.index i a) = x := by
        change w.val (B.indexEquiv ⟨i, a⟩) = x
        rw [ha]
        simp
      have hyb : w.val (B.index i b) = y := by
        change w.val (B.indexEquiv ⟨i, b⟩) = y
        rw [hb]
        simp
      have hba : b < a := by
        apply (w.property.1 i).lt_iff_lt.mp
        change w.val (B.index i b) < w.val (B.index i a)
        rw [hxa, hyb]
        exact hyx
      exact UpperUnipotent.entry_eq_zero ⟨_, hu i⟩ hba
    · exact B.leviEmbedding_apply_ne R _ a b hij
  · intro x
    rw [permutation_conjugate_entry]
    obtain ⟨⟨i, a⟩, ha⟩ := B.indexEquiv.surjective (w.val⁻¹ x)
    rw [← ha]
    change B.leviEmbedding R (u : B.Levi R) (B.index i a) (B.index i a) = 1
    rw [B.leviEmbedding_apply_same]
    exact UpperUnipotent.entry_diag ⟨_, hu i⟩ a

/-- On each minimal orbit, the stabilizer quotient of the conjugated covariance
representation is a quotient of a Levi upper-unipotent coefficient quotient. -/
private theorem stabilizerCoinvariants_finite (p : ℕ) [Fact p.Prime]
    (F : PadicField.{uF} p) (n : ℕ) (B : BlockShape (n + 1)) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
    ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      (∀ η : (Subgroup.pi Set.univ
          (fun i : Fin B.length => upperUnipotent (B.size i) F.Carrier)) →* ℂˣ,
        IsLocallyConstant (fun u => (η u : ℂ)) →
        FiniteDimensional ℂ
          (Coinvariants σ.representation
            (Subgroup.pi Set.univ
              (fun i : Fin B.length => upperUnipotent (B.size i) F.Carrier)) η)) →
      ∀ θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ,
        IsLocallyConstant (fun u => (θ u : ℂ)) →
        ∀ w : MinimalRepresentatives B (BlockShape.singletons (n + 1)),
          FiniteDimensional ℂ
            (Coinvariants
              ((twist (F.canonicalTopologicalData.parabolicHalfModulus B)
                  (σ.representation.comp (B.leviProjection F.Carrier))).comp
                (stabilizerToInducing (B.parabolic F.Carrier)
                  (upperUnipotent (n + 1) F.Carrier)
                  (permutation (n + 1) F.Carrier w.val)))
              (⊤ : Subgroup (orbitStabilizer (B.parabolic F.Carrier)
                (upperUnipotent (n + 1) F.Carrier) (permutation (n + 1) F.Carrier w.val)))
              (((θ.comp (orbitStabilizer (B.parabolic F.Carrier)
                  (upperUnipotent (n + 1) F.Carrier)
                  (permutation (n + 1) F.Carrier w.val)).subtype)).comp
                (⊤ : Subgroup (orbitStabilizer (B.parabolic F.Carrier)
                  (upperUnipotent (n + 1) F.Carrier)
                  (permutation (n + 1) F.Carrier w.val))).subtype)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  intro σ hσfin θ hθ w
  let P := B.parabolic F.Carrier
  let U := upperUnipotent (n + 1) F.Carrier
  let UM := Subgroup.pi Set.univ (fun i : Fin B.length => upperUnipotent (B.size i) F.Carrier)
  let r := permutation (n + 1) F.Carrier w.val
  let S := orbitStabilizer P U r
  let χ := F.canonicalTopologicalData.parabolicHalfModulus B
  let ι := B.leviEmbedding F.Carrier
  let jU : UM →* U :=
    ((MulAut.conj r).toMonoidHom.comp (ι.comp UM.subtype)).codRestrict U
      (fun u => by
        change r * ι (u : B.Levi F.Carrier) * r⁻¹ ∈ U
        exact conj_leviEmbedding_mem B w u)
  have hjU (u : UM) : ((jU u : U) : Langlands.GeneralLinear (n + 1) F.Carrier) =
      r * ι (u : B.Levi F.Carrier) * r⁻¹ := rfl
  let j : UM →* S :=
    jU.codRestrict S (fun u => by
      change (MulAut.conj r⁻¹) ((jU u : U) : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ P
      rw [hjU, MulAut.conj_apply]
      have h : r⁻¹ * (r * ι (u : B.Levi F.Carrier) * r⁻¹) * r⁻¹⁻¹ =
          ι (u : B.Levi F.Carrier) := by group
      rw [h]
      exact (B.leviInParabolic F.Carrier (u : B.Levi F.Carrier)).property)
  have hst (u : UM) :
      stabilizerToInducing P U r (j u) = B.leviInParabolic F.Carrier (u : B.Levi F.Carrier) := by
    apply Subtype.ext
    rw [stabilizerToInducing_apply, B.leviInParabolic_val]
    change r⁻¹ * (r * ι (u : B.Levi F.Carrier) * r⁻¹) * r = ι (u : B.Levi F.Carrier)
    group
  have hχ (u : UM) : χ (B.leviInParabolic F.Carrier (u : B.Levi F.Carrier)) = 1 := by
    change F.canonicalTopologicalData.parabolicHalfModulus B
      (B.leviInParabolic F.Carrier (u : B.Levi F.Carrier)) = 1
    rw [F.canonicalTopologicalData.parabolicHalfModulus_section,
      F.canonicalTopologicalData.leviHalfModulus_eq_one]
    apply F.canonicalTopologicalData.normOneLevi_le_ker_leviModulus B
    rw [F.canonicalTopologicalData.mem_normOneLevi]
    intro i
    have hu : (u : B.Levi F.Carrier) i ∈ upperUnipotent (B.size i) F.Carrier :=
      u.property i (Set.mem_univ i)
    rw [PadicField.TopologicalData.determinantNorm, MonoidHom.comp_apply,
      determinant_upperUnipotent ⟨_, hu⟩, map_one]
  let piece := (twist χ (σ.representation.comp (B.leviProjection F.Carrier))).comp
    (stabilizerToInducing P U r)
  have hpiece (u : UM) (v : σ) : piece (j u) v = σ.representation (u : B.Levi F.Carrier) v := by
    change (χ (stabilizerToInducing P U r (j u)) : ℂ) •
      σ.representation (B.leviProjection F.Carrier (stabilizerToInducing P U r (j u))) v = _
    rw [hst, hχ, B.leviProjection_section, Units.val_one, one_smul]
  let θS : (⊤ : Subgroup S) →* ℂˣ := (θ.comp S.subtype).comp (⊤ : Subgroup S).subtype
  let η : UM →* ℂˣ := (θ.comp S.subtype).comp j
  have hjc : Continuous (fun u : UM => (jU u : U)) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun u : UM => r * ι (u : B.Levi F.Carrier) * r⁻¹)
    exact (continuous_const.mul ((B.leviEmbeddingContinuous F.Carrier).continuous.comp
      continuous_subtype_val)).mul continuous_const
  have hηloc : IsLocallyConstant (fun u => (η u : ℂ)) :=
    hθ.comp_continuous hjc
  have hfin := hσfin η hηloc
  have hle : relations σ.representation UM η ≤ relations piece (⊤ : Subgroup S) θS := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have h := sub_mem_relations piece (⊤ : Subgroup S) θS ⟨j u, trivial⟩ v
    change piece (j u) v - (η u : ℂ) • v ∈ relations piece (⊤ : Subgroup S) θS at h
    rw [hpiece] at h
    exact h
  exact Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/-- The canonical-topology case of the target. -/
private theorem core (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    (B : BlockShape (n + 1)) :
    Body.{uF, uV} p F F.canonicalTopologicalData.topology (n + 1) B
      (F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1))
      (F.canonicalTopologicalData.parabolicHalfModulus B) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  let := F.canonicalTopologicalData.generalLinearNonarchimedean (n + 1)
  let := F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  let := F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
  intro σ hσfin θ hθ
  let P := B.parabolic F.Carrier
  let U := upperUnipotent (n + 1) F.Carrier
  let χ := F.canonicalTopologicalData.parabolicHalfModulus B
  let cov := twist χ (σ.representation.comp (B.leviProjection F.Carrier))
  have hcov : IsSmooth cov :=
    (isSmooth_twist_iff χ _ (F.canonicalTopologicalData.isOpen_ker_parabolicHalfModulus B)).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous σ.isSmooth)
  let A : SmoothRep.{0, uF, uV} ℂ P := SmoothRep.of cov hcov
  have hP : IsClosed (P : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    B.isClosed_parabolic F.Carrier
  have hU : IsClosed (U : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    UpperUnipotent.isClosed
  have hθopen : IsOpen (θ.ker : Set U) := by
    have h : (θ.ker : Set U) = (fun u => (θ u : ℂ)) ⁻¹' {1} := by
      ext u
      simp [MonoidHom.mem_ker]
    rw [h]
    exact hθ.isOpen_fiber 1
  let θs : Induction.SmoothCharacter ℂ U := ⟨θ, hθopen⟩
  let : CompactSpace (Induction.LeftQuotient P) :=
    Parabolic.parabolicQuotientCompact F F.canonicalTopologicalData B
  obtain ⟨_hbij, m, s, e, he⟩ := unipotentOrbit p F n B
  let ambient := (restrictedCompactInduction (R := ℂ) P U).obj A
  let sf := s.supportFiltration (R := ℂ)
  let fs : ObjectRepFiltration ambient m :=
    ObjectRepFiltration.ofSubrepresentations (fun k => (sf.step k).obj A)
      (sf.monotone A) (sf.zero A) (sf.top A)
  let pieceσ (i : Fin m) := cov.comp (stabilizerToInducing P U (s.representative i))
  have hsmooth (i : Fin m) : IsSmooth (pieceσ i) := by
    apply isSmooth_comp _ _ hcov
    exact ((continuous_const.mul
      (continuous_subtype_val.comp continuous_subtype_val)).mul
        continuous_const).subtype_mk _
  have hpiece (i : Fin m) :
      FiniteDimensional ℂ
        (Coinvariants (pieceσ i) (⊤ : Subgroup (orbitStabilizer P U (s.representative i)))
          ((θ.comp (orbitStabilizer P U (s.representative i)).subtype).comp
            (⊤ : Subgroup (orbitStabilizer P U (s.representative i))).subtype)) := by
    have h := stabilizerCoinvariants_finite.{uF, uV} p F n B σ hσfin θ hθ (e i)
    rw [← he i] at h
    exact h
  have hgraded (i : Fin m) :
      FiniteDimensional ℂ
        (Coinvariants (fs.gradedRepresentation i).ρ (⊤ : Subgroup U)
          (θ.comp (⊤ : Subgroup U).subtype)) := by
    obtain ⟨eg⟩ := closedSubgroupMackeyFiltration
      (Langlands.GeneralLinear (n + 1) F.Carrier) P U hP hU m s i
    let er := Representation.equivOfIso (eg.app A)
    obtain ⟨ec⟩ := compactLocalization p inferInstance F n
      (orbitStabilizer P U (s.representative i))
      (isClosed_orbitStabilizer P U (s.representative i) hP)
      _ (pieceσ i) (hsmooth i) θs
    have := hpiece i
    exact LinearEquiv.finiteDimensional
      ((representationEquiv (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) er).trans ec).symm
  have hambient : FiniteDimensional ℂ
      (Coinvariants ambient.ρ (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype)) :=
    finiteDimensional_of_filtration fs (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) hgraded
  let ecomp := Representation.equivOfIso
    ((rawRestrictedCompactSmoothIso (R := ℂ) P U).app A.obj)
  have : FiniteDimensional ℂ
      (Coinvariants ((rawRestrictedCompactInduction (R := ℂ) P U).obj A.obj).ρ
        (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype)) := hambient
  let eambient :=
    (representationEquiv (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) ecomp).trans
      (restrictionEquiv (Induction.smoothInduced P cov) U θ)
  exact LinearEquiv.finiteDimensional eambient

/-- Normalized parabolic induction preserves finite-dimensionality of all locally
constant upper-unipotent character quotients, given the same for the coefficient. -/
theorem parabolicInducedCoinvariantFiniteness :
    ParabolicInducedCoinvariantFinitenessStatement.{uF, uV} := by
  intro p _ F T n hn B
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hT : T.topology = F.canonicalTopologicalData.topology :=
    T.topology_eq_canonicalModule.trans
      F.canonicalTopologicalData.topology_eq_canonicalModule.symm
  have key : ∀ (τ : TopologicalSpace F.Carrier) (χ : B.parabolic F.Carrier →* ℂˣ),
      τ = F.canonicalTopologicalData.topology →
      χ = F.canonicalTopologicalData.parabolicHalfModulus B →
      ∀ hG, Body.{uF, uV} p F τ (m + 1) B hG χ := by
    rintro τ χ rfl rfl hG
    exact core p F m B
  exact key T.topology (T.parabolicHalfModulus B) hT
    (T.parabolicHalfModulus_eq B F.canonicalTopologicalData)
    (T.generalLinearTopologicalGroup (m + 1))

end Langlands.Whittaker
