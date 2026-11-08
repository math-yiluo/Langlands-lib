import Langlands.Representation.Whittaker.GelfandGraev
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.CompactGrading
import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CuspidalSupport.QuasicuspidalSubquotientProof
import Langlands.Representation.CyclicSpan
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Representation.CuspidalSupport.LeviCompactPart
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.CompactCoefficient.IsotypicSemisimplicityProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.Category.Twist

/-!
# Cuspidal detection in the Gelfand–Graev representation of a product Levi

For a block shape `B` and the product Levi `M = B.Levi F`, let `V_M = c-Ind_{N_M}^M ψ_M` be its
Gelfand–Graev representation. If a nonzero `x ∈ V_M` generates a quasicuspidal subrepresentation,
then some intertwiner from `V_M` to an external tensor product of irreducible supercuspidal
representations does not vanish on `x`.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open GeneralLinear Whittaker CuspidalSupport Induction
open scoped NNReal

universe uF uW

section Basic

/-- Upper unipotent matrices have determinant one. -/
theorem determinant_upperUnipotent {R : Type*} [CommRing R] {d : ℕ} (u : upperUnipotent d R) :
    GeneralLinear.determinant (u : GeneralLinear d R) = 1 := by
  apply Units.ext
  change Matrix.det (u : GeneralLinear d R).val = 1
  rw [Matrix.det_of_isUpperTriangular u.property.1]
  simp [UpperUnipotent.entry_diag]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n)

/-- The topological-ring structure carried by a field realization. -/
theorem topologicalRing : letI := T.topology; IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The product unipotent subgroup lies in the determinant-unit subgroup. -/
theorem leviUpperUnipotent_le_ker :
    leviUpperUnipotent (F := F.Carrier) B ≤ (leviDeterminantNorm T B).ker := by
  intro u hu
  rw [MonoidHom.mem_ker]
  funext i
  have hi : u i ∈ upperUnipotent (B.size i) F.Carrier := hu i (Set.mem_univ i)
  change T.determinantNorm (B.size i) (u i) = 1
  change T.normalizedAbsUnits (GeneralLinear.determinant
    ((⟨u i, hi⟩ : upperUnipotent (B.size i) F.Carrier) : GeneralLinear (B.size i) F.Carrier)) = 1
  rw [determinant_upperUnipotent, map_one]

theorem isOpen_ker_leviDeterminantNorm :
    letI := T.topology
    IsOpen ((leviDeterminantNorm T B).ker : Set (B.Levi F.Carrier)) :=
  isOpen_determinantUnitSubgroup T B

/-- The coordinate characters separate the points of `(ℝ≥0ˣ)^k`. -/
theorem separating_characters {k : ℕ} (d : Fin k → ℝ≥0ˣ) (hd : d ≠ 1) :
    ∃ χ : (Fin k → ℝ≥0ˣ) →* ℂˣ, χ d ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 1 := by
    by_contra h
    push Not at h
    exact hd (funext h)
  let c : ℝ≥0 →* ℂ := (Complex.ofRealHom.toMonoidHom).comp NNReal.toRealHom.toMonoidHom
  refine ⟨(Units.map c).comp (Pi.evalMonoidHom (fun _ : Fin k => ℝ≥0ˣ) i), ?_⟩
  intro h
  apply hi
  have h' := congrArg (fun z : ℂˣ => (z : ℂ)) h
  simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Units.coe_map, Units.val_one] at h'
  have h'' : (((d i : ℝ≥0) : ℝ) : ℂ) = 1 := h'
  have h3 : ((d i : ℝ≥0) : ℝ) = 1 := Complex.ofReal_eq_one.mp h''
  exact Units.ext (NNReal.coe_eq_one.mp h3)

/-- Refined unipotent radicals lie in the determinant-unit subgroup. -/
theorem refinedUnipotent_le_ker (R : Geometric.BlockRefinement B) :
    Geometric.refinedUnipotent F.Carrier B R ≤ (leviDeterminantNorm T B).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  funext i
  have hdet := (R i).determinant_eq_one_of_mem_unipotentSubgroup
    ((Geometric.mem_refinedUnipotent F.Carrier B R g).mp hg i)
  change T.normalizedAbsUnits (GeneralLinear.determinant (g i)) = 1
  rw [hdet, map_one]

end Basic

section GradedQuasicuspidal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) (ψ : AddChar F.Carrier ℂ)

/-- An element of a subrepresentation with vanishing coinvariants lies in the ambient
coinvariant relations. -/
theorem mem_relations_of_subsingleton {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ G V} (X : Subrepresentation ρ) (N : Subgroup G)
    (hX : Subsingleton (Jacquet.Coinvariants X.toRepresentation N)) {w : V}
    (hw : w ∈ X.toSubmodule) : w ∈ Jacquet.relations ρ N := by
  rw [← Jacquet.mk_eq_zero]
  let i : X.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := X.toSubmodule.subtype
      isIntertwining' _ := LinearMap.ext fun _ => rfl }
  have h0 : Jacquet.mk X.toRepresentation N ⟨w, hw⟩ = 0 := Subsingleton.elim _ _
  have h1 := congrArg (Representation.Coinvariants.map _ _ (Jacquet.restrictMap i N)) h0
  rw [map_zero] at h1
  exact h1

/-- Graded pieces of a vector with quasicuspidal span have quasicuspidal span. -/
theorem isLeviQuasicuspidal_orbitSpan_gradedPiece :
    letI := T.topology
    letI := topologicalRing T
    ∀ (x : LeviGelfandGraevFunctions (F := F.Carrier) B ψ) (d : Fin B.length → ℝ≥0ˣ),
      IsLeviQuasicuspidal B (Cyclic.orbitSpan (leviGelfandGraev B ψ) x).toRepresentation →
      IsLeviQuasicuspidal B (Cyclic.orbitSpan (leviGelfandGraev B ψ)
        (gradedPiece (leviUpperUnipotent_le_ker T B) (isOpen_ker_leviDeterminantNorm T B)
          d x)).toRepresentation := by
  let := T.topology
  let := topologicalRing T
  let := T.leviTopologicalGroup B
  intro x d hx R hR
  let ρ := leviGelfandGraev (F := F.Carrier) B ψ
  let N := Geometric.refinedUnipotent F.Carrier B R
  have hP := leviUpperUnipotent_le_ker T B
  have hν := isOpen_ker_leviDeterminantNorm T B
  -- graded projections preserve the ambient relations
  have hrel : ∀ e : Fin B.length → ℝ≥0ˣ, ∀ v ∈ Jacquet.relations ρ N,
      gradedPiece hP hν e v ∈ Jacquet.relations ρ N := by
    intro e
    suffices h : Jacquet.relations ρ N ≤
        (Jacquet.relations ρ N).comap (gradedProjection hP hν e) from fun v hv => h hv
    conv_lhs => rw [Jacquet.relations_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change gradedPiece hP hν e (ρ u v - v) ∈ Jacquet.relations ρ N
    rw [← gradedProjection_apply, map_sub, gradedProjection_apply,
      gradedProjection_apply]
    change gradedPiece hP hν e (compactInduced _ _ (u : B.Levi F.Carrier) v) - _ ∈ _
    rw [gradedPiece_translate_ker hP hν e (refinedUnipotent_le_ker T B R u.property)]
    exact Jacquet.sub_mem_relations ρ N u _
  -- every element of the graded span lies in the ambient relations
  have hY : ∀ w ∈ (Cyclic.orbitSpan ρ (gradedPiece hP hν d x)).toSubmodule,
      w ∈ Jacquet.relations ρ N := by
    intro w hw
    change w ∈ FiniteVectors.orbitSpan ρ _ at hw
    revert w
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    have hmx : ρ m x ∈ (Cyclic.orbitSpan ρ x).toSubmodule :=
      FiniteVectors.action_mem_orbitSpan ρ m x
    have h1 := mem_relations_of_subsingleton _ N (hx R hR) hmx
    have h2 := hrel (d * (leviDeterminantNorm T B m)⁻¹) _ h1
    change gradedPiece hP hν _ (compactInduced _ _ m x) ∈ _ at h2
    rw [gradedPiece_translate, inv_mul_cancel_right] at h2
    exact h2
  -- injectivity of the coinvariant map of the inclusion
  let Y := Cyclic.orbitSpan ρ (gradedPiece hP hν d x)
  let i : Y.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := Y.toSubmodule.subtype
      isIntertwining' _ := LinearMap.ext fun _ => rfl }
  have hsm : IsSmooth (ρ.comp N.subtype) :=
    isSmooth_comp N.subtype continuous_subtype_val (compactInduced_smooth _ _)
  have hinj := coinvariants_map_injective_of_smooth
    (T.refinedUnipotent_finite_containment B R) (Jacquet.restrictMap i N)
    (Submodule.injective_subtype _) hsm
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := Jacquet.mk_surjective Y.toRepresentation N a
  obtain ⟨b, rfl⟩ := Jacquet.mk_surjective Y.toRepresentation N b
  apply hinj
  change Jacquet.mk ρ N a.val = Jacquet.mk ρ N b.val
  rw [(Jacquet.mk_eq_zero ρ N _).mpr (hY a.val a.property),
    (Jacquet.mk_eq_zero ρ N _).mpr (hY b.val b.property)]

end GradedQuasicuspidal

section Projection

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Projection along a complementary invariant subspace commutes with the action. -/
theorem projectionOnto_equivariant (ρ : Representation ℂ G V) (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) (g : G) (x : V) :
    (S.toSubmodule.projectionOnto Q.toSubmodule h (ρ g x) : V) =
      ρ g (S.toSubmodule.projectionOnto Q.toSubmodule h x : V) := by
  set a : V := (S.toSubmodule.projectionOnto Q.toSubmodule h x : V)
  have ha : a ∈ S.toSubmodule := (S.toSubmodule.projectionOnto Q.toSubmodule h x).2
  have hb : x - a ∈ Q.toSubmodule := by
    rw [← Submodule.projectionOnto_apply_eq_zero_iff h, map_sub,
      Submodule.projectionOnto_apply_of_mem_left h ha, sub_eq_zero]
  have hx : ρ g x = ρ g a + ρ g (x - a) := by rw [← map_add, add_sub_cancel]
  rw [hx, map_add, Submodule.projectionOnto_apply_of_mem_left h (S.apply_mem_toSubmodule g ha),
    (Submodule.projectionOnto_apply_eq_zero_iff h).mpr (Q.apply_mem_toSubmodule g hb),
    add_zero]

/-- If a subrepresentation equal to the whole space is semisimple, every subrepresentation of
the ambient representation has an invariant complement. -/
theorem exists_isCompl_of_top {ρ : Representation ℂ G V} (R : Subrepresentation ρ) (hR : R = ⊤)
    [ComplementedLattice (Subrepresentation R.toRepresentation)] (X : Subrepresentation ρ) :
    ∃ C : Subrepresentation ρ, IsCompl X.toSubmodule C.toSubmodule := by
  subst hR
  let ι := (⊤ : Subrepresentation ρ).toSubmodule.subtype
  let X' : Subrepresentation (⊤ : Subrepresentation ρ).toRepresentation :=
    { toSubmodule := X.toSubmodule.comap ι
      apply_mem_toSubmodule := fun g w hw => X.apply_mem_toSubmodule g hw }
  obtain ⟨C', hC'⟩ := exists_isCompl X'
  refine ⟨{ toSubmodule := C'.toSubmodule.map ι
            apply_mem_toSubmodule := ?_ }, ?_⟩
  · rintro g _ ⟨w, hw, rfl⟩
    exact ⟨_, C'.apply_mem_toSubmodule g hw, rfl⟩
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hvX ⟨w, hw, rfl⟩
    have hwX : w ∈ X'.toSubmodule := hvX
    have h0 : w ∈ (X' ⊓ C').toSubmodule := ⟨hwX, hw⟩
    rw [hC'.inf_eq_bot] at h0
    have : w = 0 := h0
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hw : (⟨v, Submodule.mem_top⟩ : (⊤ : Subrepresentation ρ).toSubmodule) ∈
        (X' ⊔ C').toSubmodule := by
      rw [hC'.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    refine Submodule.mem_sup.mpr ⟨a.val, ha, b.val, ⟨b, hb, rfl⟩, ?_⟩
    have := congrArg Subtype.val hab
    simpa using this

end Projection

section QuasicuspidalPart

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n)

universe uV

/-- A vector with quasicuspidal span lies in the quasicuspidal part of a decomposition. -/
theorem mem_of_isLeviQuasicuspidal_orbitSpan :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) (S Q : Subrepresentation A.representation),
      IsCompl S.toSubmodule Q.toSubmodule →
      (∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) →
        IsLeviQuasicuspidal B D.representation → Subsingleton D) →
      ∀ y : A, IsLeviQuasicuspidal B (Cyclic.orbitSpan A.representation y).toRepresentation →
        y ∈ S.toSubmodule := by
  let := T.topology
  intro A S Q hSQ hQ y hy
  let ρ := A.representation
  let Y := Cyclic.orbitSpan ρ y
  let pQ : A →ₗ[ℂ] Q.toSubmodule := Q.toSubmodule.projectionOnto S.toSubmodule hSQ.symm
  let φ : Y.toRepresentation.IntertwiningMap (SmoothRep.subrepresentation A Q).representation :=
    { toLinearMap := pQ.comp Y.toSubmodule.subtype
      isIntertwining' g := by
        ext w
        apply Subtype.ext
        exact projectionOnto_equivariant ρ Q S hSQ.symm g w.val }
  let Z := φ.range
  let φ' : Y.toRepresentation.IntertwiningMap
      (SmoothRep.subrepresentation (SmoothRep.subrepresentation A Q) Z).representation :=
    { toLinearMap := φ.toLinearMap.codRestrict Z.toSubmodule fun w => ⟨w, rfl⟩
      isIntertwining' g := by
        ext w
        apply Subtype.ext
        exact congrArg (fun f : Y.toSubmodule →ₗ[ℂ] _ => f w) (φ.isIntertwining' g) }
  have hφ' : Function.Surjective φ' := by
    rintro ⟨z, ⟨w, rfl⟩⟩
    exact ⟨w, rfl⟩
  have hZq := isLeviQuasicuspidal_of_surjective B φ' hφ' hy
  let D := SmoothRep.subquotient (SmoothRep.subrepresentation A Q) Z ⊥
  have hDq : IsLeviQuasicuspidal B D.representation :=
    isLeviQuasicuspidal_quotient B (A := SmoothRep.subrepresentation
      (SmoothRep.subrepresentation A Q) Z) ⊥ hZq
  have hD := hQ D ⟨Z, ⊥, ⟨CategoryTheory.Iso.refl _⟩⟩ hDq
  have hz : φ (Cyclic.generator ρ y) ∈ Z.toSubmodule := ⟨_, rfl⟩
  let A' := SmoothRep.subrepresentation (SmoothRep.subrepresentation A Q) Z
  let z : A' := ⟨φ (Cyclic.generator ρ y), hz⟩
  have h0 : z ∈ LinearMap.ker (SmoothRep.hom (SmoothRep.mkQ A' ⊥)).toLinearMap :=
    Subsingleton.elim (α := D) _ _
  have hker : LinearMap.ker (SmoothRep.hom (SmoothRep.mkQ A' ⊥)).toLinearMap =
      (⊥ : Subrepresentation A'.representation).toSubmodule :=
    Submodule.ker_mkQ _
  rw [hker] at h0
  have h0' : z = 0 := h0
  have h1 : pQ y = 0 := congrArg Subtype.val h0'
  exact (Submodule.projectionOnto_apply_eq_zero_iff hSQ.symm).mp h1

/-- An irreducible quasicuspidal quotient detected by a map intertwining the
determinant-unit subgroup. -/
theorem exists_determinantUnit_map_ne_zero :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) (y : A),
      IsLeviQuasicuspidal B (Cyclic.orbitSpan A.representation y).toRepresentation → y ≠ 0 →
      ∃ (π : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) (f0 : A →ₗ[ℂ] π),
        π.IsIrreducible ∧ IsLeviQuasicuspidal B π.representation ∧
        (∀ s ∈ (leviDeterminantNorm T B).ker, ∀ v,
          f0 (A.representation s v) = π.representation s (f0 v)) ∧ f0 y ≠ 0 := by
  let := T.topology
  intro A y hy hy0
  let ρ := A.representation
  obtain ⟨S, Q, hSQ, hS, hQ⟩ := leviQuasicuspidalDecomposition F T B A
  have hyS : y ∈ S.toSubmodule := mem_of_isLeviQuasicuspidal_orbitSpan T B A S Q hSQ hQ y hy
  -- the quasicuspidal part restricted to the determinant-unit subgroup is semisimple
  let AS := SmoothRep.subrepresentation A S
  let Dd : SmoothRep.{0, uF, uV} ℂ (determinantUnitSubgroup T B) :=
    SmoothRep.of (determinantUnitRestriction T B AS.representation)
      (isSmooth_determinantUnitRestriction T B AS.isSmooth)
  have hcomp : HasCompactSmoothDualCoefficients Dd.representation :=
    (leviHarishChandraTheorem p F T n B AS).mp hS
  have htop := determinantUnitTotalIsotypic_exhaust T B Dd hcomp
  have hss := (CompactCoefficientClass.isotypicSemisimplicityTheorem.{uF, uV, uV}
    (determinantUnitSubgroup T B) Dd).2.2
  let ys : AS := ⟨y, hyS⟩
  let X := Cyclic.orbitSpan Dd.representation ys
  obtain ⟨C, hXC⟩ := exists_isCompl_of_top _ htop X
  -- the irreducible quotient of the cyclic span of `y`
  let Y := Cyclic.orbitSpan ρ y
  have hgen : ∀ U : Subrepresentation Y.toRepresentation,
      (∀ v ∈ ({Cyclic.generator ρ y} : Finset Y.toSubmodule), v ∈ U) → U = ⊤ := by
    intro U hU
    have hg : Cyclic.generator ρ y ∈ U := hU _ (Finset.mem_singleton_self _)
    apply eq_top_iff.mpr
    rintro ⟨w, hw⟩ -
    change w ∈ FiniteVectors.orbitSpan ρ y at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, rfl⟩ := hw
      exact U.apply_mem_toSubmodule g hg
    | zero => exact U.toSubmodule.zero_mem
    | add a b ha hb iha ihb => exact U.toSubmodule.add_mem iha ihb
    | smul c a ha iha => exact U.toSubmodule.smul_mem c iha
  have : Nontrivial Y.toSubmodule :=
    ⟨⟨Cyclic.generator ρ y, 0, (Cyclic.generator_ne_zero ρ y).mpr hy0⟩⟩
  obtain ⟨K, hK⟩ := QuasicuspidalEmbedding.exists_isCoatom_subrepresentation
    Y.toRepresentation {Cyclic.generator ρ y} hgen
  have hgK : Cyclic.generator ρ y ∉ K := by
    intro h
    exact hK.1 (hgen K (fun v hv => by rw [Finset.mem_singleton.mp hv]; exact h))
  let AY := SmoothRep.subrepresentation A Y
  let π := SmoothRep.quotient AY K
  let q := SmoothRep.hom (SmoothRep.mkQ AY K)
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective AY K
  have hπirr : π.IsIrreducible :=
    QuasicuspidalEmbedding.isIrreducible_of_isCoatom q hq K hK
      (fun v => Submodule.Quotient.mk_eq_zero K.toSubmodule)
  have hπq : IsLeviQuasicuspidal B π.representation :=
    isLeviQuasicuspidal_of_surjective B q hq hy
  -- the map
  have hXY : ∀ w ∈ X.toSubmodule, (w : AS).val ∈ Y.toSubmodule := by
    intro w hw
    change w ∈ FiniteVectors.orbitSpan Dd.representation ys at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, rfl⟩ := hw
      exact FiniteVectors.action_mem_orbitSpan ρ g.val y
    | zero => exact Y.toSubmodule.zero_mem
    | add a b ha hb iha ihb => exact Y.toSubmodule.add_mem iha ihb
    | smul c a ha iha => exact Y.toSubmodule.smul_mem c iha
  let pS : A →ₗ[ℂ] AS := S.toSubmodule.projectionOnto Q.toSubmodule hSQ
  let pX : AS →ₗ[ℂ] X.toSubmodule := X.toSubmodule.projectionOnto C.toSubmodule hXC
  let ιX : X.toSubmodule →ₗ[ℂ] AS := X.toSubmodule.subtype
  let ιS : AS →ₗ[ℂ] A := S.toSubmodule.subtype
  let r : A →ₗ[ℂ] AY := LinearMap.codRestrict Y.toSubmodule (ιS.comp (ιX.comp (pX.comp pS)))
    (fun v => hXY _ (pX (pS v)).2)
  refine ⟨π, q.toLinearMap.comp r, hπirr, hπq, ?_, ?_⟩
  · intro s hs v
    change q (r (ρ s v)) = π.representation s (q (r v))
    rw [← Representation.IntertwiningMap.isIntertwining _ _ q s]
    congr 1
    apply Subtype.ext
    change (pX (pS (ρ s v)) : AS).val = ρ s (pX (pS v) : AS).val
    have h1 : (pS (ρ s v)).val = ρ s (pS v).val := projectionOnto_equivariant ρ S Q hSQ s v
    have h1' : pS (ρ s v) = AS.representation s (pS v) := Subtype.ext h1
    rw [h1']
    have h2 := projectionOnto_equivariant Dd.representation X C hXC ⟨s, hs⟩ (pS v)
    exact congrArg Subtype.val h2
  · change q (r y) ≠ 0
    have hry : r y = ⟨y, Cyclic.mem_orbitSpan ρ y⟩ := by
      apply Subtype.ext
      change (pX (pS y) : AS).val = y
      have h1 : pS y = ys := Submodule.projectionOnto_apply_of_mem_left hSQ hyS
      rw [h1, Submodule.projectionOnto_apply_of_mem_left hXC (Cyclic.mem_orbitSpan _ ys)]
    rw [hry]
    intro h0
    apply hgK
    exact (Submodule.Quotient.mk_eq_zero K.toSubmodule).mp h0

end QuasicuspidalPart

section Detection

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) (ψ : AddChar F.Carrier ℂ)

/-- Translates generate the same cyclic subrepresentation. -/
theorem orbitSpan_translate {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (t : G) (v : V) :
    Cyclic.orbitSpan ρ (ρ t v) = Cyclic.orbitSpan ρ v := by
  apply le_antisymm
  · exact Cyclic.orbitSpan_le ρ _ (FiniteVectors.action_mem_orbitSpan ρ t v)
  · apply Cyclic.orbitSpan_le ρ v
    have h := FiniteVectors.action_mem_orbitSpan ρ t⁻¹ (ρ t v)
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h

/-- **Cuspidal detection.** A nonzero vector of the Levi Gelfand–Graev representation with
quasicuspidal cyclic span is detected by an intertwiner to an external tensor product of
irreducible supercuspidal representations, with carriers in an arbitrary universe. -/
theorem leviGelfandGraev_cuspidalDetection (hn : 0 < n) :
    letI := T.topology
    letI := topologicalRing T
    ∀ (x : LeviGelfandGraevFunctions (F := F.Carrier) B ψ), x ≠ 0 →
      IsLeviQuasicuspidal B (Cyclic.orbitSpan (leviGelfandGraev B ψ) x).toRepresentation →
      ∃ (A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := B.size i))
        (Φ : (leviGelfandGraev B ψ).IntertwiningMap
          (B.blockTensor fun i => (A i).obj.representation)), Φ x ≠ 0 := by
  classical
  let := T.topology
  let := topologicalRing T
  let := T.leviTopologicalGroup B
  intro x hx hxq
  let ρ := leviGelfandGraev (F := F.Carrier) B ψ
  let ν := leviDeterminantNorm T B
  have hP := leviUpperUnipotent_le_ker T B
  have hν := isOpen_ker_leviDeterminantNorm T B
  -- a nonzero graded piece and a translate of it into degree one
  obtain ⟨d, hd⟩ : ∃ d, gradedPiece hP hν d x ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [← sum_gradedPiece hP hν x]
    exact Finset.sum_eq_zero fun d _ => h d
  obtain ⟨t, rfl⟩ : ∃ t, ν t = d := by
    by_contra h
    push Not at h
    apply hd
    apply compactFunctions_ext
    intro g
    rw [eval_gradedPiece, ite_eq_right_iff.mpr (fun hg => absurd hg (h g))]
    rfl
  let z := gradedPiece hP hν (ν t) x
  let y := ρ t z
  have hy0 : y ≠ 0 := by
    intro h
    apply hd
    have := congrArg (ρ t⁻¹) h
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  have hyq : IsLeviQuasicuspidal B (Cyclic.orbitSpan ρ y).toRepresentation := by
    change IsLeviQuasicuspidal B (Cyclic.orbitSpan ρ (ρ t z)).toRepresentation
    rw [orbitSpan_translate]
    exact isLeviQuasicuspidal_orbitSpan_gradedPiece T B ψ x (ν t) hxq
  -- a map intertwining the determinant-unit subgroup
  let A : SmoothRep.{0, uF, uF} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of ρ (compactInduced_smooth _ _)
  obtain ⟨π, f0, hπirr, hπq, hf0, hf0y⟩ := exists_determinantUnit_map_ne_zero T B A y hyq hy0
  -- the twist trick
  obtain ⟨χ, hχ⟩ := exists_twistedExtension_ne_zero ν π.representation f0 hf0 hP hν
    (separating_characters (k := B.length)) x t hf0y
  let χ' : B.Levi F.Carrier →* ℂˣ := (χ.comp ν)⁻¹
  have hker : ν.ker ≤ χ'.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [χ', hg]
  have hχ' : IsOpen (χ'.ker : Set (B.Levi F.Carrier)) :=
    Subgroup.isOpen_mono hker hν
  let π' := π.twist χ' hχ'
  have hirr : π'.IsIrreducible := (SmoothRep.isIrreducible_twist_iff χ' hχ' π).mpr hπirr
  have hq : IsLeviQuasicuspidal B π'.representation := by
    intro R hR
    exact (Jacquet.subsingleton_coinvariants_twist_iff χ' π.representation
      ((refinedUnipotent_le_ker T B R).trans hker)).mpr (hπq R hR)
  have hadm : π'.IsAdmissible :=
    LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T B π' hirr hq
  obtain ⟨Afam, ⟨e⟩⟩ := padicLeviCuspidalFactorization.{uF, uF, uW} p F T n hn B π' hirr
    ⟨hadm, hq⟩
  refine ⟨Afam, e.toIntertwiningMap.comp (twistedExtension ν π.representation f0 hf0 hP hν χ), ?_⟩
  intro h0
  apply hχ
  apply e.injective
  rw [map_zero]
  exact h0

end Detection

end Langlands.RankinSelberg.SupercuspidalCompleteness
