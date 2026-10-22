import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.CuspidalSupport.LeviAssociation
import Langlands.Representation.CuspidalSupport.AssociationForwardStatement
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Group.GL.SingleBlock

/-! Weyl transport along composite permutations, and the reduction of factor
matching for associated cuspidal data to adjacent block swaps. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV uW u

section Transport

variable {F : Type uF} [Field F] {n : ℕ} {B C D : BlockShape n}
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Inverse Levi conjugations compose like the permutations. -/
theorem leviConjugation_symm_symm {w v u : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (hv : ConjugatesLevi (F := F) C D v)
    (hu : ConjugatesLevi (F := F) B D u) (h : v * w = u) (m : D.Levi F) :
    (leviConjugation B C w hw).symm ((leviConjugation C D v hv).symm m) =
      (leviConjugation B D u hu).symm m := by
  subst h
  apply B.leviEmbedding_injective F
  rw [leviConjugation_symm_embedding, leviConjugation_symm_embedding,
    leviConjugation_symm_embedding, map_mul, mul_inv_rev]
  simp only [mul_assoc]

/-- Transport along two conjugating permutations is transport along their product. -/
theorem transport_transport {w v u : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (hv : ConjugatesLevi (F := F) C D v)
    (hu : ConjugatesLevi (F := F) B D u) (h : v * w = u)
    (ρ : Representation ℂ (B.Levi F) V) :
    transport C D v hv (transport B C w hw ρ) = transport B D u hu ρ := by
  ext m x
  change ρ ((leviConjugation B C w hw).symm ((leviConjugation C D v hv).symm m)) x =
    ρ ((leviConjugation B D u hu).symm m) x
  rw [leviConjugation_symm_symm hw hv hu h]

/-- The Levi element given by a block-preserving permutation matrix. -/
def weylLeviElement (b : Equiv.Perm (Fin n)) (hb : b ∈ blockWeyl B) : B.Levi F :=
  (B.leviEquiv F).symm ⟨permutation n F b, (permutation_mem_levi_iff B b).mpr hb⟩

theorem leviEmbedding_weylLeviElement (b : Equiv.Perm (Fin n)) (hb : b ∈ blockWeyl B) :
    B.leviEmbedding F (weylLeviElement (F := F) b hb) = permutation n F b := by
  change ((B.leviEquiv F) ((B.leviEquiv F).symm _) : GeneralLinear n F) = _
  rw [MulEquiv.apply_symm_apply]

/-- Self-conjugation by a block-preserving permutation is inner in the Levi. -/
theorem leviConjugation_symm_weyl (b : Equiv.Perm (Fin n)) (hb : b ∈ blockWeyl B)
    (hb' : ConjugatesLevi (F := F) B B b) (m : B.Levi F) :
    (leviConjugation B B b hb').symm m =
      (weylLeviElement (F := F) b hb)⁻¹ * m * weylLeviElement (F := F) b hb := by
  apply B.leviEmbedding_injective F
  rw [leviConjugation_symm_embedding, map_mul, map_mul, map_inv,
    leviEmbedding_weylLeviElement]

/-- Transport by a block-preserving permutation is equivalent to the original
representation, through the action of the corresponding Levi element. -/
def transportWeylEquiv (b : Equiv.Perm (Fin n)) (hb : b ∈ blockWeyl B)
    (hb' : ConjugatesLevi (F := F) B B b) (ρ : Representation ℂ (B.Levi F) V) :
    (transport B B b hb' ρ).Equiv ρ :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (ρ (weylLeviElement (F := F) b hb))
      (ρ (weylLeviElement (F := F) b hb)⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_eq_id]))
    (fun m' => by
      apply LinearMap.ext
      intro x
      change ρ (weylLeviElement (F := F) b hb)
          (ρ ((leviConjugation B B b hb').symm m') x) =
        ρ m' (ρ (weylLeviElement (F := F) b hb) x)
      rw [leviConjugation_symm_weyl b hb hb', ← Module.End.mul_apply, ← map_mul,
        ← Module.End.mul_apply, ← map_mul]
      simp only [mul_assoc, mul_inv_cancel_left])

end Transport

section GroupEquiv

variable {k : Type u} [Field k] {G : Type uF} {H : Type uW} [Monoid G] [Monoid H]
  {V : Type uV} [AddCommGroup V] [Module k V]

/-- Invariant subspaces do not change under pullback along a surjective
monoid homomorphism. -/
def subrepresentationCompOrderIso (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hf g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (f h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_iff (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) ↔ Representation.IsIrreducible ρ :=
  (subrepresentationCompOrderIso ρ f hf).isSimpleOrder_iff

theorem isIrreducible_comp_mulEquiv_iff {G : Type uF} {H : Type uW} [Group G] [Group H]
    (ρ : Representation k G V) (e : H ≃* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) ↔ Representation.IsIrreducible ρ :=
  isIrreducible_comp_iff ρ e.toMonoidHom e.surjective

end GroupEquiv

section TransportProperties

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_transport (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) (ρ : Representation ℂ (B.Levi F) V) :
    Representation.IsIrreducible (transport B C w hw ρ) ↔ Representation.IsIrreducible ρ :=
  isIrreducible_comp_mulEquiv_iff ρ (leviConjugation B C w hw).symm

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Levi conjugation as an equivalence of topological groups. -/
def leviConjugationContinuous (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) : B.Levi F ≃ₜ* C.Levi F where
  toMulEquiv := leviConjugation B C w hw
  continuous_toFun := continuous_leviConjugation B C w hw
  continuous_invFun := continuous_leviConjugation_symm B C w hw

theorem isAdmissible_transport (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) {ρ : Representation ℂ (B.Levi F) V}
    (hρ : IsAdmissible ρ) : IsAdmissible (transport B C w hw ρ) :=
  isAdmissible_comp_continuousMulEquiv ρ (leviConjugationContinuous w hw).symm hρ

end TransportProperties

section BlockPermutationTransport

variable {F : Type uF} [Field F] {n : ℕ} (B : BlockShape n) (e : Equiv.Perm (Fin B.length))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Conjugation by the canonical block reordering reorders the Levi factors. -/
theorem leviConjugation_blockPermutation_apply
    (h : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e)) (m : B.Levi F)
    (i : Fin B.length) :
    leviConjugation B (B.permute e) (B.blockPermutation e) h m i = m (e i) := by
  apply Units.ext
  ext x y
  have h1 := (B.permute e).leviEmbedding_apply_same F
    (leviConjugation B (B.permute e) (B.blockPermutation e) h m) i x y
  rw [leviConjugation_embedding, permutation_conjugate_entry, Equiv.Perm.inv_def] at h1
  have hx := B.blockPermutation_symm_index e i x
  have hy := B.blockPermutation_symm_index e i y
  rw [← h1, hx, hy]
  exact B.leviEmbedding_apply_same F m (e i) x y

theorem leviConjugation_symm_blockPermutation_apply
    (h : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e))
    (m : (B.permute e).Levi F) (i : Fin B.length) :
    (leviConjugation B (B.permute e) (B.blockPermutation e) h).symm m (e i) = m i := by
  conv_rhs => rw [← MulEquiv.apply_symm_apply
    (leviConjugation B (B.permute e) (B.blockPermutation e) h) m]
  rw [leviConjugation_blockPermutation_apply]

/-- Pulling back a product of blockwise subgroups along the inverse block
reordering gives the product over the reindexed refinement. -/
theorem map_pi_blockPermutation
    (h : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e))
    (K : ∀ {m : ℕ}, BlockShape m → Subgroup (GeneralLinear m F))
    (S : ∀ i, BlockShape (B.size (e i))) :
    (Subgroup.pi Set.univ (fun i => K (S i)) : Subgroup ((B.permute e).Levi F)).map
        (leviConjugation B (B.permute e) (B.blockPermutation e) h).symm.toMonoidHom =
      Subgroup.pi Set.univ
        (fun j => K (Equiv.piCongrLeft (fun j => BlockShape (B.size j)) e S j)) := by
  ext m
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_pi, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]
  rw [← (e.forall_congr_right (q := fun j =>
    m j ∈ K (Equiv.piCongrLeft (fun j => BlockShape (B.size j)) e S j)))]
  refine forall_congr' fun (i : Fin B.length) => ?_
  have hL := leviConjugation_blockPermutation_apply B e h m i
  have hS := Equiv.piCongrLeft_apply_apply (P := fun j => BlockShape (B.size j)) (e := e) S i
  change leviConjugation B (B.permute e) (B.blockPermutation e) h m i ∈ K (S i) ↔
    m (e i) ∈ K (Equiv.piCongrLeft (fun j => BlockShape (B.size j)) e S (e i))
  rw [hL, hS]
  exact Iff.rfl

/-- Transport along the canonical block reordering preserves quasicuspidality. -/
theorem isLeviQuasicuspidal_transport_blockPermutation
    (h : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e))
    {ρ : Representation ℂ (B.Levi F) V} (hρ : IsLeviQuasicuspidal B ρ) :
    IsLeviQuasicuspidal (B.permute e) (transport B (B.permute e) (B.blockPermutation e) h ρ) := by
  intro S hS
  let L := leviConjugation B (B.permute e) (B.blockPermutation e) h
  let S' : BlockRefinement B := Equiv.piCongrLeft (fun j => BlockShape (B.size j)) e S
  have hU : (refinedUnipotent F (B.permute e) S).map L.symm.toMonoidHom =
      refinedUnipotent F B S' :=
    map_pi_blockPermutation B e h (fun T => T.unipotentSubgroup F) S
  have hP : (refinedParabolic F (B.permute e) S).map L.symm.toMonoidHom =
      refinedParabolic F B S' :=
    map_pi_blockPermutation B e h (fun T => T.parabolic F) S
  have hS' : refinedParabolic F B S' ≠ ⊤ := by
    intro htop
    apply hS
    rw [eq_top_iff]
    intro x _
    have hx : L.symm x ∈ (refinedParabolic F (B.permute e) S).map L.symm.toMonoidHom := by
      rw [hP, htop]
      exact Subgroup.mem_top _
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply] at hx
  have hc := (Jacquet.coinvariantsMapEquiv ρ L.symm.toMonoidHom
    (refinedUnipotent F (B.permute e) S)).toEquiv.subsingleton_congr
  rw [hU] at hc
  exact hc.mpr (hρ S' hS')

end BlockPermutationTransport

section Swaps

/-- Adjacent transpositions of `Fin L`, indexed by the smaller natural position. -/
theorem closure_adjacent_swaps (L : ℕ) :
    Submonoid.closure {s : Equiv.Perm (Fin L) |
      ∃ (j : ℕ) (hj : j + 1 < L), s = Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩} = ⊤ := by
  cases L with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    apply top_unique
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ m]
    apply Submonoid.closure_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.val, by omega, rfl⟩

theorem val_swap_adjacent {L j : ℕ} (hj : j + 1 < L) (x : Fin L) :
    ((Equiv.swap (⟨j, by omega⟩ : Fin L) ⟨j + 1, hj⟩ x : Fin L) : ℕ) =
      Equiv.swap j (j + 1) (x : ℕ) :=
  Fin.val_injective.map_swap _ _ x

end Swaps

section LengthOne

variable {G : Type uF} [Group G]

/-- The filtration `0 ⊆ A` of length one. -/
def lengthOneFiltration (A : Rep.{uV} ℂ G) : ObjectRepFiltration A 1 :=
  ObjectRepFiltration.ofSubrepresentations (fun i => if i = 0 then ⊥ else ⊤)
    (by
      intro i j hij
      by_cases hi : i = 0
      · simp only [hi, ↓reduceIte]
        exact bot_le
      · have hj : j ≠ 0 := fun hj => hi (le_antisymm (hj ▸ hij) (Fin.zero_le _))
        simp only [hi, hj, ↓reduceIte, le_refl])
    (by simp) (by simp)

theorem lengthOneFiltration_succ (A : Rep.{uV} ℂ G) :
    (lengthOneFiltration A).subrepresentation (0 : Fin 1).succ = ⊤ := by
  change (if (0 : Fin 1).succ = 0 then ⊥ else ⊤) = ⊤
  simp

/-- The representation maps onto the graded piece of `0 ⊆ A`. -/
def lengthOneGradedMap (A : Rep.{uV} ℂ G) :
    A.ρ.IntertwiningMap ((lengthOneFiltration A).gradedRepresentation 0).ρ :=
  ((lengthOneFiltration A).gradedProjection 0).hom.comp
    { toLinearMap := LinearMap.codRestrict _ LinearMap.id
        (fun v => by rw [lengthOneFiltration_succ]; trivial)
      isIntertwining' := fun _ => rfl }

theorem lengthOneGradedMap_bijective (A : Rep.{uV} ℂ G) :
    Function.Bijective (lengthOneGradedMap A) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    change v ∈ (lengthOneFiltration A).subrepresentation 0 at hmem
    rw [ObjectRepFiltration.subrepresentation_zero] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · intro x
    obtain ⟨⟨v, hv⟩, rfl⟩ := (lengthOneFiltration A).gradedProjection_surjective 0 x
    exact ⟨v, rfl⟩

/-- The graded piece of `0 ⊆ A` is `A` itself. -/
def lengthOneGradedEquiv (A : Rep.{uV} ℂ G) :
    A.ρ.Equiv ((lengthOneFiltration A).gradedRepresentation 0).ρ :=
  (lengthOneGradedMap A).ofBijective (lengthOneGradedMap_bijective A)

/-- An irreducible representation and any representation equivalent to it have
the same composition factors, through their length-one series. -/
theorem haveSameJordanHolderFactors_of_isIrreducible {A : Rep.{uV} ℂ G} {A' : Rep.{uW} ℂ G}
    (hA : Representation.IsIrreducible A.ρ) (e : A.ρ.Equiv A'.ρ) :
    HaveSameJordanHolderFactors A A' := by
  refine ⟨1, lengthOneFiltration A, lengthOneFiltration A', ?_, ?_, 1, ?_⟩
  · intro i
    rw [Fin.fin_one_eq_zero i]
    exact (isIrreducible_iff_of_equiv (lengthOneGradedEquiv A)).mp hA
  · intro i
    rw [Fin.fin_one_eq_zero i]
    exact (isIrreducible_iff_of_equiv (e.trans (lengthOneGradedEquiv A'))).mp hA
  · intro i
    rw [Fin.fin_one_eq_zero i]
    exact ⟨(lengthOneGradedEquiv A).symm.trans (e.trans (lengthOneGradedEquiv A'))⟩

end LengthOne

section SingleBlock

variable {n : ℕ}

theorem length_pos_of_pos (B : BlockShape n) (hn : 0 < n) : 0 < B.length := by
  apply Nat.pos_of_ne_zero
  intro h
  have : IsEmpty (Fin B.length) := by rw [h]; infer_instance
  have hs := B.sum_eq
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
  omega

/-- Two one-block shapes of the same rank are equal. -/
theorem eq_of_length_eq_one {B C : BlockShape n} (hB : B.length = 1) (hC : C.length = 1) :
    B = C := by
  have hsB := B.singleBlock_size hB
  have hsC := C.singleBlock_size hC
  obtain ⟨lB, sB, pB, eB⟩ := B
  obtain ⟨lC, sC, pC, eC⟩ := C
  dsimp only at hB hC hsB hsC
  subst hB hC
  have : sB = sC := funext fun i => (hsB i).trans (hsC i).symm
  subst this
  rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- For one block the standard parabolic is everything, and normalized
induction of an irreducible smooth representation is irreducible. -/
theorem isIrreducible_normalizedParabolicInduced_singleBlock (B : BlockShape n)
    (hB : B.length = 1) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσs : letI := T.topology
      IsSmooth σ) (hσ : Representation.IsIrreducible σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.IsIrreducible (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  have hP : B.parabolic F.Carrier = ⊤ := B.singleBlock_parabolic_eq_top hB F.Carrier
  let χ := (B.inflateCharacter (T.leviHalfCharacter B)).toMonoidHom
  let σP : Representation ℂ (B.parabolic F.Carrier) V :=
    twist χ (σ.comp (B.leviProjection F.Carrier))
  let c : GeneralLinear n F.Carrier →* B.parabolic F.Carrier :=
    (MonoidHom.id _).codRestrict (B.parabolic F.Carrier) (fun g => hP ▸ Subgroup.mem_top g)
  have hc : Continuous c := continuous_id.subtype_mk _
  have hσP : IsSmooth σP :=
    (isSmooth_twist_iff χ _ (B.inflateCharacter (T.leviHalfCharacter B)).isOpen_ker).mpr
      (isSmooth_comp _ (B.leviProjectionContinuous F.Carrier).continuous hσs)
  have hτ : IsSmooth (σP.comp c) := isSmooth_comp c hc hσP
  have E := fullInductionEquiv (B.parabolic F.Carrier) σP (σP.comp c) hP
    (Representation.Equiv.refl σP) hτ
  have hproj : Function.Surjective (B.leviProjection F.Carrier) := fun m =>
    ⟨B.leviInParabolic F.Carrier m, B.leviProjection_section F.Carrier m⟩
  have hcs : Function.Surjective c := fun q => ⟨q.val, rfl⟩
  have hirr : Representation.IsIrreducible (σP.comp c) :=
    (isIrreducible_comp_iff σP c hcs).mpr ((isIrreducible_twist_iff χ _).mpr
      ((isIrreducible_comp_iff σ _ hproj).mpr hσ))
  exact (isIrreducible_iff_of_equiv E).mpr hirr

/-- The case of at most one block. -/
theorem associatedCuspidalInductionFactors_of_length_lt_two (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      B.length < 2 →
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hB hσ _ _ _ hassoc
  obtain ⟨w, hw, ⟨φ⟩⟩ := hassoc
  have hB1 : B.length = 1 := by have := length_pos_of_pos B hn; omega
  have hC1 : C.length = 1 := by
    obtain ⟨e, he⟩ := exists_blockMap_of_conjugatesLevi hw
    have hle : ∀ k : Fin C.length, (k : ℕ) < 1 := by
      intro k
      have h := he (w.symm (C.index k ⟨0, C.positive k⟩))
      rw [Equiv.apply_symm_apply, blockIndex_index] at h
      rw [h, ← hB1]
      exact (e.symm _).isLt
    have := length_pos_of_pos C hn
    by_contra hne
    exact absurd (hle ⟨1, by omega⟩) (by simp)
  obtain rfl := eq_of_length_eq_one hB1 hC1
  have hb : w ∈ blockWeyl B := fun a => Fin.ext (by
    have h1 := (blockIndex B (w a)).isLt
    have h2 := (blockIndex B a).isLt
    omega)
  exact haveSameJordanHolderFactors_of_isIrreducible
    (isIrreducible_normalizedParabolicInduced_singleBlock T B hB1 σ.representation
      σ.isSmooth hσ)
    (T.normalizedParabolicInducedEquiv B
      ((transportWeylEquiv w hb hw σ.representation).symm.trans φ))

end SingleBlock

section Reduction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)

/-- One adjacent swap extends factor matching from block map `e` to `e * s`.
The induction hypothesis keeps the target carrier universe of the source,
while the conclusion allows an arbitrary target carrier universe. -/
theorem factors_step
    (hE : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (htrans : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uW} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (B : BlockShape n) (e : Equiv.Perm (Fin B.length))
    (ih : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w),
        IsMinimalRepresentative B C w →
        (∀ a, (blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ)) →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (j : ℕ) (hj : j + 1 < B.length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (C : BlockShape n) (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) B C w),
      IsMinimalRepresentative B C w →
      (∀ a, (blockIndex C (w a) : ℕ) =
        ((e * Equiv.swap (⟨j, by omega⟩ : Fin B.length) ⟨j + 1, hj⟩).symm
          (blockIndex B a) : ℕ)) →
      ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
        (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
        σ.IsIrreducible → IsLeviCuspidal B σ.representation →
        τ.IsIrreducible → IsLeviCuspidal C τ.representation →
        Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedParabolicInduced B σ.representation))
          (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro C w hw hmin hblock σ τ hσ hσc hτ hτc hφ
  obtain ⟨φ⟩ := hφ
  set s : Equiv.Perm (Fin B.length) := Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ with hs
  have hsymm : ∀ x, (e * s).symm x = s (e.symm x) := fun x => by
    rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, hs, Equiv.swap_apply_self,
      Equiv.apply_symm_apply]
  let B' := B.permute e
  let w' := B.blockPermutation e
  have hw' : ConjugatesLevi (F := F.Carrier) B B' w' := conjugatesLevi_blockPermutation B e
  have hmin' : IsMinimalRepresentative B B' w' := isMinimalRepresentative_blockPermutation B e
  let v := w * w'⁻¹
  have hvblock : ∀ a, (blockIndex C (v a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B' a : ℕ) := by
    intro a
    obtain ⟨b, rfl⟩ := w'.surjective a
    have hva : v (w' b) = w b := by
      simp only [v, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hva, hblock, hsymm, blockIndex_blockPermutation, hs, val_swap_adjacent]
  have hv : ConjugatesLevi (F := F.Carrier) B' C v :=
    conjugatesLevi_of_blockIndex v (fun i => Equiv.swap j (j + 1) (i : ℕ))
      ((Equiv.injective _).comp Fin.val_injective) hvblock
  have hvmin : IsMinimalRepresentative B' C v := by
    apply isMinimalRepresentative_mul_inv hmin hmin'
    · intro a b hab
      rw [blockIndex_blockPermutation, blockIndex_blockPermutation] at hab
      exact e.symm.injective hab
    · intro a b hab
      exact blockIndex_eq_of_conjugatesLevi_apply hw hab
  let σ' : SmoothRep.{0, uF, uV} ℂ (B'.Levi F.Carrier) :=
    SmoothRep.of (transport B B' w' hw' σ.representation)
      (isSmooth_transport B B' w' hw' σ.isSmooth)
  have hσ' : σ'.IsIrreducible := (isIrreducible_transport w' hw' _).mpr hσ
  have hσ'c : IsLeviCuspidal B' σ'.representation :=
    ⟨isAdmissible_transport w' hw' hσc.1,
      isLeviQuasicuspidal_transport_blockPermutation B e hw' hσc.2⟩
  have h1 := ih B' w' hw' hmin' (fun a => by rw [blockIndex_blockPermutation]) σ σ'
    hσ hσc hσ' hσ'c ⟨Representation.Equiv.refl _⟩
  have hvw : v * w' = w := by simp only [v, inv_mul_cancel_right]
  have h2 := hE B' C v hv j hj hvblock hvmin σ' τ hσ' hσ'c hτ hτc
    ⟨by
      change (transport B' C v hv (transport B B' w' hw' σ.representation)).Equiv _
      rw [transport_transport hw' hv hw hvw]
      exact φ⟩
  exact htrans _ _ _ h1 h2

/-- Factor matching along every block map, for a source with at least two
blocks, with source and target carriers in the same universe. -/
theorem factors_of_blockMap
    (hE : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (htrans : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (B : BlockShape n) (hB : 2 ≤ B.length) (e : Equiv.Perm (Fin B.length)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (C : BlockShape n) (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) B C w),
      IsMinimalRepresentative B C w →
      (∀ a, (blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ)) →
      ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
        (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
        σ.IsIrreducible → IsLeviCuspidal B σ.representation →
        τ.IsIrreducible → IsLeviCuspidal C τ.representation →
        Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedParabolicInduced B σ.representation))
          (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  refine Submonoid.induction_of_closure_eq_top_right (closure_adjacent_swaps B.length) e ?_ ?_
  · have h0 : 0 + 1 < B.length := by omega
    have hbase := factors_step F T n hE htrans B
      (Equiv.swap (⟨0, by omega⟩ : Fin B.length) ⟨0 + 1, h0⟩)
      (fun C w hw hmin hblock σ τ hσ hσc hτ hτc hφ =>
        hE B C w hw 0 h0 (fun a => by
          rw [hblock, Equiv.symm_swap]
          exact val_swap_adjacent h0 _) hmin σ τ hσ hσc hτ hτc hφ) 0 h0
    rw [Equiv.swap_mul_self] at hbase
    exact hbase
  · rintro x _ ⟨j, hj, rfl⟩ ih
    exact factors_step F T n hE htrans B x ih j hj

/-- The reduction of factor matching for associated irreducible cuspidal data
to adjacent block swaps and factor-matching transitivity. -/
theorem associatedCuspidalInductionFactors_of_adjacent
    (hEV : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (hEW : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
        (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
        (∀ a, (blockIndex C (w a) : ℕ) = Equiv.swap j (j + 1) (blockIndex B a : ℕ)) →
        IsMinimalRepresentative B C w →
        ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
          (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
          σ.IsIrreducible → IsLeviCuspidal B σ.representation →
          τ.IsIrreducible → IsLeviCuspidal C τ.representation →
          Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
          HaveSameJordanHolderFactors
            (Rep.of (T.normalizedParabolicInduced B σ.representation))
            (Rep.of (T.normalizedParabolicInduced C τ.representation)))
    (htransV : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (htransW : ∀ (A A' : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier))
      (A'' : Rep.{max uF uW} ℂ (GeneralLinear n F.Carrier)),
      HaveSameJordanHolderFactors A A' → HaveSameJordanHolderFactors A' A'' →
        HaveSameJordanHolderFactors A A'')
    (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hσ hσc hτ hτc hassoc
  by_cases hB : B.length < 2
  · exact associatedCuspidalInductionFactors_of_length_lt_two T n hn B C σ τ hB hσ hσc hτ hτc
      hassoc
  replace hB : 2 ≤ B.length := not_lt.mp hB
  obtain ⟨w, hw, ⟨φ⟩⟩ := hassoc
  obtain ⟨⟨⟨v, hvmin⟩, hv⟩, ⟨⟨b, hb⟩, hwvb⟩, -⟩ := minimalConjugatingCosets w hw
  have hbB : ConjugatesLevi (F := F.Carrier) B B b :=
    conjugatesLevi_of_blockIndex b (fun i => (i : ℕ)) Fin.val_injective
      (fun a => by rw [hb a])
  obtain ⟨e, he⟩ := exists_blockMap_of_conjugatesLevi hv
  have hiso : (transport B C v hv σ.representation).Equiv τ.representation := by
    refine (transportEquiv v hv (transportWeylEquiv b hb hbB σ.representation).symm).trans ?_
    rw [transport_transport hbB hv hw hwvb.symm]
    exact φ
  have h0 : 0 + 1 < B.length := by omega
  have hall := factors_of_blockMap F T n hEV htransV B hB
    (e * Equiv.swap (⟨0, by omega⟩ : Fin B.length) ⟨0 + 1, h0⟩)
  refine factors_step F T n hEW htransW B _ hall 0 h0 C v hv hvmin (fun a => ?_)
    σ τ hσ hσc hτ hτc ⟨hiso⟩
  rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  exact he a

end Reduction

end Langlands.CuspidalSupport
