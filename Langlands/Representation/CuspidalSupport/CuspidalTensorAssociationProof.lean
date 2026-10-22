import Langlands.Representation.CuspidalSupport.BlockMap
import Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.Representation.Geometric.WeylUniquenessProof
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Association of external tensor products of supercuspidal factors forces
equality of their multisets of cuspidal data. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.CuspidalSupport

section FactorEquivalence

variable {K : Type*} [Field K] {G : Type*} [Group G]

/-- Pulling back along a surjective homomorphism preserves irreducibility. -/
theorem isIrreducible_comp_of_surjective {H : Type*} [Group H]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K H V) [hρ : ρ.IsIrreducible] (f : G →* H)
    (hf : Function.Surjective f) : Representation.IsIrreducible (ρ.comp f) := by
  let e : Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun h v hv => by
        obtain ⟨g, rfl⟩ := hf h
        exact S.apply_mem_toSubmodule g hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun S => rfl
      right_inv := fun S => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

/-- The carrier of an irreducible representation is nontrivial. -/
theorem nontrivial_of_isIrreducible {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) [hρ : ρ.IsIrreducible] : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    (Subrepresentation.ext (Subsingleton.elim _ _))

/-- An equivalence of representations restricts along any homomorphism. -/
def equivComp {H : Type*} [Group H] {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {ρ : Representation K H V} {σ : Representation K H W}
    (E : ρ.Equiv σ) (f : G →* H) : Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk E.toLinearEquiv fun g => by
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap (f g) v

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  {W : κ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]

omit [DecidableEq ι] in
/-- Over a field, a pure tensor of basis vectors is nonzero. -/
theorem exists_tprod_ne_zero [∀ i, Nontrivial (V i)] :
    ∃ v : ∀ i, V i, PiTensorProduct.tprod K v ≠ 0 := by
  let b := fun i => Module.Basis.ofVectorSpace K (V i)
  let p : ∀ i, Module.Basis.ofVectorSpaceIndex K (V i) := fun i =>
    Classical.choice (b i).index_nonempty
  refine ⟨fun i => b i (p i), ?_⟩
  rw [← Basis.piTensorProduct_apply]
  exact (Basis.piTensorProduct b).ne_zero p

omit [Fintype κ] in
/-- A nonzero tensor has a nonzero partial contraction onto a chosen factor,
by a linear map commuting with every operator applied to that factor. -/
theorem exists_factor_contraction (j₀ : κ) (x : ⨂[K] j, W j) (hx : x ≠ 0) :
    ∃ c : (⨂[K] j, W j) →ₗ[K] W j₀, c x ≠ 0 ∧
      ∀ (f : W j₀ →ₗ[K] W j₀) (w : ∀ j, W j),
        c (PiTensorProduct.tprod K (Function.update w j₀ (f (w j₀)))) =
          f (c (PiTensorProduct.tprod K w)) := by
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor K W j₀
  let b := Module.Basis.ofVectorSpace K (⨂[K] (j : ({j₀}ᶜ : Set κ)), W j)
  let _ : DecidableEq (Module.Basis.ofVectorSpaceIndex K
    (⨂[K] (j : ({j₀}ᶜ : Set κ)), W j)) := Classical.decEq _
  let d := TensorProduct.equivFinsuppOfBasisLeft (N := W j₀) b
  have hy : d (e x) ≠ 0 := by
    intro h
    apply hx
    apply e.injective
    apply d.injective
    rw [h, map_zero, map_zero]
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.mp hy
  refine ⟨(Finsupp.lapply t) ∘ₗ d.toLinearMap ∘ₗ e.toLinearMap, ht, ?_⟩
  intro f w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply, e, d,
    PiTensorProduct.equivPiTensorComplSingletonTensor_tprod,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Function.update_self, map_smul]
  congr 4
  funext j
  exact Function.update_of_ne j.property _ _

omit [Fintype ι] in
/-- The external action of an element supported in one coordinate changes
only that tensor factor. -/
theorem external_mulSingle_tprod {H : ι → Type*} [∀ i, Group (H i)]
    (π : ∀ i, Representation K (H i) (V i)) (i₀ : ι) (g : H i₀) (v : ∀ i, V i) :
    FiniteTensor.external π (Pi.mulSingle i₀ g) (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (Function.update v i₀ (π i₀ g (v i₀))) := by
  rw [FiniteTensor.external_tprod]
  congr 1
  funext i
  by_cases hi : i = i₀
  · subst hi
    rw [Function.update_self, Pi.mulSingle_eq_same]
  · rw [Function.update_of_ne hi, Pi.mulSingle_eq_of_ne hi, map_one, Module.End.one_apply]

variable [∀ i, Nontrivial (V i)]

omit [Fintype κ] in
/-- If a group acts on one factor of each of two finite tensor products, through
irreducible representations, then an equivalence of the two tensor products
gives an equivalence of the two acting factors. -/
theorem nonempty_equiv_of_factor_actions {i₀ : ι} {j₀ : κ}
    {ρ : Representation K G (V i₀)} {σ : Representation K G (W j₀)}
    [hρ : ρ.IsIrreducible] [hσ : σ.IsIrreducible]
    {πV : Representation K G (⨂[K] i, V i)} {πW : Representation K G (⨂[K] j, W j)}
    (hV : ∀ g v, πV g (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (Function.update v i₀ (ρ g (v i₀))))
    (hW : ∀ g w, πW g (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (Function.update w j₀ (σ g (w j₀))))
    (E : πV.Equiv πW) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero (K := K) (V := V)
  have hx : E (PiTensorProduct.tprod K v) ≠ 0 :=
    (map_ne_zero_iff E (EquivLike.injective E)).mpr hv
  obtain ⟨c, hc, hcf⟩ := exists_factor_contraction j₀ _ hx
  let e : V i₀ →ₗ[K] ⨂[K] i, V i := (PiTensorProduct.tprod K).toLinearMap v i₀
  have he : ∀ g u, e (ρ g u) = πV g (e u) := by
    intro g u
    simp only [e, MultilinearMap.toLinearMap_apply, hV, Function.update_self,
      Function.update_idem]
  have hcW : ∀ g y, c (πW g y) = σ g (c y) := by
    intro g y
    have h : c ∘ₗ πW g = σ g ∘ₗ c := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hW]
      exact hcf (σ g) w
    exact LinearMap.congr_fun h y
  let T : ρ.IntertwiningMap σ :=
    { toLinearMap := c ∘ₗ E.toLinearMap ∘ₗ e
      isIntertwining' := fun g => by
        ext u
        simp only [LinearMap.comp_apply, he]
        rw [Representation.Equiv.coe_toLinearMap, ← hcW]
        congr 1
        exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g (e u) }
  have hT : T ≠ 0 := by
    intro h
    have h' := congrArg (fun f : ρ.IntertwiningMap σ => f (v i₀)) h
    apply hc
    simpa [T, e, Function.update_eq_self] using h'
  rcases Representation.IsIrreducible.bijective_or_eq_zero T with hb | h0
  · exact ⟨T.ofBijective hb⟩
  · exact absurd h0 hT

end FactorEquivalence

section Blocks

open GeneralLinear Geometric

variable {F : Type*} [Field F] {n : ℕ}

/-- Levi entries vanish between coordinates of different blocks. -/
theorem leviEmbedding_eq_zero_of_blockIndex_ne (D : BlockShape n) (m : D.Levi F)
    {a b : Fin n} (h : blockIndex D a ≠ blockIndex D b) :
    D.leviEmbedding F m a b = 0 := by
  obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq D (rfl : blockIndex D a = _)
  obtain ⟨y, hy⟩ := exists_index_of_blockIndex_eq D (rfl : blockIndex D b = _)
  rw [← hx, ← hy]
  exact D.leviEmbedding_apply_ne F m x y h

/-- Two coordinates of one block are linked by a nonzero Levi entry, namely
that of a block transposition matrix. -/
theorem exists_leviEmbedding_ne_zero (D : BlockShape n) {a b : Fin n}
    (h : blockIndex D a = blockIndex D b) :
    ∃ m : D.Levi F, D.leviEmbedding F m a b ≠ 0 := by
  obtain ⟨⟨i, x⟩, rfl⟩ := D.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := D.indexEquiv.surjective b
  change blockIndex D (D.index i x) = blockIndex D (D.index j y) at h
  rw [blockIndex_index, blockIndex_index] at h
  subst h
  refine ⟨Pi.mulSingle i (permutation _ F (Equiv.swap y x)), ?_⟩
  change D.leviEmbedding F _ (D.index i x) (D.index i y) ≠ 0
  rw [D.leviEmbedding_apply_same F, Pi.mulSingle_eq_same, permutation_entry,
    Equiv.swap_apply_left]
  simp

variable (B C : BlockShape n) {w : Equiv.Perm (Fin n)}

/-- Entries of the inverse Levi conjugation are permuted entries. -/
theorem leviConjugation_symm_entry (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F)
    (a b : Fin n) :
    B.leviEmbedding F ((leviConjugation B C w hw).symm m) a b =
      C.leviEmbedding F m (w a) (w b) := by
  rw [leviConjugation_symm_embedding, permutation_inv, mul_permutation_entry,
    permutation_mul_entry, inv_inv]

variable {B C}

/-- A conjugating permutation preserves the relation of lying in one block. -/
theorem blockIndex_eq_iff (hw : ConjugatesLevi (F := F) B C w) (a b : Fin n) :
    blockIndex C (w a) = blockIndex C (w b) ↔ blockIndex B a = blockIndex B b := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := exists_leviEmbedding_ne_zero (F := F) C h
    by_contra hne
    apply hm
    rw [← leviConjugation_symm_entry B C hw m a b]
    exact leviEmbedding_eq_zero_of_blockIndex_ne B _ hne
  · intro h
    obtain ⟨m, hm⟩ := exists_leviEmbedding_ne_zero (F := F) B h
    by_contra hne
    apply hm
    have he := leviConjugation_symm_entry B C hw (leviConjugation B C w hw m) a b
    rw [MulEquiv.symm_apply_apply] at he
    rw [he]
    exact leviEmbedding_eq_zero_of_blockIndex_ne C _ hne

theorem blockIndex_image (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length)
    (x : Fin (B.size i)) : blockIndex C (w (B.index i x)) = blockMap B C w i :=
  (blockIndex_eq_iff hw _ _).mpr (by rw [blockIndex_index, blockIndex_index])

theorem blockImage_bijective (hw : ConjugatesLevi (F := F) B C w) :
    Function.Bijective (blockMap B C w) := by
  constructor
  · intro i i' h
    have h' := (blockIndex_eq_iff hw _ _).mp h
    rwa [blockIndex_index, blockIndex_index] at h'
  · intro j
    obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq B
      (rfl : blockIndex B (w⁻¹ (C.index j ⟨0, C.positive j⟩)) = _)
    refine ⟨blockIndex B (w⁻¹ (C.index j ⟨0, C.positive j⟩)), ?_⟩
    rw [← blockIndex_image hw _ x, hx, Equiv.Perm.inv_def, Equiv.apply_symm_apply,
      blockIndex_index]

theorem exists_blockPosition (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length)
    (x : Fin (B.size i)) :
    ∃ y : Fin (C.size (blockMap B C w i)), C.index _ y = w (B.index i x) :=
  exists_index_of_blockIndex_eq C (blockIndex_image hw i x)

/-- The position, in its target block, of the image of a source coordinate. -/
def blockPosition (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length)
    (x : Fin (B.size i)) : Fin (C.size (blockMap B C w i)) :=
  (exists_blockPosition hw i x).choose

theorem index_blockPosition (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length)
    (x : Fin (B.size i)) : C.index _ (blockPosition hw i x) = w (B.index i x) :=
  (exists_blockPosition hw i x).choose_spec

theorem blockPosition_bijective (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    Function.Bijective (blockPosition hw i) := by
  constructor
  · intro x x' h
    have h' := congrArg (C.index _) h
    rw [index_blockPosition, index_blockPosition] at h'
    exact (B.index i).injective (w.injective h')
  · intro y
    have hb : blockIndex B (w⁻¹ (C.index _ y)) = i := by
      have h := (blockIndex_eq_iff hw (w⁻¹ (C.index _ y)) (B.index i ⟨0, B.positive i⟩)).mp
        (by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, blockIndex_index]; rfl)
      rwa [blockIndex_index] at h
    obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq B hb
    refine ⟨x, (C.index _).injective ?_⟩
    rw [index_blockPosition, hx, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

/-- The bijection between a source block and its target block. -/
def blockPositionEquiv (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    Fin (B.size i) ≃ Fin (C.size (blockMap B C w i)) :=
  Equiv.ofBijective _ (blockPosition_bijective hw i)

/-- Block entries of the inverse Levi conjugation. -/
theorem leviConjugation_symm_apply_entry (hw : ConjugatesLevi (F := F) B C w)
    (m : C.Levi F) (i : Fin B.length) (x y : Fin (B.size i)) :
    (leviConjugation B C w hw).symm m i x y =
      m (blockMap B C w i) (blockPosition hw i x) (blockPosition hw i y) := by
  have h := B.leviEmbedding_apply_same F ((leviConjugation B C w hw).symm m) i x y
  rw [leviConjugation_symm_entry, ← index_blockPosition hw i x,
    ← index_blockPosition hw i y, C.leviEmbedding_apply_same F] at h
  exact h.symm

theorem leviConjugation_symm_mulSingle_ne (hw : ConjugatesLevi (F := F) B C w)
    {i i' : Fin B.length} (h : i' ≠ i)
    (g : GeneralLinear (C.size (blockMap B C w i)) F) :
    (leviConjugation B C w hw).symm (Pi.mulSingle (blockMap B C w i) g) i' = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  rw [leviConjugation_symm_apply_entry,
    Pi.mulSingle_eq_of_ne ((blockImage_bijective hw).injective.ne h)]
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply,
    (blockPosition_bijective hw i').injective.eq_iff]

/-- The action on one source block of the target block subgroup. -/
def factorHom (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    GeneralLinear (C.size (blockMap B C w i)) F →* GeneralLinear (B.size i) F :=
  (Pi.evalMonoidHom (fun i => GeneralLinear (B.size i) F) i).comp
    ((leviConjugation B C w hw).symm.toMonoidHom.comp
      (MonoidHom.mulSingle (fun j => GeneralLinear (C.size j) F) (blockMap B C w i)))

theorem factorHom_apply_entry (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length)
    (g : GeneralLinear (C.size (blockMap B C w i)) F) (x y : Fin (B.size i)) :
    factorHom hw i g x y = g (blockPosition hw i x) (blockPosition hw i y) := by
  change (leviConjugation B C w hw).symm (Pi.mulSingle _ g) i x y = _
  rw [leviConjugation_symm_apply_entry, Pi.mulSingle_eq_same]

theorem factorHom_surjective (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length) :
    Function.Surjective (factorHom hw i) := by
  intro h
  refine ⟨reindex (blockPositionEquiv hw i) h, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  rw [factorHom_apply_entry]
  change h ((blockPositionEquiv hw i).symm (blockPositionEquiv hw i x))
    ((blockPositionEquiv hw i).symm (blockPositionEquiv hw i y)) = h x y
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The transported external action of the target block subgroup changes only
the corresponding source factor, through `factorHom`. -/
theorem external_leviConjugation_symm_mulSingle {K : Type*} [Field K]
    {V : Fin B.length → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (π : ∀ i, Representation K (GeneralLinear (B.size i) F) (V i))
    (hw : ConjugatesLevi (F := F) B C w) (i : Fin B.length)
    (g : GeneralLinear (C.size (blockMap B C w i)) F) (v : ∀ i, V i) :
    FiniteTensor.external π ((leviConjugation B C w hw).symm
        (Pi.mulSingle (blockMap B C w i) g)) (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (Function.update v i (π i (factorHom hw i g) (v i))) := by
  rw [FiniteTensor.external_tprod]
  congr 1
  funext i'
  by_cases hi : i' = i
  · subst hi
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne hi, leviConjugation_symm_mulSingle_ne hw hi, map_one,
      Module.End.one_apply]

end Blocks

section Datum

open GeneralLinear PadicField.TopologicalData

universe uV uF

/-- Supercuspidal representations of `GL_r(F)` are isomorphic when the first,
pulled back along a homomorphism permuting matrix entries by a coordinate
bijection, is equivalent to the second. -/
theorem nonempty_iso_of_equiv_comp_permuted {F : Type uF} [Field F] [TopologicalSpace F]
    {r : ℕ} (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F) (n := r)) (β : Fin r ≃ Fin r)
    (φ : GeneralLinear r F →* GeneralLinear r F) (hφ : ∀ g x y, φ g x y = g (β x) (β y))
    (E : Representation.Equiv (A₁.obj.representation.comp φ) A₂.obj.representation) :
    Nonempty (A₁ ≅ A₂) := by
  have hP : ∀ g, φ g = permutation r F β.symm * g * (permutation r F β.symm)⁻¹ := by
    intro g
    apply Matrix.GeneralLinearGroup.ext
    intro x y
    rw [permutation_conjugate_entry, hφ, Equiv.Perm.inv_def, Equiv.symm_symm]
  let D : A₁.obj.representation.IntertwiningMap A₂.obj.representation :=
    { toLinearMap := E.toLinearMap ∘ₗ A₁.obj.representation (permutation r F β.symm)
      isIntertwining' := fun g => by
        ext v
        have h := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g
          (A₁.obj.representation (permutation r F β.symm) v)
        rw [MonoidHom.comp_apply, hP] at h
        simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] at h
        exact h }
  have hD : Function.Bijective D :=
    (EquivLike.bijective E).comp
      (A₁.obj.representation.apply_bijective (permutation r F β.symm))
  exact ⟨CategoryTheory.ObjectProperty.isoMk _ (SmoothRep.mkIso (D.ofBijective hD))⟩

/-- Two cuspidal data are equal when their actual representatives are
equivalent after pulling back along a homomorphism that permutes matrix
entries by a coordinate bijection. -/
theorem cuspidalDatum_eq_of_equiv {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {T : F.TopologicalData} {ρ₁ ρ₂ : CuspidalDatum.{uV, uF} T}
    (A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ₁.rank))
    (A₂ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ₂.rank))
    (h₁ : ρ₁.IsRepresentedBy A₁) (h₂ : ρ₂.IsRepresentedBy A₂)
    (β : Fin ρ₁.rank ≃ Fin ρ₂.rank)
    (φ : GeneralLinear ρ₂.rank F.Carrier →* GeneralLinear ρ₁.rank F.Carrier)
    (hφ : ∀ g x y, φ g x y = g (β x) (β y))
    (E : letI := T.topology
      Representation.Equiv (A₁.obj.representation.comp φ) A₂.obj.representation) :
    ρ₁ = ρ₂ := by
  let _ := T.topology
  obtain ⟨r, hr, c₁⟩ := ρ₁
  obtain ⟨r₂, hr₂, c₂⟩ := ρ₂
  obtain rfl : r = r₂ := Fin.equiv_iff_eq.mp ⟨β⟩
  have hc : c₁ = c₂ := by
    rw [← show A₁.isoClass = c₁ from h₁, ← show A₂.isoClass = c₂ from h₂]
    exact (SupercuspidalRep.isoClass_eq_iff A₁ A₂).mpr
      (nonempty_iso_of_equiv_comp_permuted A₁ A₂ β φ hφ E)
  rw [hc]

/-- Proof of `GLCuspidalTensorAssociationStatement`. -/
theorem glCuspidalTensorAssociation : GLCuspidalTensorAssociationStatement.{uV, uF} := by
  intro p _ F T n _
  let _ := T.topology
  intro k l ρ ρ' h h' A A' hA hA' hassoc
  obtain ⟨w, hw, ⟨E⟩⟩ := hassoc
  have : ∀ i, Nontrivial (A i).obj := fun i =>
    nontrivial_of_isIrreducible (A i).obj.representation (hρ := (A i).property.1)
  have key : ∀ i,
      ρ i = ρ' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i) := by
    intro i
    have hE : Nonempty (Representation.Equiv
        ((A i).obj.representation.comp (factorHom hw i))
        (A' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)).obj.representation) := by
      refine nonempty_equiv_of_factor_actions (V := fun i => (A i).obj)
        (W := fun j => (A' j).obj)
        (hρ := isIrreducible_comp_of_surjective (A i).obj.representation
          (hρ := (A i).property.1) (factorHom hw i) (factorHom_surjective hw i))
        (hσ := (A' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)).property.1)
        ?_ ?_
        (equivComp E (MonoidHom.mulSingle _
          (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)))
      -- Elaborating the lemmas before unifying with the goals avoids slow unification.
      · intro g v
        have hl := external_leviConjugation_symm_mulSingle (fun i => (A i).obj.representation)
          hw i g v
        exact hl
      · intro g v
        have hl := external_mulSingle_tprod (fun j => (A' j).obj.representation)
          (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i) g v
        exact hl
    obtain ⟨E'⟩ := hE
    exact cuspidalDatum_eq_of_equiv (A i)
      (A' (blockMap (T.cuspidalShape ρ h) (T.cuspidalShape ρ' h') w i)) (hA i)
      (hA' _) (blockPositionEquiv hw i) (factorHom hw i)
      (fun g x y => factorHom_apply_entry hw i g x y) E'
  let τ : Fin k ≃ Fin l := Equiv.ofBijective _ (blockImage_bijective hw)
  rw [← Fin.univ_val_map, ← Fin.univ_val_map, show ρ = ρ' ∘ τ from funext key,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

end Datum

end Langlands.CuspidalSupport
