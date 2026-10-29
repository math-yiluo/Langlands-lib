import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof

/-!
# The single-block normalized refined Jacquet comparison

For a one-block shape `C` of `GL_n`, a refinement `D` of its sole block is the
same datum as the block shape `B := C.singleBlockRefinementEquiv hC D` of the
whole group. The actual refined Levi of `D` is identified with the standard
Levi of `B`, and the normalized refined Jacquet module of
`σ := ρ ∘ C.leviEmbedding` is identified with the normalized standard Jacquet
module of `ρ` along `B`: the linear equivalence sends one actual quotient class
to the other, and both actions use their own `δ^(-1/2)` normalization.

Restricted to block scalars, the flattened scalar coordinates of `D` are the
ordinary scalar coordinates of `B` in the same order. Hence generalized
eigencharacters (with one common natural power), Jacquet exponents, and the
monotone and nonconstant absolute-value conditions correspond.
-/

noncomputable section

open scoped NNReal

namespace Langlands

universe uR uA uA' uV uW

section CharacterSpaceTransport

variable {R : Type uR} [CommRing R] {A : Type uA} [Monoid A] {A' : Type uA'} [Monoid A']
variable {V : Type uV} [AddCommGroup V] [Module R V] {W : Type uW} [AddCommGroup W] [Module R W]
variable {π : Representation R A V} {σ : Representation R A W}

/-- A representation equivalence matches the uniform character spaces of each
fixed power. -/
theorem equiv_apply_mem_characterSpace_iff (e : π.Equiv σ) (χ : A →* Rˣ) (k : ℕ)
    (v : V) : e v ∈ characterSpace σ χ k ↔ v ∈ characterSpace π χ k := by
  refine ⟨fun h => ?_, map_mem_characterSpace_of_intertwiningMap e.toIntertwiningMap χ k⟩
  simpa using map_mem_characterSpace_of_intertwiningMap e.symm.toIntertwiningMap χ k h

/-- The image of a character space under a representation equivalence is the
character space of the same character and power. -/
theorem map_characterSpace_of_equiv (e : π.Equiv σ) (χ : A →* Rˣ) (k : ℕ) :
    (characterSpace π χ k).map e.toLinearMap = characterSpace σ χ k := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (equiv_apply_mem_characterSpace_iff e χ k v).mpr hv
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    exact (equiv_apply_mem_characterSpace_iff e χ k _).mp (by simpa using hw)

/-- Pulling a representation and a character back along a monoid equivalence
does not change any character space. -/
theorem characterSpace_comp_mulEquiv (π : Representation R A V) (f : A' ≃* A)
    (χ : A →* Rˣ) (k : ℕ) :
    characterSpace (π.comp f.toMonoidHom) (χ.comp f.toMonoidHom) k =
      characterSpace π χ k := by
  ext v
  simp only [mem_characterSpace]
  constructor
  · intro h a
    simpa using h (f.symm a)
  · intro h b
    exact h (f b)

/-- Generalized eigencharacters are unchanged by pulling back along a monoid
equivalence. -/
theorem isGeneralizedEigencharacter_comp_mulEquiv_iff (π : Representation R A V)
    (f : A' ≃* A) (χ : A →* Rˣ) :
    IsGeneralizedEigencharacter (π.comp f.toMonoidHom) (χ.comp f.toMonoidHom) ↔
      IsGeneralizedEigencharacter π χ := by
  simp only [IsGeneralizedEigencharacter, characterSpace_comp_mulEquiv]

end CharacterSpaceTransport

namespace GeneralLinear.BlockShape

universe u uM

variable {n : ℕ} (C : BlockShape n) (hC : C.length = 1)

include hC

/-- The block indices of a one-block shape, with their unique element. -/
abbrev singleBlockUnique : Unique (Fin C.length) where
  default := C.singleBlockIndex hC
  uniq := C.eq_singleBlockIndex hC

section Group

variable (R : Type u) [CommRing R] (D : Geometric.BlockRefinement C)

/-- The actual refined Levi of a refinement of the sole block, identified with
the standard Levi of the corresponding block shape of the whole group: an
element is sent to its inner block coordinates at the sole block. -/
def singleBlockRefinedLeviEquiv :
    Geometric.refinedLevi R C D ≃* (C.singleBlockRefinementEquiv hC D).Levi R :=
  letI := C.singleBlockUnique hC
  (Geometric.refinedLeviEquiv R C D).symm.trans (MulEquiv.piUnique fun i => (D i).Levi R)

theorem singleBlockRefinedLeviEquiv_apply (m : Geometric.refinedLevi R C D) :
    C.singleBlockRefinedLeviEquiv hC R D m =
      (Geometric.refinedLeviEquiv R C D).symm m (C.singleBlockIndex hC) := rfl

/-- The inner block-diagonal matrix of the sole block coordinates of `m` is the
sole block of `m`. -/
theorem leviEmbedding_refinedLeviEquiv_symm_singleBlockIndex
    (m : Geometric.refinedLevi R C D) :
    (D (C.singleBlockIndex hC)).leviEmbedding R
        ((Geometric.refinedLeviEquiv R C D).symm m (C.singleBlockIndex hC)) =
      m.val (C.singleBlockIndex hC) :=
  congrArg (fun x : Geometric.refinedLevi R C D => x.val (C.singleBlockIndex hC))
    ((Geometric.refinedLeviEquiv R C D).apply_symm_apply m)

/-- The group transport is compatible with the two actual block-diagonal
embeddings into `GL_n`. -/
theorem singleBlockRefinedLeviEquiv_leviEmbedding (m : Geometric.refinedLevi R C D) :
    (C.singleBlockRefinementEquiv hC D).leviEmbedding R
        (C.singleBlockRefinedLeviEquiv hC R D m) =
      C.leviEmbedding R m.val := by
  apply Units.ext
  ext x y
  obtain ⟨⟨j, a⟩, rfl⟩ := (C.singleBlockRefinementEquiv hC D).indexEquiv.surjective x
  obtain ⟨⟨k, b⟩, rfl⟩ := (C.singleBlockRefinementEquiv hC D).indexEquiv.surjective y
  change (C.singleBlockRefinementEquiv hC D).leviEmbedding R _
      ((C.singleBlockRefinementEquiv hC D).index j a)
      ((C.singleBlockRefinementEquiv hC D).index k b) =
    C.leviEmbedding R m.val ((C.singleBlockRefinementEquiv hC D).index j a)
      ((C.singleBlockRefinementEquiv hC D).index k b)
  conv_rhs => rw [C.singleBlockRefinement_index hC D j a,
    C.singleBlockRefinement_index hC D k b, C.leviEmbedding_apply_same,
    ← C.leviEmbedding_refinedLeviEquiv_symm_singleBlockIndex hC R D m]
  by_cases hjk : j = k
  · subst k
    exact ((C.singleBlockRefinementEquiv hC D).leviEmbedding_apply_same R _ j a b).trans
      ((D (C.singleBlockIndex hC)).leviEmbedding_apply_same R _ j a b).symm
  · exact ((C.singleBlockRefinementEquiv hC D).leviEmbedding_apply_ne R _ a b hjk).trans
      ((D (C.singleBlockIndex hC)).leviEmbedding_apply_ne R _ a b hjk).symm

end Group

section Scalars

variable (D : Geometric.BlockRefinement C)

/-- The flattened numbering of the blocks of the sole refined block, in their
consecutive order. -/
def singleBlockFlattenOrderIso :
    Fin (C.singleBlockRefinementEquiv hC D).length ≃o Fin (C.flatten D).length where
  toEquiv :=
    letI := C.singleBlockUnique hC
    (Equiv.uniqueSigma fun i => Fin (D i).length).symm.trans (C.flattenBlockEquiv D)
  map_rel_iff' := by
    have hlt : ∀ j k : Fin (C.singleBlockRefinementEquiv hC D).length,
        C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩ <
            C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, k⟩ ↔ j < k := by
      intro j k
      rw [flattenBlockEquiv_lt_iff]
      simp only [lt_self_iff_false, true_and, false_or, Fin.lt_def]
    have hmono : StrictMono fun j : Fin (C.singleBlockRefinementEquiv hC D).length =>
        C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩ :=
      fun j k h => (hlt j k).mpr h
    intro j k
    exact hmono.le_iff_le

@[simp] theorem singleBlockFlattenOrderIso_apply
    (j : Fin (C.singleBlockRefinementEquiv hC D).length) :
    C.singleBlockFlattenOrderIso hC D j = C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩ :=
  rfl

variable (M : Type uM) [Monoid M]

/-- The ordinary coordinates of flattened scalars: the `j`-th ordinary coordinate
is the flattened coordinate numbered by the pair of the sole block and `j`. -/
def singleBlockScalarMulEquiv :
    (Fin (C.flatten D).length → M) ≃* (Fin (C.singleBlockRefinementEquiv hC D).length → M) where
  toFun a j := a (C.singleBlockFlattenOrderIso hC D j)
  invFun b k := b ((C.singleBlockFlattenOrderIso hC D).symm k)
  left_inv a := funext fun k => congrArg a ((C.singleBlockFlattenOrderIso hC D).apply_symm_apply k)
  right_inv b := funext fun j => congrArg b ((C.singleBlockFlattenOrderIso hC D).symm_apply_apply j)
  map_mul' _ _ := rfl

@[simp] theorem singleBlockScalarMulEquiv_apply (a : Fin (C.flatten D).length → M)
    (j : Fin (C.singleBlockRefinementEquiv hC D).length) :
    C.singleBlockScalarMulEquiv hC D M a j = a (C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩) :=
  rfl

@[simp] theorem singleBlockScalarMulEquiv_symm_apply
    (b : Fin (C.singleBlockRefinementEquiv hC D).length → M) (k : Fin (C.flatten D).length) :
    (C.singleBlockScalarMulEquiv hC D M).symm b k =
      b ((C.singleBlockFlattenOrderIso hC D).symm k) :=
  rfl

/-- The same coordinate equivalence, continuous for the product topologies. -/
def singleBlockScalarEquiv [TopologicalSpace M] :
    (Fin (C.flatten D).length → M) ≃ₜ* (Fin (C.singleBlockRefinementEquiv hC D).length → M) where
  toMulEquiv := C.singleBlockScalarMulEquiv hC D M
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

@[simp] theorem singleBlockScalarEquiv_toMulEquiv [TopologicalSpace M] :
    (C.singleBlockScalarEquiv hC D M).toMulEquiv = C.singleBlockScalarMulEquiv hC D M := rfl

@[simp] theorem coe_singleBlockScalarEquiv [TopologicalSpace M] :
    ⇑(C.singleBlockScalarEquiv hC D M) = ⇑(C.singleBlockScalarMulEquiv hC D M) := rfl

/-- Flattened block scalars of the refined Levi are the ordinary block scalars of
the corresponding standard Levi. -/
theorem singleBlockRefinedLeviEquiv_flattened_blockScalarLevi (R : Type u) [CommRing R]
    (a : Fin (C.flatten D).length → Rˣ) :
    C.singleBlockRefinedLeviEquiv hC R D
        (Geometric.flattenedLeviEquiv R C D ((C.flatten D).blockScalarLevi R a)) =
      (C.singleBlockRefinementEquiv hC D).blockScalarLevi R
        (C.singleBlockScalarMulEquiv hC D Rˣ a) := by
  funext j
  have key : ∀ (k : Fin (C.flatten D).length) (q : (i : Fin C.length) × Fin (D i).length)
      (_ : (C.flattenBlockEquiv D).symm k = q),
      Geometric.flattenedLeviProductEquiv R C D ((C.flatten D).blockScalarLevi R a) q.1 q.2 =
        GeneralLinear.scalar (a k) := by
    intro k q h
    subst q
    exact Geometric.flattenedLeviProductEquiv_apply_symm R C D _ k
  change (Geometric.refinedLeviEquiv R C D).symm (Geometric.refinedLeviEquiv R C D
      (Geometric.flattenedLeviProductEquiv R C D ((C.flatten D).blockScalarLevi R a)))
      (C.singleBlockIndex hC) j = _
  rw [MulEquiv.symm_apply_apply]
  exact key _ ⟨C.singleBlockIndex hC, j⟩ ((C.flattenBlockEquiv D).symm_apply_apply _)

end Scalars

section Order

variable (D : Geometric.BlockRefinement C) {α : Type*}

/-- Monotonicity is unchanged by the ordinary numbering of the sole refined block. -/
theorem singleBlock_monotone_comp_iff [Preorder α] (f : Fin (C.flatten D).length → α) :
    Monotone (fun j => f (C.singleBlockFlattenOrderIso hC D j)) ↔ Monotone f := by
  constructor
  · intro h k l hkl
    have := h ((C.singleBlockFlattenOrderIso hC D).symm.monotone hkl)
    simpa only [OrderIso.apply_symm_apply] using this
  · intro h
    exact h.comp (C.singleBlockFlattenOrderIso hC D).monotone

/-- Nonconstancy is unchanged by the ordinary numbering of the sole refined block. -/
theorem singleBlock_exists_ne_comp_iff (f : Fin (C.flatten D).length → α) :
    (∃ i j, f (C.singleBlockFlattenOrderIso hC D i) ≠ f (C.singleBlockFlattenOrderIso hC D j)) ↔
      ∃ k l, f k ≠ f l := by
  constructor
  · rintro ⟨i, j, h⟩
    exact ⟨_, _, h⟩
  · rintro ⟨k, l, h⟩
    refine ⟨(C.singleBlockFlattenOrderIso hC D).symm k,
      (C.singleBlockFlattenOrderIso hC D).symm l, ?_⟩
    simpa only [OrderIso.apply_symm_apply] using h

/-- Blockwise monotonicity in the flattened numbering is monotonicity in the
ordinary numbering of the sole block. -/
theorem singleBlock_forall_block_monotone_iff [Preorder α] (f : Fin (C.flatten D).length → α) :
    (∀ i : Fin C.length, Monotone fun j : Fin (D i).length => f (C.flattenBlockEquiv D ⟨i, j⟩)) ↔
      Monotone (fun j => f (C.singleBlockFlattenOrderIso hC D j)) := by
  constructor
  · intro h
    exact h (C.singleBlockIndex hC)
  · intro h i
    obtain rfl := C.eq_singleBlockIndex hC i
    exact h

end Order

section Coinvariants

variable {F : Type u} [CommRing F] (D : Geometric.BlockRefinement C)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (Langlands.GeneralLinear n F) V)

/-- The refined Jacquet module of `ρ ∘ C.leviEmbedding` is the standard Jacquet
module of `ρ` along the corresponding block shape: the actual quotient classes
of the same vector correspond. -/
def singleBlockRefinedJacquetLinearEquiv :
    Geometric.RefinedJacquetModule C D (ρ.comp (C.leviEmbedding F)) ≃ₗ[ℂ]
      (C.singleBlockRefinementEquiv hC D).JacquetModule ρ where
  __ := Jacquet.lift (ρ.comp (C.leviEmbedding F)) (Geometric.refinedUnipotent F C D)
    ((C.singleBlockRefinementEquiv hC D).jacquetMk ρ) (fun u => LinearMap.ext fun v => by
      have hu := (C.singleBlock_mem_refinedUnipotent_iff hC F D u.val).mp u.property
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp hu
      have h := Jacquet.mk_apply_subgroup
        (ρ.comp ((C.singleBlockRefinementEquiv hC D).parabolic F).subtype)
        ((C.singleBlockRefinementEquiv hC D).unipotentRadical F) ⟨w, hw⟩ v
      change (C.singleBlockRefinementEquiv hC D).jacquetMk ρ
          (ρ (C.leviEmbedding F u.val) v) =
        (C.singleBlockRefinementEquiv hC D).jacquetMk ρ v
      rw [← hwu]
      exact h)
  invFun := Jacquet.lift (ρ.comp ((C.singleBlockRefinementEquiv hC D).parabolic F).subtype)
    ((C.singleBlockRefinementEquiv hC D).unipotentRadical F)
    (Geometric.refinedJacquetMk C D (ρ.comp (C.leviEmbedding F))) (fun w => LinearMap.ext fun v => by
      have hw : ((w : (C.singleBlockRefinementEquiv hC D).parabolic F) :
          Langlands.GeneralLinear n F) ∈ (C.singleBlockRefinementEquiv hC D).unipotentSubgroup F :=
        Subgroup.mem_map.mpr ⟨w.val, w.property, rfl⟩
      obtain ⟨m, hm⟩ := C.singleBlock_leviEmbedding_surjective hC F w.val.val
      have hmu : m ∈ Geometric.refinedUnipotent F C D :=
        (C.singleBlock_mem_refinedUnipotent_iff hC F D m).mpr (hm ▸ hw)
      have h := Jacquet.mk_apply_subgroup (ρ.comp (C.leviEmbedding F))
        (Geometric.refinedUnipotent F C D) ⟨m, hmu⟩ v
      change Geometric.refinedJacquetMk C D (ρ.comp (C.leviEmbedding F)) (ρ w.val.val v) =
        Geometric.refinedJacquetMk C D (ρ.comp (C.leviEmbedding F)) v
      rw [← hm]
      exact h)
  left_inv x := by
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ _ x
    rfl
  right_inv x := by
    obtain ⟨v, rfl⟩ := (C.singleBlockRefinementEquiv hC D).jacquetMk_surjective ρ x
    rfl

@[simp] theorem singleBlockRefinedJacquetLinearEquiv_mk (v : V) :
    C.singleBlockRefinedJacquetLinearEquiv hC D ρ
        (Geometric.refinedJacquetMk C D (ρ.comp (C.leviEmbedding F)) v) =
      (C.singleBlockRefinementEquiv hC D).jacquetMk ρ v := rfl

@[simp] theorem singleBlockRefinedJacquetLinearEquiv_symm_mk (v : V) :
    (C.singleBlockRefinedJacquetLinearEquiv hC D ρ).symm
        ((C.singleBlockRefinementEquiv hC D).jacquetMk ρ v) =
      Geometric.refinedJacquetMk C D (ρ.comp (C.leviEmbedding F)) v := rfl

end Coinvariants

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

open Geometric GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (C : GeneralLinear.BlockShape n) (hC : C.length = 1) (D : BlockRefinement C)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)

include hC

/-- The full refined modulus is the explicit standard modulus of the
corresponding block shape. -/
theorem singleBlock_refinedLeviModulus (m : refinedLevi F.Carrier C D) :
    T.refinedLeviModulus C D m =
      T.leviModulus (C.singleBlockRefinementEquiv hC D)
        (C.singleBlockRefinedLeviEquiv hC F.Carrier D m) := by
  rw [refinedLeviModulus_apply, Fintype.prod_eq_single (C.singleBlockIndex hC)]
  · rfl
  · intro i hi
    exact absurd (C.eq_singleBlockIndex hC i) hi

/-- The actual normalized refined Jacquet module of `ρ ∘ C.leviEmbedding` is the
actual normalized Jacquet module of `ρ` along `C.singleBlockRefinementEquiv hC D`,
pulled back along the refined-Levi/standard-Levi group transport. -/
def singleBlockNormalizedRefinedJacquetEquiv :
    (T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).Equiv
      ((T.normalizedJacquet (C.singleBlockRefinementEquiv hC D) ρ).comp
        (C.singleBlockRefinedLeviEquiv hC F.Carrier D).toMonoidHom) :=
  Representation.Equiv.mk (C.singleBlockRefinedJacquetLinearEquiv hC D ρ) fun m => by
    refine Representation.Coinvariants.hom_ext (LinearMap.ext fun v => ?_)
    change C.singleBlockRefinedJacquetLinearEquiv hC D ρ
        (T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier)) m
          (refinedJacquetMk C D (ρ.comp (C.leviEmbedding F.Carrier)) v)) =
      T.normalizedJacquet (C.singleBlockRefinementEquiv hC D) ρ
        (C.singleBlockRefinedLeviEquiv hC F.Carrier D m)
        (C.singleBlockRefinedJacquetLinearEquiv hC D ρ
          (refinedJacquetMk C D (ρ.comp (C.leviEmbedding F.Carrier)) v))
    rw [normalizedRefinedJacquet_mk, map_smul, BlockShape.singleBlockRefinedJacquetLinearEquiv_mk,
      BlockShape.singleBlockRefinedJacquetLinearEquiv_mk, normalizedJacquet_mk,
      refinedLeviInverseHalfModulus_apply, T.singleBlock_refinedLeviModulus C hC D m,
      BlockShape.singleBlockRefinedLeviEquiv_leviEmbedding]
    rfl

@[simp] theorem singleBlockNormalizedRefinedJacquetEquiv_mk (v : V) :
    T.singleBlockNormalizedRefinedJacquetEquiv C hC D ρ
        (refinedJacquetMk C D (ρ.comp (C.leviEmbedding F.Carrier)) v) =
      (C.singleBlockRefinementEquiv hC D).jacquetMk ρ v := rfl

@[simp] theorem singleBlockNormalizedRefinedJacquetEquiv_symm_mk (v : V) :
    (T.singleBlockNormalizedRefinedJacquetEquiv C hC D ρ).symm
        ((C.singleBlockRefinementEquiv hC D).jacquetMk ρ v) =
      refinedJacquetMk C D (ρ.comp (C.leviEmbedding F.Carrier)) v := rfl

/-- On flattened block scalars, the normalized refined Jacquet action is the
split-centre action of the corresponding standard Jacquet module, pulled back
along the ordinary scalar coordinates. -/
def singleBlockScalarJacquetEquiv :
    Representation.Equiv
      ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
        ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
          ((C.flatten D).blockScalarLevi F.Carrier)))
      ((T.splitCentreJacquet (C.singleBlockRefinementEquiv hC D) ρ).comp
        (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom) :=
  Representation.Equiv.mk (C.singleBlockRefinedJacquetLinearEquiv hC D ρ) fun a => by
    have h := (T.singleBlockNormalizedRefinedJacquetEquiv C hC D ρ).toIntertwiningMap.isIntertwining'
      (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))
    change _ = T.normalizedJacquet (C.singleBlockRefinementEquiv hC D) ρ
      (C.singleBlockRefinedLeviEquiv hC F.Carrier D
        (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))) ∘ₗ _ at h
    rw [C.singleBlockRefinedLeviEquiv_flattened_blockScalarLevi hC D F.Carrier a] at h
    exact h

@[simp] theorem singleBlockScalarJacquetEquiv_mk (v : V) :
    T.singleBlockScalarJacquetEquiv C hC D ρ
        (refinedJacquetMk C D (ρ.comp (C.leviEmbedding F.Carrier)) v) =
      (C.singleBlockRefinementEquiv hC D).jacquetMk ρ v := rfl

/-- The actual quotient-class equivalence matches the character spaces of every
ordinary scalar character `χ` and its flattened pullback, with the same power. -/
theorem singleBlock_mem_characterSpace_iff
    (χ : (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ) →* ℂˣ) (k : ℕ)
    (v : RefinedJacquetModule C D (ρ.comp (C.leviEmbedding F.Carrier))) :
    C.singleBlockRefinedJacquetLinearEquiv hC D ρ v ∈
        characterSpace (T.splitCentreJacquet (C.singleBlockRefinementEquiv hC D) ρ) χ k ↔
      v ∈ characterSpace
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier)))
        (χ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom) k := by
  rw [← characterSpace_comp_mulEquiv _ (C.singleBlockScalarMulEquiv hC D F.Carrierˣ) χ k]
  exact equiv_apply_mem_characterSpace_iff (T.singleBlockScalarJacquetEquiv C hC D ρ) _ k v

/-- The same identification as an equality of submodules. -/
theorem singleBlock_map_characterSpace
    (χ : (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ) →* ℂˣ) (k : ℕ) :
    (characterSpace
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier)))
        (χ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom) k).map
        (C.singleBlockRefinedJacquetLinearEquiv hC D ρ).toLinearMap =
      characterSpace (T.splitCentreJacquet (C.singleBlockRefinementEquiv hC D) ρ) χ k := by
  rw [← characterSpace_comp_mulEquiv _ (C.singleBlockScalarMulEquiv hC D F.Carrierˣ) χ k]
  exact map_characterSpace_of_equiv (T.singleBlockScalarJacquetEquiv C hC D ρ) _ k

/-- Generalized occurrence with one common natural power corresponds, for every
ordinary scalar character. -/
theorem singleBlock_isGeneralizedEigencharacter_iff
    (χ : (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ) →* ℂˣ) :
    IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier)))
        (χ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom) ↔
      IsGeneralizedEigencharacter (T.splitCentreJacquet (C.singleBlockRefinementEquiv hC D) ρ) χ :=
  (isGeneralizedEigencharacter_iff_of_equiv (T.singleBlockScalarJacquetEquiv C hC D ρ) _).trans
    (isGeneralizedEigencharacter_comp_mulEquiv_iff _ _ χ)

/-- The same correspondence, starting from an arbitrary flattened scalar
character. -/
theorem singleBlock_isGeneralizedEigencharacter_iff_flattened
    (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ) :
    IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ ↔
      IsGeneralizedEigencharacter (T.splitCentreJacquet (C.singleBlockRefinementEquiv hC D) ρ)
        (ψ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).symm.toMonoidHom) := by
  have hψ : ψ = (ψ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).symm.toMonoidHom).comp
      (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom := by
    ext a
    simp
  conv_lhs => rw [hψ]
  exact T.singleBlock_isGeneralizedEigencharacter_iff C hC D ρ _

/-- Open kernels correspond under the continuous scalar coordinate equivalence. -/
theorem singleBlock_isOpen_ker_iff
    (χ : (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ) →* ℂˣ) :
    letI := T.topology
    IsOpen ((χ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom).ker :
        Set (Fin (C.flatten D).length → F.Carrierˣ)) ↔
      IsOpen (χ.ker : Set (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ)) := by
  let := T.topology
  change IsOpen ((C.singleBlockScalarEquiv hC D F.Carrierˣ) ⁻¹'
      (χ.ker : Set (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ))) ↔ _
  exact (C.singleBlockScalarEquiv hC D F.Carrierˣ).toHomeomorph.isOpen_preimage

/-- An ordinary scalar character is an actual Jacquet exponent along
`C.singleBlockRefinementEquiv hC D` exactly when its flattened pullback has open
kernel and is a generalized eigencharacter of the refined scalar action. -/
theorem singleBlock_isJacquetExponent_iff
    (χ : (Fin (C.singleBlockRefinementEquiv hC D).length → F.Carrierˣ) →* ℂˣ) :
    T.IsJacquetExponent (C.singleBlockRefinementEquiv hC D) ρ χ ↔
      (letI := T.topology
       IsOpen ((χ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom).ker :
        Set (Fin (C.flatten D).length → F.Carrierˣ))) ∧
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier)))
        (χ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom) :=
  and_congr (T.singleBlock_isOpen_ker_iff C hC D χ).symm
    (T.singleBlock_isGeneralizedEigencharacter_iff C hC D ρ χ).symm

/-- A flattened scalar character with open kernel occurring in the refined
scalar action is exactly the pullback of an actual Jacquet exponent. -/
theorem singleBlock_isJacquetExponent_iff_flattened
    (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ) :
    ((letI := T.topology
      IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ))) ∧
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ) ↔
      T.IsJacquetExponent (C.singleBlockRefinementEquiv hC D) ρ
        (ψ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).symm.toMonoidHom) := by
  have hψ : ψ = (ψ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).symm.toMonoidHom).comp
      (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).toMonoidHom := by
    ext a
    simp
  rw [T.singleBlock_isJacquetExponent_iff C hC D ρ, ← hψ]

/-- The ordinary scalar coordinates are monotone in absolute value exactly when
the flattened ones are. -/
theorem singleBlockScalar_monotone_normalizedAbs_iff (a : Fin (C.flatten D).length → F.Carrierˣ) :
    Monotone (fun j => T.normalizedAbs (C.singleBlockScalarMulEquiv hC D F.Carrierˣ a j : F.Carrier)) ↔
      Monotone (fun k => T.normalizedAbs (a k : F.Carrier)) :=
  C.singleBlock_monotone_comp_iff hC D (fun k => T.normalizedAbs (a k : F.Carrier))

/-- The ordinary scalar coordinates have nonconstant absolute value exactly when
the flattened ones do. -/
theorem singleBlockScalar_exists_normalizedAbs_ne_iff
    (a : Fin (C.flatten D).length → F.Carrierˣ) :
    (∃ i j, T.normalizedAbs (C.singleBlockScalarMulEquiv hC D F.Carrierˣ a i : F.Carrier) ≠
        T.normalizedAbs (C.singleBlockScalarMulEquiv hC D F.Carrierˣ a j : F.Carrier)) ↔
      ∃ k l, T.normalizedAbs (a k : F.Carrier) ≠ T.normalizedAbs (a l : F.Carrier) :=
  C.singleBlock_exists_ne_comp_iff hC D (fun k => T.normalizedAbs (a k : F.Carrier))

/-- The refined blockwise monotone chamber condition is the ordinary monotone
chamber condition of the scalar coordinates. -/
theorem singleBlockScalar_forall_block_monotone_iff
    (a : Fin (C.flatten D).length → F.Carrierˣ) :
    (∀ i : Fin C.length, Monotone fun j : Fin (D i).length =>
        T.normalizedAbs (a (C.flattenBlockEquiv D ⟨i, j⟩) : F.Carrier)) ↔
      Monotone (fun j => T.normalizedAbs (C.singleBlockScalarMulEquiv hC D F.Carrierˣ a j : F.Carrier)) :=
  C.singleBlock_forall_block_monotone_iff hC D (fun k => T.normalizedAbs (a k : F.Carrier))

end PadicField.TopologicalData

end Langlands
