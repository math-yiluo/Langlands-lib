import Langlands.Representation.RestrictedTensor.Action
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Finite-coordinate splitting and compact tails of restricted groups -/

noncomputable section
open Filter Topology
open scoped Classical

universe uI uG

namespace Langlands.RestrictedTensor

variable {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)]
variable (H : ∀ i, Subgroup (G i))

/-- The restricted product on the complement of a finite set. -/
abbrev ComplementGroup (S : Finset ι) :=
  RestrictedGroup (fun i : {i // i ∉ S} => G i) (fun i => H i)

/-- Restriction to the complementary coordinates. -/
def complementProjection (S : Finset ι) : RestrictedGroup G H →* ComplementGroup H S :=
  RestrictedProduct.mapAlongMonoidHom G (fun i : {i // i ∉ S} => G i)
    Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ => MonoidHom.id _) (Eventually.of_forall fun _ _ h => h)

@[simp]
theorem complementProjection_apply (S : Finset ι) (g : RestrictedGroup G H)
    (i : {i // i ∉ S}) : complementProjection H S g i = g i := rfl

/-- Assemble finite and complementary coordinates. -/
def finiteAssemble (S : Finset ι)
    (x : (∀ i : S, G i) × ComplementGroup H S) : RestrictedGroup G H where
  val i := if hi : i ∈ S then x.1 ⟨i, hi⟩ else x.2 ⟨i, hi⟩
  property := by
    have hf := (eventually_cofinite.mp x.2.property).image Subtype.val
    apply eventually_cofinite.mpr
    apply (S.finite_toSet.union hf).subset
    intro i hi
    by_cases his : i ∈ S
    · exact Or.inl his
    · refine Or.inr ⟨⟨i, his⟩, ?_, rfl⟩
      change x.2 ⟨i, his⟩ ∉ H i
      change (if hi : i ∈ S then x.1 ⟨i, hi⟩ else x.2 ⟨i, hi⟩) ∉ H i at hi
      simpa only [dite_eq_right his] using hi

@[simp]
theorem finiteAssemble_apply_mem (S : Finset ι)
    (x : (∀ i : S, G i) × ComplementGroup H S) (i : S) :
    finiteAssemble H S x i = x.1 i := dite_eq_left i.2

@[simp]
theorem finiteAssemble_apply_not_mem (S : Finset ι)
    (x : (∀ i : S, G i) × ComplementGroup H S) (i : {i // i ∉ S}) :
    finiteAssemble H S x i = x.2 i := dite_eq_right i.2

/-- The algebraic splitting, without any topological assumptions. -/
def finiteSplitMulEquiv (S : Finset ι) :
    RestrictedGroup G H ≃* (∀ i : S, G i) × ComplementGroup H S where
  toFun g := (fun i => g i, complementProjection H S g)
  invFun := finiteAssemble H S
  left_inv g := by
    ext i
    change (if hi : i ∈ S then g i else g i) = g i
    split <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      exact finiteAssemble_apply_mem H S x i
    · ext i
      exact finiteAssemble_apply_not_mem H S x i
  map_mul' _ _ := rfl

variable [∀ i, TopologicalSpace (G i)]

theorem continuous_complementProjection (S : Finset ι) :
    Continuous (complementProjection H S) :=
  RestrictedProduct.mapAlong_continuous G (fun i : {i // i ∉ S} => G i)
    Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ x => x) (Eventually.of_forall fun _ _ h => h) (fun _ => continuous_id)

theorem continuous_finiteSplitMulEquiv (S : Finset ι) :
    Continuous (finiteSplitMulEquiv H S) :=
  (continuous_pi fun i => RestrictedProduct.continuous_eval i.1).prodMk
    (continuous_complementProjection H S)

/-- The all-integral subgroup in the split coordinates, used to check continuity
at the identity. -/
def splitIntegralSubgroup (S : Finset ι) :
    Subgroup ((∀ i : S, G i) × ComplementGroup H S) where
  carrier := {x | (∀ i : S, x.1 i ∈ H i) ∧ ∀ i : {i // i ∉ S}, x.2 i ∈ H i}
  one_mem' := ⟨fun i => (H i).one_mem, fun i => (H i).one_mem⟩
  mul_mem' hx hy := ⟨fun i => (H i).mul_mem (hx.1 i) (hy.1 i),
    fun i => (H i).mul_mem (hx.2 i) (hy.2 i)⟩
  inv_mem' hx := ⟨fun i => (H i).inv_mem (hx.1 i),
    fun i => (H i).inv_mem (hx.2 i)⟩

theorem isOpen_splitIntegralSubgroup (hH : ∀ i, IsOpen (H i : Set (G i)))
    (S : Finset ι) : IsOpen (splitIntegralSubgroup H S : Set ((∀ i : S, G i) × ComplementGroup H S)) := by
  have hfin : IsOpen {x : (∀ i : S, G i) | ∀ i : S, x i ∈ H i} := by
    convert isOpen_iInter_of_finite (fun i : S =>
      (hH i).preimage (continuous_apply i)) using 1
    ext x
    simp
  exact (hfin.preimage continuous_fst).inter
    ((RestrictedProduct.isOpen_forall_mem (fun i : {i // i ∉ S} => hH i)).preimage
      continuous_snd)

theorem continuous_finiteAssemble [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι) :
    Continuous (finiteAssemble H S) := by
  let : Fact (∀ i, IsOpen (H i : Set (G i))) := ⟨hH⟩
  let : Fact (∀ i : {i // i ∉ S}, IsOpen (H i : Set (G i))) := ⟨fun i => hH i⟩
  let f : splitIntegralSubgroup H S → ∀ i, H i := fun x i =>
    ⟨finiteAssemble H S x.1 i, by
      change (if hi : i ∈ S then x.1.1 ⟨i, hi⟩ else x.1.2 ⟨i, hi⟩) ∈ H i
      split <;> rename_i hi
      · exact x.2.1 ⟨i, hi⟩
      · exact x.2.2 ⟨i, hi⟩⟩
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    have hiCont : Continuous (fun x : splitIntegralSubgroup H S => finiteAssemble H S x.1 i) := by
      change Continuous (fun x : splitIntegralSubgroup H S =>
        (if hi : i ∈ S then x.1.1 ⟨i, hi⟩ else x.1.2 ⟨i, hi⟩ : G i))
      by_cases hi : i ∈ S
      · simp only [dite_eq_left hi]
        exact (continuous_apply (⟨i, hi⟩ : S)).comp (continuous_fst.comp continuous_subtype_val)
      · simp only [dite_eq_right hi]
        exact (RestrictedProduct.continuous_eval (⟨i, hi⟩ : {i // i ∉ S})).comp
          (continuous_snd.comp continuous_subtype_val)
    exact hiCont.subtype_mk _
  have hc : Continuous (fun x : splitIntegralSubgroup H S => finiteAssemble H S x.1) :=
    (RestrictedProduct.isEmbedding_structureMap (R := G)
      (A := fun i => (H i : Set (G i))) (𝓕 := cofinite)).continuous.comp hf
  apply continuous_of_continuousAt_one (finiteSplitMulEquiv H S).symm.toMonoidHom
  change ContinuousAt (finiteAssemble H S) 1
  exact (isOpen_splitIntegralSubgroup H hH S).isOpenEmbedding_subtypeVal.continuousAt_iff
    (g := finiteAssemble H S) (x := (1 : splitIntegralSubgroup H S)) |>.mp hc.continuousAt

/-- Separate any finite set of coordinates in the original restricted-product
topology. This also applies to the empty finite set. -/
def finiteSplitEquiv [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι) :
    RestrictedGroup G H ≃ₜ* (∀ i : S, G i) × ComplementGroup H S where
  __ := finiteSplitMulEquiv H S
  continuous_toFun := continuous_finiteSplitMulEquiv H S
  continuous_invFun := continuous_finiteAssemble H hH S

@[simp]
theorem finiteSplitEquiv_fst [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι)
    (g : RestrictedGroup G H) (i : S) :
    (finiteSplitEquiv H hH S g).1 i = g i := rfl

@[simp]
theorem finiteSplitEquiv_snd [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι)
    (g : RestrictedGroup G H) (i : {i // i ∉ S}) :
    (finiteSplitEquiv H hH S g).2 i = g i := rfl

@[simp]
theorem finiteSplitEquiv_symm_apply_mem [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι)
    (x : (∀ i : S, G i) × ComplementGroup H S) (i : S) :
    (finiteSplitEquiv H hH S).symm x i = x.1 i :=
  finiteAssemble_apply_mem H S x i

@[simp]
theorem finiteSplitEquiv_symm_apply_not_mem [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (S : Finset ι)
    (x : (∀ i : S, G i) × ComplementGroup H S) (i : {i // i ∉ S}) :
    (finiteSplitEquiv H hH S).symm x i = x.2 i :=
  finiteAssemble_apply_not_mem H S x i

/-- Evaluation identifies the product over a singleton with its one factor. -/
def singletonCoordinatesEquiv (i : ι) : (∀ j : ({i} : Finset ι), G j) ≃ₜ* G i := by
  letI : Unique ({i} : Finset ι) :=
    { default := ⟨i, Finset.mem_singleton_self i⟩
      uniq := fun j => Subtype.ext (Finset.mem_singleton.mp j.2) }
  exact
    { toMulEquiv := MulEquiv.piUnique (fun j : ({i} : Finset ι) => G j)
      continuous_toFun := (Homeomorph.piUnique (fun j : ({i} : Finset ι) => G j)).continuous
      continuous_invFun := (Homeomorph.piUnique (fun j : ({i} : Finset ι) => G j)).symm.continuous }

/-- The one-coordinate case, with the local group as the first factor. -/
def singletonSplitEquiv [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (i : ι) :
    RestrictedGroup G H ≃ₜ* G i × ComplementGroup H {i} := by
  let e := finiteSplitEquiv H hH {i}
  let p := singletonCoordinatesEquiv (G := G) i
  exact
    { toMulEquiv := e.toMulEquiv.trans (p.toMulEquiv.prodCongr (MulEquiv.refl _))
      continuous_toFun := (p.continuous.comp (continuous_fst.comp e.continuous)).prodMk
        (continuous_snd.comp e.continuous)
      continuous_invFun := e.symm.continuous.comp
        ((p.symm.continuous.comp continuous_fst).prodMk continuous_snd) }

@[simp]
theorem singletonSplitEquiv_fst [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (i : ι) (g : RestrictedGroup G H) :
    (singletonSplitEquiv H hH i g).1 = g i := rfl

@[simp]
theorem singletonSplitEquiv_snd [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (i : ι)
    (g : RestrictedGroup G H) (j : {j // j ∉ ({i} : Finset ι)}) :
    (singletonSplitEquiv H hH i g).2 j = g j := rfl

@[simp]
theorem singletonSplitEquiv_symm_apply_same [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (i : ι)
    (x : G i × ComplementGroup H {i}) :
    (singletonSplitEquiv H hH i).symm x i = x.1 := by
  have h := congrArg Prod.fst ((singletonSplitEquiv H hH i).apply_symm_apply x)
  exact h

@[simp]
theorem singletonSplitEquiv_symm_apply_ne [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (i : ι)
    (x : G i × ComplementGroup H {i}) (j : {j // j ∉ ({i} : Finset ι)}) :
    (singletonSplitEquiv H hH i).symm x j = x.2 j := by
  have h := congrArg (fun y : G i × ComplementGroup H {i} => y.2 j)
    ((singletonSplitEquiv H hH i).apply_symm_apply x)
  exact h

/-- Inserting the first factor is exactly Mathlib's single-coordinate monoid hom. -/
@[simp]
theorem singletonSplitEquiv_symm_mulSingle [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) (i : ι) (g : G i) :
    (singletonSplitEquiv H hH i).symm (g, 1) =
      RestrictedProduct.mulSingleMonoidHom H i g := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [RestrictedProduct.mulSingleMonoidHom]
  · have hj : j ∉ ({i} : Finset ι) := by simpa using hji
    rw [show (singletonSplitEquiv H hH i).symm (g, 1) j =
      (1 : ComplementGroup H {i}) ⟨j, hj⟩ from
        singletonSplitEquiv_symm_apply_ne H hH i (g, 1) ⟨j, hj⟩]
    simp [RestrictedProduct.mulSingleMonoidHom, hji]

/-- Hausdorffness is the existing Mathlib restricted-product instance. -/
theorem restrictedGroup_t2Space [∀ i, T2Space (G i)] :
    T2Space (RestrictedGroup G H) := inferInstance

/-- Openness of the reference subgroups supplies Mathlib's topological-group instance. -/
theorem restrictedGroup_isTopologicalGroup [∀ i, IsTopologicalGroup (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsTopologicalGroup (RestrictedGroup G H) := by
  let : Fact (∀ i, IsOpen (H i : Set (G i))) := ⟨hH⟩
  infer_instance

/-- Local compactness uses Mathlib's locally compact restricted-group theorem. -/
theorem restrictedGroup_locallyCompactSpace [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hC : ∀ i, IsCompact (H i : Set (G i))) :
    LocallyCompactSpace (RestrictedGroup G H) := by
  let : Fact (∀ i, IsOpen (H i : Set (G i))) := ⟨hH⟩
  exact RestrictedProduct.locallyCompactSpace_of_group G
    (B := H) (Eventually.of_forall hC)

/-- The continuous injective coordinate map transfers total disconnectedness
from the ordinary product, even though its topology is generally coarser. -/
instance restrictedGroup_totallyDisconnectedSpace [∀ i, TotallyDisconnectedSpace (G i)] :
    TotallyDisconnectedSpace (RestrictedGroup G H) := by
  constructor
  exact isTotallyDisconnected_of_image
    (RestrictedProduct.continuous_coe (R := G) (A := fun i => (H i : Set (G i)))
      (𝓕 := cofinite)).continuousOn DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- Reference-group elements that are trivial on a prescribed finite set. -/
def tailReferenceSubgroup (S : Finset ι) : Subgroup (RestrictedGroup G H) where
  carrier := {g | (∀ i ∈ S, g i = 1) ∧ ∀ i ∉ S, g i ∈ H i}
  one_mem' := ⟨fun _ _ => rfl, fun i _ => (H i).one_mem⟩
  mul_mem' hg hh := ⟨fun i hi => by simp [hg.1 i hi, hh.1 i hi],
    fun i hi => (H i).mul_mem (hg.2 i hi) (hh.2 i hi)⟩
  inv_mem' hg := ⟨fun i hi => by simp [hg.1 i hi],
    fun i hi => (H i).inv_mem (hg.2 i hi)⟩

omit [∀ i, TopologicalSpace (G i)] in
@[simp]
theorem mem_tailReferenceSubgroup (S : Finset ι) (g : RestrictedGroup G H) :
    g ∈ tailReferenceSubgroup H S ↔
      (∀ i ∈ S, g i = 1) ∧ ∀ i ∉ S, g i ∈ H i := Iff.rfl

omit [∀ i, TopologicalSpace (G i)] in
theorem tailReferenceSubgroup_integral (S : Finset ι) {g : RestrictedGroup G H}
    (hg : g ∈ tailReferenceSubgroup H S) (i : ι) : g i ∈ H i := by
  by_cases hi : i ∈ S
  · rw [hg.1 i hi]
    exact (H i).one_mem
  · exact hg.2 i hi

/-- Erase finitely many coordinates in the full product of reference subgroups. -/
def tailReferenceMap (S : Finset ι) (x : ∀ i, H i) : RestrictedGroup G H :=
  RestrictedProduct.structureMap G (fun i => (H i : Set (G i))) cofinite
    (fun i => if i ∈ S then 1 else x i)

theorem continuous_tailReferenceMap (S : Finset ι) :
    Continuous (tailReferenceMap H S) := by
  apply (RestrictedProduct.isEmbedding_structureMap
    (R := G) (A := fun i => (H i : Set (G i))) (𝓕 := cofinite)).continuous.comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simpa only [ite_eq_left hi] using
      (continuous_const : Continuous (fun _ : ∀ i, H i => (1 : H i)))
  · simpa only [ite_eq_right hi] using (continuous_apply i : Continuous (fun x : ∀ i, H i => x i))

omit [∀ i, TopologicalSpace (G i)] in
theorem range_tailReferenceMap (S : Finset ι) :
    Set.range (tailReferenceMap H S) = (tailReferenceSubgroup H S : Set _) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · intro i hi
      simp [tailReferenceMap, hi]
    · intro i hi
      simp [tailReferenceMap, hi]
  · intro hg
    refine ⟨fun i => ⟨g i, tailReferenceSubgroup_integral H S hg i⟩, ?_⟩
    ext i
    by_cases hi : i ∈ S
    · simpa [tailReferenceMap, hi] using (hg.1 i hi).symm
    · simp [tailReferenceMap, hi]

/-- The tails are compact; they are not asserted to be open. -/
theorem isCompact_tailReferenceSubgroup (hC : ∀ i, IsCompact (H i : Set (G i)))
    (S : Finset ι) : IsCompact (tailReferenceSubgroup H S : Set (RestrictedGroup G H)) := by
  let : ∀ i, CompactSpace (H i) := fun i => isCompact_iff_compactSpace.mp (hC i)
  rw [← range_tailReferenceMap H S]
  exact isCompact_range (continuous_tailReferenceMap H S)

/-- Every identity neighborhood contains a compact-reference tail. Compactness
is not needed for this neighborhood extraction. -/
theorem exists_tailReferenceSubgroup_subset (hH : ∀ i, IsOpen (H i : Set (G i)))
    {U : Set (RestrictedGroup G H)} (hU : U ∈ 𝓝 (1 : RestrictedGroup G H)) :
    ∃ S : Finset ι, (tailReferenceSubgroup H S : Set (RestrictedGroup G H)) ⊆ U := by
  have hmap := RestrictedProduct.nhds_eq_map_structureMap hH (1 : ∀ i, H i)
  have hone : RestrictedProduct.structureMap G (fun i => (H i : Set (G i)))
      cofinite (1 : ∀ i, H i) = (1 : RestrictedGroup G H) := by ext; rfl
  rw [hone] at hmap
  rw [hmap, mem_map, nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, V, hV, hVU⟩ := hU
  refine ⟨S, fun g hg => ?_⟩
  let x : ∀ i, H i := fun i => ⟨g i, tailReferenceSubgroup_integral H S hg i⟩
  have hx : x ∈ Set.pi (S : Set ι) V := by
    intro i hi
    have heq : x i = 1 := Subtype.ext (hg.1 i hi)
    rw [heq]
    exact mem_of_mem_nhds (hV i)
  exact hVU hx

theorem exists_tailReferenceSubgroup_le (hH : ∀ i, IsOpen (H i : Set (G i)))
    (U : OpenSubgroup (RestrictedGroup G H)) :
    ∃ S : Finset ι, tailReferenceSubgroup H S ≤ U.toSubgroup :=
  exists_tailReferenceSubgroup_subset H hH (U.isOpen.mem_nhds U.one_mem)

end Langlands.RestrictedTensor
