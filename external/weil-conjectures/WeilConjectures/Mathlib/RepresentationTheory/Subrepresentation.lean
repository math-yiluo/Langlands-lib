/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Artinian.Module
public import WeilConjectures.Mathlib.RepresentationTheory.Basic

/-!
# Subquotients of a representation, and translates of subrepresentations

`Mathlib.RepresentationTheory.Subrepresentation` provides the lattice `Subrepresentation ρ` of
subrepresentations of `ρ : Representation k W V` and, for a single subrepresentation `S`, the
representation `S.toRepresentation` on `S`.  This file adds the subquotient: for
subrepresentations `U ≤ S` the representation of `W` on `S ⧸ U`.

It also adds two order isomorphisms of lattices of subrepresentations: the translation
`U ↦ ρ g U` of subrepresentations of the restriction of `ρ` to a normal subgroup, and the
identification of the lattices of two representations on the same space with the same invariant
subspaces.

`U` is presented inside `S` as `U.toSubmodule.comap S.toSubmodule.subtype`, so that no inclusion
`U ≤ S` is needed to *form* the quotient; the interesting case is of course `U ≤ S`, where the
quotient is the honest subquotient `S / U`.

## Main declarations

* `Subrepresentation.instCompleteLattice`: the subrepresentations form a complete lattice, modular
  and, for finite-dimensional `V`, compactly generated.
* `Subrepresentation.isIrreducible_toRepresentation_iff_isAtom`: a subrepresentation is
  irreducible if and only if it is an atom of the lattice of subrepresentations.
* `Subrepresentation.subquotient`: the representation of `W` on `S ⧸ U`.
* `Subrepresentation.dualAnnihilator`, `Subrepresentation.subquotientDualEquiv`: the annihilator
  `U^⊥` of a subrepresentation in the contragredient, and the equivalence `U^⊥ / S^⊥ ≅ (S / U)^∨`.
* `Subrepresentation.translate`: translation by `g` of subrepresentations of the restriction to a
  normal subgroup.
* `Subrepresentation.orderIsoOfForallIff`: representations with the same invariant subspaces have
  the same lattice of subrepresentations.
* `Subrepresentation.orderIsoMapComap`: subrepresentations correspond along an equivalence of
  representations, and so do the determinant characters of their subquotients
  (`Subrepresentation.detCharacter_subquotient_orderIsoMapComap`).
* `Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible`: Schur's lemma on an irreducible
  subquotient, over an algebraically closed field.
* `Subrepresentation.comap`, `Subrepresentation.map`: preimages and images along intertwining maps,
  and `Subrepresentation.subquotientEquivOfIntertwiningMap`: the equivalence of subquotients
  induced by an intertwining map.
* `Subrepresentation.exists_lt_isIrreducible_subquotient`: a nonzero subrepresentation of a
  finite-dimensional representation has an irreducible quotient.
* `Subrepresentation.exists_subquotient_tprod_equiv`: every irreducible subquotient of `ρ ⊗ σ` is
  a subquotient of `V_i ⊗ E_j` for irreducible subquotients `V_i` of `ρ` and `E_j` of `σ`.

## Blueprint

`Subrepresentation.exists_subquotient_tprod_equiv` and the lemmas it rests on implement the parts
`lemma-tensor-exterior-powers-filtered-representations--1` and
`lemma-tensor-exterior-powers-filtered-representations--3` of
`lemma-tensor-exterior-powers-filtered-representations--3` that `sk-p-tensor` uses.
-/

@[expose] public section

namespace Subrepresentation

section Semiring

variable {A V G : Type*} [Semiring A] [AddCommMonoid V] [Module A V] [Monoid G]
  {ρ : Representation A G V}

/-- The join of a set of subrepresentations: the join of the underlying submodules is stable. -/
instance : SupSet (Subrepresentation ρ) where
  sSup S := ⟨⨆ U ∈ S, U.toSubmodule, fun g v hv ↦ by
    induction hv using Submodule.iSup_induction' with
    | mem U v hv =>
      induction hv using Submodule.iSup_induction' with
      | mem hU v hv => exact Submodule.mem_iSup_of_mem U <|
          Submodule.mem_iSup_of_mem hU (U.apply_mem_toSubmodule g hv)
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy⟩

/-- The meet of a set of subrepresentations: the meet of the underlying submodules is stable. -/
instance : InfSet (Subrepresentation ρ) where
  sInf S := ⟨⨅ U ∈ S, U.toSubmodule, fun g v hv ↦ by
    simp only [Submodule.mem_iInf] at hv ⊢
    exact fun U hU ↦ U.apply_mem_toSubmodule g (hv U hU)⟩

@[simp]
theorem toSubmodule_sSup (S : Set (Subrepresentation ρ)) :
    (sSup S).toSubmodule = ⨆ U ∈ S, U.toSubmodule :=
  rfl

@[simp]
theorem toSubmodule_sInf (S : Set (Subrepresentation ρ)) :
    (sInf S).toSubmodule = ⨅ U ∈ S, U.toSubmodule :=
  rfl

@[simp]
theorem toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ :=
  rfl

@[simp]
theorem toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ :=
  rfl

theorem toSubmodule_le_toSubmodule_iff {S T : Subrepresentation ρ} :
    S.toSubmodule ≤ T.toSubmodule ↔ S ≤ T :=
  Iff.rfl

instance instCompleteLattice : CompleteLattice (Subrepresentation ρ) :=
  toSubmodule_injective.completeLattice _ .rfl .rfl toSubmodule_sup toSubmodule_inf
    toSubmodule_sSup toSubmodule_sInf rfl rfl

@[simp]
theorem toSubmodule_iSup {ι : Sort*} (U : ι → Subrepresentation ρ) :
    (⨆ i, U i).toSubmodule = ⨆ i, (U i).toSubmodule := by
  rw [iSup, toSubmodule_sSup, iSup_range]

theorem disjoint_toSubmodule_iff {S T : Subrepresentation ρ} :
    Disjoint S.toSubmodule T.toSubmodule ↔ Disjoint S T := by
  rw [disjoint_iff, disjoint_iff, ← toSubmodule_inf, ← toSubmodule_bot (ρ := ρ),
    toSubmodule_injective.eq_iff]

/-- A family of subrepresentations is independent if and only if the underlying submodules are. -/
theorem iSupIndep_toSubmodule_iff {ι : Type*} {U : ι → Subrepresentation ρ} :
    iSupIndep (fun i ↦ (U i).toSubmodule) ↔ iSupIndep U := by
  simp only [iSupIndep, ← toSubmodule_iSup, disjoint_toSubmodule_iff]

/-- The subrepresentations of a subrepresentation `S` are the subrepresentations of `ρ` contained
in `S`. -/
def orderIsoIic (S : Subrepresentation ρ) : Subrepresentation S.toRepresentation ≃o Set.Iic S where
  toFun T := ⟨⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨_, T.apply_mem_toSubmodule g hx, rfl⟩⟩, by
    rintro _ ⟨x, -, rfl⟩
    exact x.2⟩
  invFun U := ⟨U.1.toSubmodule.comap S.toSubmodule.subtype,
    fun g _ hx ↦ U.1.apply_mem_toSubmodule g hx⟩
  left_inv T := toSubmodule_injective <|
    Submodule.comap_map_eq_of_injective Subtype.val_injective _
  right_inv U := by
    refine Subtype.ext (toSubmodule_injective ?_)
    exact Submodule.map_comap_eq_self (by rw [Submodule.range_subtype]; exact U.2)
  map_rel_iff' {T T'} := by
    change T.toSubmodule.map _ ≤ T'.toSubmodule.map _ ↔ T.toSubmodule ≤ T'.toSubmodule
    exact Submodule.map_le_map_iff_of_injective Subtype.val_injective _ _

end Semiring

section Ring

variable {A V G : Type*} [Ring A] [AddCommGroup V] [Module A V] [Monoid G]
  {ρ : Representation A G V}

instance : IsModularLattice (Subrepresentation ρ) :=
  ⟨fun {x} {y} {z} h ↦ by
    rw [← toSubmodule_le_toSubmodule_iff]
    exact IsModularLattice.sup_inf_le_assoc_of_le (x := x.toSubmodule) y.toSubmodule
      (z := z.toSubmodule) h⟩

instance [IsNoetherian A V] : IsCompactlyGenerated (Subrepresentation ρ) :=
  have : WellFoundedGT (Subrepresentation ρ) :=
    StrictMono.wellFoundedGT (f := toSubmodule (ρ := ρ)) fun _ _ h ↦ h
  IsCompactlyGenerated.of_wellFoundedGT

end Ring

section Monoid

variable {k V G : Type*} [Field k] [AddCommGroup V] [Module k V] [Monoid G]
  {ρ : Representation k G V}

/-- A subrepresentation is irreducible as a representation if and only if it is an atom of the
lattice of subrepresentations. -/
theorem isIrreducible_toRepresentation_iff_isAtom {S : Subrepresentation ρ} :
    S.toRepresentation.IsIrreducible ↔ IsAtom S :=
  (orderIsoIic S).isSimpleOrder_iff.trans Set.isSimpleOrder_Iic_iff_isAtom

/-- A subrepresentation `S` that is irreducible as a representation is an atom of the lattice of
subrepresentations. -/
theorem isAtom_of_isIrreducible {S : Subrepresentation ρ} (hS : S.toRepresentation.IsIrreducible) :
    IsAtom S :=
  isIrreducible_toRepresentation_iff_isAtom.1 hS

end Monoid

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k W V}

/-- The representation induced on the subquotient `S ⧸ U` of two subrepresentations of `ρ`. -/
noncomputable def subquotient (S U : Subrepresentation ρ) :
    Representation k W (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) where
  toFun w := Submodule.mapQ _ _ ((ρ w).restrict (S.apply_mem_toSubmodule w)) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    simpa only [LinearMap.coe_restrict_apply] using U.apply_mem_toSubmodule w hx)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_one]
    exact congrArg _ (Subtype.ext (by simp))
  map_mul' v w := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul]
    exact congrArg _ (Subtype.ext (by simp))

@[simp]
theorem subquotient_apply_mk (S U : Subrepresentation ρ) (w : W) (x : S.toSubmodule) :
    S.subquotient U w (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨ρ w x, S.apply_mem_toSubmodule w x.2⟩ :=
  rfl

theorem toSubmodule_le_toSubmodule {S T : Subrepresentation ρ} :
    S.toSubmodule ≤ T.toSubmodule ↔ S ≤ T :=
  Iff.rfl

section Dual

/-- The *annihilator* `U^⊥` of a subrepresentation `U`: the linear forms vanishing on `U`, a
subrepresentation of the contragredient representation. -/
def dualAnnihilator (U : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := U.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule w f hf := by
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro x hx
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    exact hf _ (U.apply_mem_toSubmodule w⁻¹ hx)

/-- A linear form lies in `U^⊥` if and only if it vanishes on `U`. -/
theorem mem_dualAnnihilator {U : Subrepresentation ρ} {f : Module.Dual k V} :
    f ∈ U.dualAnnihilator ↔ ∀ x ∈ U, f x = 0 :=
  Submodule.mem_dualAnnihilator f

/-- Taking annihilators reverses inclusions. -/
theorem dualAnnihilator_antitone : Antitone (dualAnnihilator : Subrepresentation ρ → _) :=
  fun _ _ h ↦ Submodule.dualAnnihilator_anti (toSubmodule_le_toSubmodule.2 h)

@[simp]
theorem dualAnnihilator_bot : (⊥ : Subrepresentation ρ).dualAnnihilator = ⊤ :=
  toSubmodule_injective Submodule.dualAnnihilator_bot

@[simp]
theorem dualAnnihilator_top : (⊤ : Subrepresentation ρ).dualAnnihilator = ⊥ :=
  toSubmodule_injective Submodule.dualAnnihilator_top

/-- For `U ≤ S`, a linear form on `V` vanishing on `U` induces a linear form on the subquotient
`S / U`. -/
noncomputable def dualAnnihilatorToDualSubquotient (U S : Subrepresentation ρ) :
    U.dualAnnihilator.toSubmodule →ₗ[k]
      Module.Dual k (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) where
  toFun f := Submodule.liftQ _ ((f : Module.Dual k V) ∘ₗ S.toSubmodule.subtype) fun x hx ↦
    mem_dualAnnihilator.1 f.2 x hx
  map_add' _ _ := Submodule.linearMap_qext _ rfl
  map_smul' _ _ := Submodule.linearMap_qext _ rfl

@[simp]
theorem dualAnnihilatorToDualSubquotient_apply_mk (U S : Subrepresentation ρ)
    (f : U.dualAnnihilator.toSubmodule) (x : S.toSubmodule) :
    dualAnnihilatorToDualSubquotient U S f (Submodule.Quotient.mk x) = (f : Module.Dual k V) x :=
  rfl

/-- The kernel of `U^⊥ → (S / U)^∨` is `S^⊥`. -/
theorem ker_dualAnnihilatorToDualSubquotient (U S : Subrepresentation ρ) :
    LinearMap.ker (dualAnnihilatorToDualSubquotient U S) =
      S.dualAnnihilator.toSubmodule.comap U.dualAnnihilator.toSubmodule.subtype := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨fun h ↦ mem_dualAnnihilator.2 fun x hx ↦ ?_, fun h ↦ Submodule.linearMap_qext _ ?_⟩
  · simpa using congr($h (Submodule.Quotient.mk ⟨x, hx⟩))
  · exact LinearMap.ext fun x ↦ mem_dualAnnihilator.1 h x x.2

/-- For `U ≤ S`, every linear form on `S / U` comes from a linear form on `V` vanishing on `U`. -/
theorem dualAnnihilatorToDualSubquotient_surjective {U S : Subrepresentation ρ} (h : U ≤ S) :
    Function.Surjective (dualAnnihilatorToDualSubquotient U S) := by
  intro φ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (φ ∘ₗ Submodule.mkQ _ : S.toSubmodule →ₗ[k] k)
  have hgU : g ∈ U.dualAnnihilator := mem_dualAnnihilator.2 fun x hx ↦ by
    have := congr($hg ⟨x, h hx⟩)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact (congrArg φ ((Submodule.Quotient.mk_eq_zero _).2 hx)).trans (map_zero φ)
  exact ⟨⟨g, hgU⟩, Submodule.linearMap_qext _ hg⟩

/-- **The contragredient of a subquotient.** For subrepresentations `U ≤ S`, the subquotient
`U^⊥ / S^⊥` of the contragredient representation is the contragredient of the subquotient `S / U`.
(blueprint: part L3 of `lemma-tensor-exterior-powers-filtered-representations--3`) -/
noncomputable def subquotientDualEquiv {U S : Subrepresentation ρ} (h : U ≤ S) :
    (U.dualAnnihilator.subquotient S.dualAnnihilator).Equiv (S.subquotient U).dual :=
  .mk ((Submodule.quotEquivOfEq _ _ (ker_dualAnnihilatorToDualSubquotient U S).symm).trans
    ((dualAnnihilatorToDualSubquotient U S).quotKerEquivOfSurjective
      (dualAnnihilatorToDualSubquotient_surjective h))) fun w ↦ by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun f ↦ Submodule.linearMap_qext _
      (LinearMap.ext fun x ↦ ?_))
    rfl

end Dual

section Equiv

variable {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k W V'}

/-- Subrepresentations correspond along an equivalence of representations `e`: `S ↦ e(S)`. -/
def orderIsoMapComap (e : ρ.Equiv σ) : Subrepresentation ρ ≃o Subrepresentation σ where
  toFun S := ⟨S.toSubmodule.map (e.toLinearEquiv : V →ₗ[k] V'), by
    rintro w _ ⟨x, hx, rfl⟩
    exact ⟨ρ w x, S.apply_mem_toSubmodule w hx, e.apply_apply w x⟩⟩
  invFun S := ⟨S.toSubmodule.comap (e.toLinearEquiv : V →ₗ[k] V'), by
    intro w x hx
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, e.toLinearEquiv_apply, e.coe_toIntertwiningMap,
      e.apply_apply]
    exact S.apply_mem_toSubmodule w hx⟩
  left_inv S := toSubmodule_injective
    (Submodule.comap_map_eq_of_injective e.toLinearEquiv.injective _)
  right_inv S := toSubmodule_injective
    (Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective _)
  map_rel_iff' {S T} := by
    rw [← toSubmodule_le_toSubmodule, ← toSubmodule_le_toSubmodule]
    exact Submodule.map_le_map_iff_of_injective e.toLinearEquiv.injective _ _

/-- `y` lies in `e(S)` if and only if `e⁻¹ y` lies in `S`. -/
theorem mem_orderIsoMapComap_iff (e : ρ.Equiv σ) (S : Subrepresentation ρ) {y : V'} :
    y ∈ orderIsoMapComap e S ↔ e.symm y ∈ S :=
  Submodule.mem_map_equiv (p := S.toSubmodule) (e := e.toLinearEquiv)

/-- If `x` lies in `S`, then `e x` lies in `e(S)`. -/
theorem apply_mem_orderIsoMapComap (e : ρ.Equiv σ) (S : Subrepresentation ρ) {x : V}
    (hx : x ∈ S) : e x ∈ orderIsoMapComap e S :=
  ⟨x, hx, rfl⟩

/-- The equivalence between the subquotients `S ⧸ U` and `e(S) ⧸ e(U)` induced by an equivalence
of representations `e`. -/
noncomputable def subquotientEquiv (e : ρ.Equiv σ) (S U : Subrepresentation ρ) :
    (S.subquotient U).Equiv ((orderIsoMapComap e S).subquotient (orderIsoMapComap e U)) :=
  .mk (Submodule.Quotient.equiv _ _ (e.toLinearEquiv.submoduleMap S.toSubmodule) <| by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.subtype_apply]
    exact (mem_orderIsoMapComap_iff e U).symm) fun w ↦ by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
      subquotient_apply_mk, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (e.apply_apply w x)

/-- The subquotients `S ⧸ U` and `e(S) ⧸ e(U)` along an equivalence of representations `e` have the
same determinant character. -/
theorem detCharacter_subquotient_orderIsoMapComap (e : ρ.Equiv σ) (S U : Subrepresentation ρ) :
    ((orderIsoMapComap e S).subquotient (orderIsoMapComap e U)).detCharacter =
      (S.subquotient U).detCharacter :=
  (subquotientEquiv e S U).detCharacter_eq

/-- Subquotients can be transported along an equivalence of representations `e : ρ ≅ σ`: every
subquotient `S / U` of `σ` is equivalent to a subquotient `S' / U'` of `ρ`. -/
theorem exists_subquotient_equiv_of_equiv (e : ρ.Equiv σ) (U S : Subrepresentation σ) :
    ∃ U' S' : Subrepresentation ρ, Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) :=
  ⟨_, _, ⟨(subquotientEquiv e.symm S U).symm⟩⟩

end Equiv

/-- The subquotient `S ⧸ ⊥` is equivalent to `S`. -/
noncomputable def subquotientBotEquiv (S : Subrepresentation ρ) :
    (S.subquotient ⊥).Equiv S.toRepresentation :=
  .mk (Submodule.quotEquivOfEqBot _ <| by
    ext x
    exact ⟨fun h ↦ (Submodule.mem_bot k).2 (Subtype.ext ((Submodule.mem_bot k).1 h)),
      fun h ↦ by rw [(Submodule.mem_bot k).1 h]; exact zero_mem _⟩) fun w ↦
    Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ rfl)

/-- The subquotient `S ⧸ ⊥` has the same determinant character as `S`. -/
theorem detCharacter_subquotient_bot (S : Subrepresentation ρ) :
    (S.subquotient ⊥).detCharacter = S.toRepresentation.detCharacter :=
  (subquotientBotEquiv S).detCharacter_eq.symm

/-- **Schur's lemma** on a subquotient: over an algebraically closed field, an endomorphism that
commutes with the action and preserves `U` and `S` acts on an irreducible subquotient `S ⧸ U` by a
scalar. -/
theorem exists_apply_sub_smul_mem_of_isIrreducible [IsAlgClosed k] [FiniteDimensional k V]
    {U S : Subrepresentation ρ} (hirr : (S.subquotient U).IsIrreducible) (f : V →ₗ[k] V)
    (hf : ∀ w x, f (ρ w x) = ρ w (f x)) (hU : ∀ x ∈ U, f x ∈ U) (hS : ∀ x ∈ S, f x ∈ S) :
    ∃ c : k, ∀ x ∈ S, f x - c • x ∈ U := by
  let fQ : Representation.IntertwiningMap (S.subquotient U) (S.subquotient U) :=
    { toLinearMap := Submodule.mapQ _ _ (f.restrict hS) fun x hx ↦ hU _ hx
      isIntertwining' w := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
          subquotient_apply_mk]
        congr 1
        exact Subtype.ext (hf w x) }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := S.subquotient U)).2 fQ
  refine ⟨c, fun x hx ↦ ?_⟩
  have h : c • (Submodule.Quotient.mk ⟨x, hx⟩ :
      S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) =
      Submodule.Quotient.mk ⟨f x, hS x hx⟩ :=
    congrArg (fun g : Representation.IntertwiningMap (S.subquotient U) (S.subquotient U) ↦
      g (Submodule.Quotient.mk ⟨x, hx⟩)) hc
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq] at h
  exact h

end Subrepresentation

namespace Subrepresentation

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

section Translate

variable (ρ : Representation k G V) (N : Subgroup G) [N.Normal]

/-- For a normal subgroup `N` of `G`, the translate `ρ g U` of a subrepresentation `U` of the
restriction of `ρ` to `N` is again a subrepresentation: `n (g u) = g ((g⁻¹ n g) u)`. -/
def translateFun (g : G) (U : Subrepresentation (ρ.comp N.subtype)) :
    Subrepresentation (ρ.comp N.subtype) where
  toSubmodule := U.toSubmodule.map (ρ g)
  apply_mem_toSubmodule n := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨ρ (g⁻¹ * n * g) u, U.apply_mem_toSubmodule ⟨g⁻¹ * n * g, ?_⟩ hu, ?_⟩
    · simpa using ‹N.Normal›.conj_mem _ n.2 g⁻¹
    · simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]

variable {ρ N} in
theorem mem_translateFun {g : G} {U : Subrepresentation (ρ.comp N.subtype)} {v : V} :
    v ∈ translateFun ρ N g U ↔ ρ g⁻¹ v ∈ U := by
  change v ∈ U.toSubmodule.map (ρ g) ↔ _
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro hv
    refine ⟨_, hv, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Translation `U ↦ ρ g U` by an element `g ∈ G` is an order automorphism of the lattice of
subrepresentations of the restriction of `ρ` to a normal subgroup `N`. -/
def translate (g : G) :
    Subrepresentation (ρ.comp N.subtype) ≃o Subrepresentation (ρ.comp N.subtype) where
  toFun := translateFun ρ N g
  invFun := translateFun ρ N g⁻¹
  left_inv U := SetLike.ext fun v ↦ by
    simp only [mem_translateFun, inv_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  right_inv U := SetLike.ext fun v ↦ by
    simp only [mem_translateFun, inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]
  map_rel_iff' {U U'} := by
    change translateFun ρ N g U ≤ translateFun ρ N g U' ↔ U ≤ U'
    refine ⟨fun h v hv ↦ ?_, fun h v hv ↦ mem_translateFun.2 (h (mem_translateFun.1 hv))⟩
    have := @h (ρ g v) (by
      rwa [mem_translateFun, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply])
    rwa [mem_translateFun, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this

variable {ρ N} in
theorem mem_translate {g : G} {U : Subrepresentation (ρ.comp N.subtype)} {v : V} :
    v ∈ translate ρ N g U ↔ ρ g⁻¹ v ∈ U :=
  mem_translateFun

end Translate

section OrderIsoOfForallIff

variable {H : Type*} [Monoid H] {ρ : Representation k G V} {σ : Representation k H V}

/-- Two representations on the same module with the same invariant submodules have the same
subrepresentations. -/
def orderIsoOfForallIff
    (h : ∀ U : Submodule k V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) ↔ ∀ g, ∀ v ∈ U, σ g v ∈ U) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U := ⟨U.toSubmodule, fun g _ hv ↦ (h U.toSubmodule).1
    (fun g _ hv ↦ U.apply_mem_toSubmodule g hv) g _ hv⟩
  invFun U := ⟨U.toSubmodule, fun g _ hv ↦ (h U.toSubmodule).2
    (fun g _ hv ↦ U.apply_mem_toSubmodule g hv) g _ hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end OrderIsoOfForallIff

end Subrepresentation

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k W V}
variable {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k W V'}

/-- An equivalence of representations preserves irreducibility. -/
theorem _root_.Representation.Equiv.isIrreducible_iff (e : ρ.Equiv σ) :
    ρ.IsIrreducible ↔ σ.IsIrreducible :=
  (orderIsoMapComap e).isSimpleOrder_iff

/-- The space of an irreducible representation is nontrivial. -/
theorem _root_.Representation.IsIrreducible.nontrivial (hirr : ρ.IsIrreducible) : Nontrivial V := by
  refine not_subsingleton_iff_nontrivial.1 fun _ ↦ hirr.bot_ne_top ?_
  ext x
  simp [Subsingleton.elim x 0]

theorem mem_inf {U S : Subrepresentation ρ} {x : V} : x ∈ U ⊓ S ↔ x ∈ U ∧ x ∈ S :=
  Iff.rfl

theorem mem_sup {U S : Subrepresentation ρ} {x : V} : x ∈ U ⊔ S ↔ ∃ a ∈ U, ∃ b ∈ S, a + b = x :=
  Submodule.mem_sup

instance [FiniteDimensional k V] : WellFoundedLT (Subrepresentation ρ) :=
  StrictMono.wellFoundedLT (f := toSubmodule) fun _ _ h ↦ h

instance [FiniteDimensional k V] : WellFoundedGT (Subrepresentation ρ) :=
  StrictMono.wellFoundedGT (f := toSubmodule) fun _ _ h ↦ h

section IntertwiningMap

/-- The preimage `f⁻¹(S)` of a subrepresentation under an intertwining map. -/
def comap (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule w x hx := by
    simp only [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
      f.isIntertwining] at hx ⊢
    exact S.apply_mem_toSubmodule w hx

@[simp]
theorem mem_comap {f : ρ.IntertwiningMap σ} {S : Subrepresentation σ} {x : V} :
    x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl

/-- The image `f(S)` of a subrepresentation under an intertwining map. -/
def map (f : ρ.IntertwiningMap σ) (S : Subrepresentation ρ) : Subrepresentation σ where
  toSubmodule := S.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule w := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ρ w x, S.apply_mem_toSubmodule w hx, f.isIntertwining _ _ w x⟩

theorem mem_map {f : ρ.IntertwiningMap σ} {S : Subrepresentation ρ} {y : V'} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl

/-- An intertwining map `f` with `f(S) ⊆ S'` and `f(U ∩ S) ⊆ U'`, which is injective modulo `U` on
`S` and surjective onto `S'` modulo `U'`, induces an equivalence of subquotients
`S / U ≃ S' / U'`. -/
noncomputable def subquotientEquivOfIntertwiningMap (f : ρ.IntertwiningMap σ)
    {U S : Subrepresentation ρ} {U' S' : Subrepresentation σ}
    (hS : ∀ x ∈ S, f x ∈ S') (hU : ∀ x ∈ S, x ∈ U → f x ∈ U')
    (hinj : ∀ x ∈ S, f x ∈ U' → x ∈ U) (hsurj : ∀ y ∈ S', ∃ x ∈ S, f x - y ∈ U') :
    (S.subquotient U).Equiv (S'.subquotient U') :=
  Representation.IntertwiningMap.ofBijective
    { toLinearMap := Submodule.mapQ _ _ (f.toLinearMap.restrict hS) fun x hx ↦ hU x x.2 hx
      isIntertwining' w := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
          subquotient_apply_mk]
        congr 1
        exact Subtype.ext (f.isIntertwining _ _ w x) } <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun q hq ↦ ?_, fun q ↦ ?_⟩
    · induction q using Submodule.Quotient.induction_on with | _ x
      change Submodule.Quotient.mk _ = 0 at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
      exact hinj x x.2 hq
    · induction q using Submodule.Quotient.induction_on with | _ y
      obtain ⟨x, hx, hxy⟩ := hsurj y y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      change Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.eq]
      exact hxy

/-- An intertwining map that is surjective identifies the subquotient `f⁻¹(S) / f⁻¹(U)` with
`S / U`. -/
noncomputable def subquotientComapEquiv (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (U S : Subrepresentation σ) :
    ((comap f S).subquotient (comap f U)).Equiv (S.subquotient U) :=
  subquotientEquivOfIntertwiningMap f (fun _ hx ↦ hx) (fun _ _ hx ↦ hx) (fun _ _ hx ↦ hx)
    fun y _ ↦ by
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨x, ‹f x ∈ S›, by rw [sub_self]; exact U.toSubmodule.zero_mem⟩

/-- An injective intertwining map `f` identifies the subquotient `f(S) / f(U)` with `S / U`. -/
noncomputable def subquotientMapEquiv (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (U S : Subrepresentation ρ) : ((map f S).subquotient (map f U)).Equiv (S.subquotient U) :=
  (subquotientEquivOfIntertwiningMap f (U := U) (S := S) (U' := map f U) (S' := map f S)
    (fun x hx ↦ ⟨x, hx, rfl⟩) (fun x _ hx ↦ ⟨x, hx, rfl⟩)
    (fun x _ hx ↦ by
      obtain ⟨y, hy, hxy⟩ := mem_map.1 hx
      exact hf hxy ▸ hy) fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
      exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩).symm

theorem map_bot (f : ρ.IntertwiningMap σ) : map f ⊥ = ⊥ :=
  toSubmodule_injective (Submodule.map_bot _)

theorem comap_top (f : ρ.IntertwiningMap σ) : comap f ⊤ = ⊤ :=
  toSubmodule_injective (Submodule.comap_top _)

theorem map_mono (f : ρ.IntertwiningMap σ) {S T : Subrepresentation ρ} (h : S ≤ T) :
    map f S ≤ map f T :=
  fun _ ⟨x, hx, hxy⟩ ↦ ⟨x, h hx, hxy⟩

theorem comap_mono (f : ρ.IntertwiningMap σ) {S T : Subrepresentation σ} (h : S ≤ T) :
    comap f S ≤ comap f T :=
  fun _ hx ↦ h hx

end IntertwiningMap

/-- The subquotient `S / (U ∩ S)` is the subquotient `S / U`. -/
noncomputable def subquotientInfEquiv (U S : Subrepresentation ρ) :
    (S.subquotient (U ⊓ S)).Equiv (S.subquotient U) :=
  subquotientEquivOfIntertwiningMap (.id ρ) (fun _ hx ↦ hx) (fun _ _ hx ↦ (mem_inf.1 hx).1)
    (fun _ hxS hx ↦ mem_inf.2 ⟨hx, hxS⟩) fun y hy ↦ ⟨y, hy, by
      rw [Representation.IntertwiningMap.id_apply, sub_self]; exact U.toSubmodule.zero_mem⟩

/-- The **second isomorphism theorem** for subrepresentations: `S / (U ⊓ S) ≅ (U ⊔ S) / U`. -/
noncomputable def subquotientSupEquiv (U S : Subrepresentation ρ) :
    (S.subquotient (U ⊓ S)).Equiv ((U ⊔ S).subquotient U) :=
  subquotientEquivOfIntertwiningMap (.id ρ) (fun x hx ↦
    mem_sup.2 ⟨0, U.toSubmodule.zero_mem, x, hx, zero_add x⟩)
    (fun _ _ hx ↦ (mem_inf.1 hx).1) (fun _ hxS hxU ↦ mem_inf.2 ⟨hxU, hxS⟩) fun y hy ↦ by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 hy
      refine ⟨b, hb, ?_⟩
      rw [Representation.IntertwiningMap.id_apply, sub_add_cancel_right]
      exact U.toSubmodule.neg_mem ha

/-- If the subquotient `S / U` is irreducible, then `U ∩ S < S`. -/
theorem inf_lt_of_isIrreducible {U S : Subrepresentation ρ}
    (hirr : (S.subquotient U).IsIrreducible) : U ⊓ S < S := by
  refine inf_le_right.lt_of_ne fun h ↦ hirr.bot_ne_top (eq_top_iff.2 fun q _ ↦ ?_)
  induction q using Submodule.Quotient.induction_on with | _ x
  refine (Submodule.mem_bot k).2 ((Submodule.Quotient.mk_eq_zero _).2 ?_)
  exact (mem_inf.1 (h.symm ▸ x.2 : (x : V) ∈ U ⊓ S)).1

/-- The subrepresentation `⊤` is equivalent to `ρ`. -/
def topEquiv : (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ :=
  .mk Submodule.topEquiv fun _ ↦ rfl

/-- The subquotient `⊤ / ⊥` of `ρ` is equivalent to `ρ`. -/
noncomputable def topSubquotientBotEquiv (ρ : Representation k W V) :
    ((⊤ : Subrepresentation ρ).subquotient ⊥).Equiv ρ :=
  (subquotientBotEquiv ⊤).trans topEquiv

/-- If `S / U` is irreducible and a subrepresentation `T` meets `S` outside of `U`, then `T ∩ S`
generates `S` modulo `U`. -/
theorem exists_mem_inf_sub_mem_of_isIrreducible {U S T : Subrepresentation ρ}
    (hirr : (S.subquotient U).IsIrreducible) (hT : ¬ T ⊓ S ≤ U) {y : V} (hy : y ∈ S) :
    ∃ x ∈ T ⊓ S, x - y ∈ U := by
  let I : Subrepresentation (S.subquotient U) :=
    ⟨(T.toSubmodule.comap S.toSubmodule.subtype).map (Submodule.mkQ _), by
      rintro w _ ⟨x, hx, rfl⟩
      exact ⟨⟨ρ w x, S.apply_mem_toSubmodule w x.2⟩, T.apply_mem_toSubmodule w hx, rfl⟩⟩
  rcases hirr.eq_bot_or_eq_top I with h | h
  · refine absurd (fun x hx ↦ ?_) hT
    have hI : Submodule.Quotient.mk ⟨x, hx.2⟩ ∈ I := ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    rw [h] at hI
    have := (Submodule.mem_bot k).1 hI
    rwa [Submodule.Quotient.mk_eq_zero] at this
  · have hI : Submodule.Quotient.mk ⟨y, hy⟩ ∈ I := h ▸ Submodule.mem_top
    obtain ⟨x, hxT, hx⟩ := hI
    refine ⟨x, ⟨hxT, x.2⟩, ?_⟩
    exact (Submodule.Quotient.eq (U.toSubmodule.comap S.toSubmodule.subtype)).1 hx

/-- A nonzero subrepresentation `A` of a finite-dimensional representation has a maximal proper
subrepresentation `B`, so that `A / B` is irreducible. -/
theorem exists_lt_isIrreducible_subquotient [FiniteDimensional k V] {A : Subrepresentation ρ}
    (hA : A ≠ ⊥) : ∃ B < A, (A.subquotient B).IsIrreducible := by
  obtain ⟨B, hBA, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {B | B < A}
    ⟨⊥, bot_lt_iff_ne_bot.2 hA⟩
  replace hBA : B < A := hBA
  refine ⟨B, hBA, ?_⟩
  obtain ⟨x, hxA, hxB⟩ := IsConcreteLE.exists_of_lt hBA
  have hx : (Submodule.Quotient.mk ⟨x, hxA⟩ :
      A.toSubmodule ⧸ B.toSubmodule.comap A.toSubmodule.subtype) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have : Nontrivial (Subrepresentation (A.subquotient B)) := ⟨⟨⊥, ⊤, fun h ↦ hx <| by
    have : Submodule.Quotient.mk ⟨x, hxA⟩ ∈ (⊤ : Subrepresentation (A.subquotient B)) :=
      Submodule.mem_top
    rw [← h] at this
    exact (Submodule.mem_bot k).1 this⟩⟩
  refine ⟨fun T ↦ ?_⟩
  -- the preimage `T'` of `T` in `A`, which lies between `B` and `A`
  let T' : Subrepresentation ρ :=
    ⟨(T.toSubmodule.comap (Submodule.mkQ _)).map A.toSubmodule.subtype, by
      rintro w _ ⟨y, hy, rfl⟩
      exact ⟨⟨ρ w y, A.apply_mem_toSubmodule w y.2⟩, T.apply_mem_toSubmodule w hy, rfl⟩⟩
  have hmem (y : A.toSubmodule) : (y : V) ∈ T' ↔ Submodule.Quotient.mk y ∈ T :=
    ⟨fun ⟨y', hy', h⟩ ↦ Subtype.ext h ▸ hy', fun h ↦ ⟨y, h, rfl⟩⟩
  have hBT : B ≤ T' := fun y hy ↦ (hmem ⟨y, hBA.le hy⟩).2 <| by
    rw [(Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 hy]
    exact T.toSubmodule.zero_mem
  have hTA : T' ≤ A := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rcases hTA.lt_or_eq with hlt | heq
  · have hTB : T' = B := (lt_or_eq_of_le hBT).resolve_left (hmax T' hlt) |>.symm
    refine Or.inl (eq_bot_iff.2 fun q hq ↦ ?_)
    induction q using Submodule.Quotient.induction_on with | _ y
    have := (hmem y).2 hq
    rw [hTB] at this
    exact (Submodule.mem_bot k).2 ((Submodule.Quotient.mk_eq_zero _).2 this)
  · refine Or.inr (eq_top_iff.2 fun q _ ↦ ?_)
    induction q using Submodule.Quotient.induction_on with | _ y
    have hy : (y : V) ∈ T' := by rw [heq]; exact y.2
    exact (hmem y).1 hy

section TensorProduct

open TensorProduct

/-- Peeling off the first factor of a tensor product, for a subrepresentation `A`: every
irreducible subquotient of `A ⊗ σ` is equivalent to a subquotient of `(SV / UV) ⊗ σ` for an
irreducible subquotient `SV / UV` of `ρ`. The proof runs along a composition series of `A`,
using the right exactness of `- ⊗ σ`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--1`,
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem exists_subquotient_tprod_equiv_of_subrepresentation [FiniteDimensional k V]
    (A : Subrepresentation ρ) {U S : Subrepresentation (A.toRepresentation.tprod σ)}
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ UV SV : Subrepresentation ρ, UV < SV ∧ (SV.subquotient UV).IsIrreducible ∧
      ∃ U' S' : Subrepresentation ((SV.subquotient UV).tprod σ),
        Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  induction A using WellFoundedLT.induction with | _ A ih
  by_cases hA : A = ⊥
  · -- `A ⊗ σ` is zero, so it has no irreducible subquotient
    subst hA
    have h0 (z : (⊥ : Subrepresentation ρ).toSubmodule ⊗[k] V') : z = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        rw [show a = 0 from Subtype.ext ((Submodule.mem_bot k).1 a.2), TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    have := hirr.nontrivial
    obtain ⟨q₁, q₂, hq⟩ :=
      exists_pair_ne (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype)
    induction q₁ using Submodule.Quotient.induction_on with | _ x
    induction q₂ using Submodule.Quotient.induction_on with | _ y
    exact (hq (congrArg _ (Subtype.ext ((h0 x).trans (h0 y).symm)))).elim
  obtain ⟨B, hBA, hB⟩ := exists_lt_isIrreducible_subquotient hA
  let incl : B.toRepresentation.IntertwiningMap A.toRepresentation :=
    ⟨Submodule.inclusion hBA.le, fun _ ↦ rfl⟩
  let quot : A.toRepresentation.IntertwiningMap (A.subquotient B) :=
    ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
  let ι := incl.rTensor σ
  let π := quot.rTensor σ
  have hexact : Function.Exact ι π :=
    rTensor_exact V' (fun y ↦ by
      change Submodule.mkQ _ y = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)
      (Submodule.mkQ_surjective _)
  by_cases h : ι.range ⊓ S ≤ U
  · -- the subquotient survives in `(A / B) ⊗ σ`
    have hinj (x) (hxS : x ∈ S) (hx : π x ∈ map π (U ⊓ S)) : x ∈ U := by
      obtain ⟨u, hu, hux⟩ := mem_map.1 hx
      have hxu : x - u ∈ ι.range := (hexact (x - u)).1 (by rw [map_sub, hux, sub_self])
      have := h (mem_inf.2 ⟨hxu, S.toSubmodule.sub_mem hxS (mem_inf.1 hu).2⟩)
      have hx := U.toSubmodule.add_mem this (mem_inf.1 hu).1
      rwa [sub_add_cancel] at hx
    refine ⟨B, A, hBA, hB, map π (U ⊓ S), map π S,
      ⟨(subquotientEquivOfIntertwiningMap π (fun x hx ↦ mem_map.2 ⟨x, hx, rfl⟩)
        (fun x hxS hxU ↦ mem_map.2 ⟨x, mem_inf.2 ⟨hxU, hxS⟩, rfl⟩) hinj
        fun y hy ↦ ?_).symm⟩⟩
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
    refine ⟨x, hx, ?_⟩
    rw [sub_self]
    exact (map π (U ⊓ S)).toSubmodule.zero_mem
  · -- the subquotient comes from `B ⊗ σ`
    let e := subquotientEquivOfIntertwiningMap ι (U := comap ι U) (S := comap ι S)
      (U' := U) (S' := S) (fun _ hx ↦ hx) (fun _ _ hx ↦ hx) (fun _ _ hx ↦ hx) fun y hy ↦ by
        obtain ⟨x, hx, hxy⟩ := exists_mem_inf_sub_mem_of_isIrreducible hirr h hy
        obtain ⟨⟨x', rfl⟩, hxS⟩ := mem_inf.1 hx
        exact ⟨x', hxS, hxy⟩
    obtain ⟨UV, SV, hUV, hV, U', S', ⟨e'⟩⟩ := ih B hBA (e.isIrreducible_iff.2 hirr)
    exact ⟨UV, SV, hUV, hV, U', S', ⟨e'.trans e⟩⟩

/-- Peeling off the first factor of a tensor product: every irreducible subquotient of `ρ ⊗ σ`,
for a finite-dimensional `ρ`, is equivalent to a subquotient of `(SV / UV) ⊗ σ` for an irreducible
subquotient `SV / UV` of `ρ`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--1`,
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem exists_subquotient_tprod_left_equiv [FiniteDimensional k V]
    {U S : Subrepresentation (ρ.tprod σ)} (hirr : (S.subquotient U).IsIrreducible) :
    ∃ UV SV : Subrepresentation ρ, UV < SV ∧ (SV.subquotient UV).IsIrreducible ∧
      ∃ U' S' : Subrepresentation ((SV.subquotient UV).tprod σ),
        Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  let g : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap ρ :=
    ⟨Submodule.subtype _, fun _ ↦ rfl⟩
  have hg : Function.Surjective (g.rTensor σ) :=
    LinearMap.rTensor_surjective V' fun x ↦ ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  let e := subquotientComapEquiv (g.rTensor σ) hg U S
  obtain ⟨UV, SV, hUV, hV, U', S', ⟨e'⟩⟩ :=
    exists_subquotient_tprod_equiv_of_subrepresentation ⊤ (e.isIrreducible_iff.2 hirr)
  exact ⟨UV, SV, hUV, hV, U', S', ⟨e'.trans e⟩⟩

/-- The irreducible subquotients of a tensor product: every irreducible subquotient `Q` of
`ρ ⊗ σ`, for finite-dimensional `ρ` and `σ`, is equivalent to a subquotient of `V_i ⊗ E_j` for
irreducible subquotients `V_i = SV / UV` of `ρ` and `E_j = SE / UE` of `σ`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--1`,
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem exists_subquotient_tprod_equiv [FiniteDimensional k V] [FiniteDimensional k V']
    {U S : Subrepresentation (ρ.tprod σ)} (hirr : (S.subquotient U).IsIrreducible) :
    ∃ UV SV : Subrepresentation ρ, ∃ UE SE : Subrepresentation σ, UV < SV ∧ UE < SE ∧
      (SV.subquotient UV).IsIrreducible ∧ (SE.subquotient UE).IsIrreducible ∧
      ∃ U' S' : Subrepresentation ((SV.subquotient UV).tprod (SE.subquotient UE)),
        Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  obtain ⟨UV, SV, hUV, hV, U₁, S₁, ⟨e₁⟩⟩ := exists_subquotient_tprod_left_equiv hirr
  let c₁ := Representation.TensorProduct.comm (SV.subquotient UV) σ
  let e₂ := subquotientEquiv c₁ S₁ U₁
  obtain ⟨UE, SE, hUE, hE, U₃, S₃, ⟨e₃⟩⟩ :=
    exists_subquotient_tprod_left_equiv (e₂.symm.isIrreducible_iff.2 (e₁.isIrreducible_iff.2 hirr))
  let c₄ := Representation.TensorProduct.comm (SE.subquotient UE) (SV.subquotient UV)
  exact ⟨UV, SV, UE, SE, hUV, hUE, hV, hE, _, _, ⟨(subquotientEquiv c₄ S₃ U₃).symm.trans
    (e₃.trans (e₂.symm.trans e₁))⟩⟩

end TensorProduct

end Subrepresentation
