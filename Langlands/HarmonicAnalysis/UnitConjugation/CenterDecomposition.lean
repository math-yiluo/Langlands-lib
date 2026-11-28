import Langlands.HarmonicAnalysis.UnitConjugation.TraceFormPairing
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalVanishingTransport
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct

/-!
# Test functions on the center and on its orthogonal

Let `A` be a finite-dimensional semisimple algebra over a topological field `F` of
characteristic zero, with its module topology, and let `z` be its center and `V = z^⊥` the
orthogonal of `z` for the trace form (`centerOrthogonal`). Then `A = z ⊕ V`
(`isCompl_center_centerOrthogonal`); this module makes the decomposition topological and
transports test functions and orbital integrals along it:

* subspaces of a space with the module topology carry the module topology
  (`isModuleTopology_submodule`), and `centerDecomposition : z × V ≃L[F] A`,
  `(Z, Y) ↦ Z + Y`;
* conjugation by a unit fixes the `z`-component and acts on `V` (`centerOrthogonalConj`);
* `restrictCenterOrthogonal f` is the restriction of a test function on `A` to `V`, and
  `extendTest α β` is the test function `X ↦ α(Z) β(Y)` for `X = Z + Y`;
* `CenterOrthogonalVanishing F A β`: for every test function `α` on `z` and every regular
  `Y ∈ V`, the orbital integrals of `extendTest α β` at `Y` vanish. Then every
  `extendTest α β` lies in `D₀` (`CenterOrthogonalVanishing.regularOrbitalVanishing`), the
  restriction of a function of `D₀` satisfies the condition
  (`RegularOrbitalVanishing.centerOrthogonalVanishing_restrict`), and the condition is stable
  under the dilations `β ↦ β_s` (`CenterOrthogonalVanishing.scalarDilation`).

This is the splitting `D(g) = D(z) ⊗ D(g₁)` with which Harish-Chandra reduces Theorem 3.1 to
semisimple groups: Harish-Chandra, *Admissible invariant distributions on reductive p-adic
groups* (notes by DeBacker and Sally, 1999), §3.4, Lemma 3.11, printed p. 26.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe u v

section ModuleTopology

variable {F : Type u} [Field F] [TopologicalSpace F]

/-- A subspace of a vector space with its module topology carries the module topology: the
projection along a complement is continuous for the module topology of the subspace. -/
theorem isModuleTopology_submodule {M : Type v} [AddCommGroup M] [Module F M]
    [TopologicalSpace M] [IsModuleTopology F M] (W : Submodule F M) : IsModuleTopology F W := by
  have := IsModuleTopology.isTopologicalAddGroup F M
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine IsModuleTopology.of_continuous_id ?_
  have hsurj : Function.Surjective (Submodule.projectionOnto W W' hW') := fun w =>
    ⟨w, Submodule.projectionOnto_apply_left hW' w⟩
  rw [ModuleTopology.eq_coinduced_of_surjective hsurj]
  have hid : (id : W → W) = (Submodule.projectionOnto W W' hW') ∘ Subtype.val :=
    funext fun w => (Submodule.projectionOnto_apply_left hW' w).symm
  rw [hid]
  rw [continuous_def]
  intro s hs
  exact (isOpen_coinduced.1 hs).preimage continuous_subtype_val

end ModuleTopology

section Decomposition

variable (F : Type u) [Field F] [TopologicalSpace F]
  (A : Type v) [Ring A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsModuleTopology F A]

/-- The center of `A` as a subspace. -/
abbrev centerSubmodule : Submodule F A := (Subalgebra.center F A).toSubmodule

instance isModuleTopology_centerSubmodule : IsModuleTopology F (centerSubmodule F A) :=
  isModuleTopology_submodule _

instance isModuleTopology_centerOrthogonal : IsModuleTopology F (centerOrthogonal F A) :=
  isModuleTopology_submodule _

variable [CharZero F] [FiniteDimensional F A] [IsSemisimpleRing A]

/-- The topological decomposition `z × V ≃ A`, `(Z, Y) ↦ Z + Y`, of `A` into its center and
the trace-form orthogonal of the center. -/
def centerDecomposition : (centerSubmodule F A × centerOrthogonal F A) ≃L[F] A :=
  haveI := IsModuleTopology.toContinuousAdd F A
  { toLinearEquiv := Submodule.prodEquivOfIsCompl _ _ isCompl_center_centerOrthogonal
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Submodule.prodEquivOfIsCompl _ _ isCompl_center_centerOrthogonal).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Submodule.prodEquivOfIsCompl _ _ isCompl_center_centerOrthogonal).symm.toLinearMap }

variable {F A}

@[simp]
theorem centerDecomposition_apply (p : centerSubmodule F A × centerOrthogonal F A) :
    centerDecomposition F A p = (p.1 : A) + p.2 :=
  Submodule.coe_prodEquivOfIsCompl' _ _ isCompl_center_centerOrthogonal p

theorem centerDecomposition_symm_apply_eq {X : A} (Z : centerSubmodule F A)
    (Y : centerOrthogonal F A) (h : X = (Z : A) + Y) :
    (centerDecomposition F A).symm X = (Z, Y) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, centerDecomposition_apply, h]

theorem centerDecomposition_symm_add (X : A) :
    (((centerDecomposition F A).symm X).1 : A) + ((centerDecomposition F A).symm X).2 = X := by
  rw [← centerDecomposition_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem centerDecomposition_symm_of_mem (Y : centerOrthogonal F A) :
    (centerDecomposition F A).symm (Y : A) = (0, Y) :=
  centerDecomposition_symm_apply_eq 0 Y (by simp)

/-- Conjugation by a unit, restricted to `V = z^⊥`. -/
def centerOrthogonalConj (u : Aˣ) : centerOrthogonal F A ≃ₜ centerOrthogonal F A where
  toFun Y := ⟨(u : A) * Y * ((u⁻¹ : Aˣ) : A), conj_mem_centerOrthogonal u Y.2⟩
  invFun Y := ⟨((u⁻¹ : Aˣ) : A) * Y * (((u⁻¹)⁻¹ : Aˣ) : A), conj_mem_centerOrthogonal u⁻¹ Y.2⟩
  left_inv Y := Subtype.ext (by
    simp only [inv_inv, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one])
  right_inv Y := Subtype.ext (by
    simp only [inv_inv, mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])
  continuous_toFun := Continuous.subtype_mk
    ((conjugationHomeomorph u).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((conjugationHomeomorph u⁻¹).continuous.comp continuous_subtype_val) _

omit [TopologicalSpace F] [IsModuleTopology F A] [CharZero F]
  [FiniteDimensional F A] [IsSemisimpleRing A] in
@[simp]
theorem centerOrthogonalConj_apply_coe (u : Aˣ) (Y : centerOrthogonal F A) :
    ((centerOrthogonalConj u Y : centerOrthogonal F A) : A) = (u : A) * Y * ((u⁻¹ : Aˣ) : A) :=
  rfl

/-- Conjugation fixes the central component and conjugates the `V`-component. -/
theorem centerDecomposition_symm_conj (u : Aˣ) (X : A) :
    (centerDecomposition F A).symm ((u : A) * X * ((u⁻¹ : Aˣ) : A)) =
      (((centerDecomposition F A).symm X).1,
        centerOrthogonalConj u ((centerDecomposition F A).symm X).2) := by
  apply centerDecomposition_symm_apply_eq
  conv_lhs => rw [← centerDecomposition_symm_add (F := F) X]
  have hZ := (Subalgebra.mem_center_iff (R := F)).1 ((centerDecomposition F A).symm X).1.2
  rw [centerOrthogonalConj_apply_coe, mul_add, add_mul, hZ (u : A), mul_assoc,
    Units.mul_inv, mul_one]

/-- Translation by a central element shifts the central component. -/
theorem centerDecomposition_symm_add_central (X : A) (Z : centerSubmodule F A) :
    (centerDecomposition F A).symm (X + Z) =
      (((centerDecomposition F A).symm X).1 + Z, ((centerDecomposition F A).symm X).2) := by
  apply centerDecomposition_symm_apply_eq
  conv_lhs => rw [← centerDecomposition_symm_add (F := F) X]
  rw [Submodule.coe_add]
  abel

variable [T2Space A]

/-- The restriction `f|_V` of a test function on `A` to `V = z^⊥`. -/
def restrictCenterOrthogonal :
    SchwartzBruhat A →ₗ[ℂ] SchwartzBruhat (centerOrthogonal F A) where
  toFun f := SchwartzBruhat.compLeftInverse f Subtype.val
    (fun X => ((centerDecomposition F A).symm X).2) continuous_subtype_val
    (continuous_snd.comp (centerDecomposition F A).symm.continuous)
    (fun Y => by rw [centerDecomposition_symm_of_mem])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrictCenterOrthogonal_apply (f : SchwartzBruhat A) (Y : centerOrthogonal F A) :
    restrictCenterOrthogonal f Y = f Y := rfl

/-- The test function `X ↦ α(Z) β(Y)` on `A`, for `X = Z + Y` with `Z ∈ z`, `Y ∈ z^⊥`. -/
def extendTest (α : SchwartzBruhat (centerSubmodule F A)) :
    SchwartzBruhat (centerOrthogonal F A) →ₗ[ℂ] SchwartzBruhat A where
  toFun β := Hecke.TestFunction.pullback (centerDecomposition F A).symm.toHomeomorph
    (SchwartzBruhat.tensor α β)
  map_add' β β' := by
    ext X
    exact mul_add _ _ _
  map_smul' c β := by
    ext X
    exact mul_left_comm _ _ _

omit [T2Space A] in
theorem extendTest_apply (α : SchwartzBruhat (centerSubmodule F A))
    (β : SchwartzBruhat (centerOrthogonal F A)) (X : A) :
    extendTest α β X =
      α ((centerDecomposition F A).symm X).1 * β ((centerDecomposition F A).symm X).2 := rfl

omit [T2Space A] in
theorem extendTest_apply_coe (α : SchwartzBruhat (centerSubmodule F A))
    (β : SchwartzBruhat (centerOrthogonal F A)) (Y : centerOrthogonal F A) :
    extendTest α β (Y : A) = α 0 * β Y := by
  rw [extendTest_apply, centerDecomposition_symm_of_mem]

omit [T2Space A] in
/-- Translating `extendTest α β` by a central `Z` translates `α`. -/
theorem translateTest_extendTest (α : SchwartzBruhat (centerSubmodule F A))
    (β : SchwartzBruhat (centerOrthogonal F A)) (Z : centerSubmodule F A) :
    translateTest (Z : A) (extendTest α β) = extendTest (translateTest Z α) β := by
  ext X
  rw [translateTest_apply, extendTest_apply, extendTest_apply, centerDecomposition_symm_add_central,
    translateTest_apply]

variable (F A) in
/-- The condition defining the `D₀` of `V = z^⊥`: for every test function `α` on `z` and every
regular `Y ∈ V`, all orbital integrals of `extendTest α β` at `Y` vanish. -/
def CenterOrthogonalVanishing [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    (β : SchwartzBruhat (centerOrthogonal F A)) : Prop :=
  ∀ (α : SchwartzBruhat (centerSubmodule F A)) (Y : centerOrthogonal F A),
    (Y : A) ∈ regularSet F A → OrbitalVanishingAt (Y : A) (extendTest α β)

variable [MeasurableSpace Aˣ] [BorelSpace Aˣ]

omit [T2Space A] in
/-- Every `extendTest α β` with `β` in the `D₀` of `V` lies in the `D₀` of `A`. -/
theorem CenterOrthogonalVanishing.regularOrbitalVanishing
    {β : SchwartzBruhat (centerOrthogonal F A)} (hβ : CenterOrthogonalVanishing F A β)
    (α : SchwartzBruhat (centerSubmodule F A)) :
    RegularOrbitalVanishing F A (extendTest α β) := by
  refine (regularOrbitalVanishing_iff F _).2 fun X hX => ?_
  obtain ⟨Z, Y, rfl⟩ : ∃ (Z : centerSubmodule F A) (Y : centerOrthogonal F A),
      X = (Y : A) + Z :=
    ⟨_, _, by rw [add_comm]; exact (centerDecomposition_symm_add X).symm⟩
  have hZc : ∀ W : A, W * Z = Z * W := fun W => (Subalgebra.mem_center_iff (R := F)).1 Z.2 W
  have hY : (Y : A) ∈ regularSet F A := (add_central_mem_regularSet_iff hZc _).1 hX
  rw [orbitalVanishingAt_add_central_iff hZc, translateTest_extendTest]
  exact hβ _ Y hY

/-- The restriction to `V` of a function of `D₀` lies in the `D₀` of `V`. -/
theorem RegularOrbitalVanishing.centerOrthogonalVanishing_restrict {f : SchwartzBruhat A}
    (hf : RegularOrbitalVanishing F A f) :
    CenterOrthogonalVanishing F A (restrictCenterOrthogonal f) := by
  intro α Y hY
  show OrbitalVanishingAt (Y : A) (extendTest α (restrictCenterOrthogonal f))
  have h : OrbitalVanishingAt (Y : A) (α 0 • f) :=
    OrbitalVanishingAt.smul ((regularOrbitalVanishing_iff F f).1 hf (Y : A) hY) (α 0)
  have hcongr : ∀ g : Aˣ, (α 0 • f) (((g⁻¹ : Aˣ) : A) * Y * (g : A)) =
      extendTest α (restrictCenterOrthogonal f) (((g⁻¹ : Aˣ) : A) * Y * (g : A)) := by
    intro g
    have hmem : ((g⁻¹ : Aˣ) : A) * Y * (g : A) =
        ((centerOrthogonalConj g⁻¹ Y : centerOrthogonal F A) : A) := by
      rw [centerOrthogonalConj_apply_coe, inv_inv]
    rw [hmem, extendTest_apply_coe, restrictCenterOrthogonal_apply]
    rfl
  intro _ _ μG _ μH _ _ ν hν hconv
  exact (orbitalVanishingAt_congr hcongr).1 h μG μH ν hν hconv

omit [T2Space A] in
theorem centerOrthogonalVanishing_zero : CenterOrthogonalVanishing F A 0 := by
  intro α Y _
  rw [map_zero]
  exact orbitalVanishingAt_zero _

omit [T2Space A] in
theorem CenterOrthogonalVanishing.add {β β' : SchwartzBruhat (centerOrthogonal F A)}
    (hβ : CenterOrthogonalVanishing F A β) (hβ' : CenterOrthogonalVanishing F A β') :
    CenterOrthogonalVanishing F A (β + β') := by
  intro α Y hY
  rw [map_add]
  exact OrbitalVanishingAt.add (hβ α Y hY) (hβ' α Y hY)

omit [T2Space A] in
theorem CenterOrthogonalVanishing.smul {β : SchwartzBruhat (centerOrthogonal F A)}
    (hβ : CenterOrthogonalVanishing F A β) (c : ℂ) :
    CenterOrthogonalVanishing F A (c • β) := by
  intro α Y hY
  rw [map_smul]
  exact OrbitalVanishingAt.smul (hβ α Y hY) c

/-- The `D₀` of `V`, as a complex subspace. -/
def centerOrthogonalVanishingSubmodule :
    Submodule ℂ (SchwartzBruhat (centerOrthogonal F A)) where
  carrier := {β | CenterOrthogonalVanishing F A β}
  zero_mem' := centerOrthogonalVanishing_zero
  add_mem' := CenterOrthogonalVanishing.add
  smul_mem' c _ hβ := hβ.smul c

omit [T2Space A] [MeasurableSpace Aˣ] [BorelSpace Aˣ] in
/-- Dilation commutes with `extendTest`, dilating both factors. -/
theorem scalarDilation_extendTest (s : Fˣ) (α : SchwartzBruhat (centerSubmodule F A))
    (β : SchwartzBruhat (centerOrthogonal F A)) :
    scalarDilation s (extendTest α β) = extendTest (scalarDilation s α) (scalarDilation s β) := by
  ext X
  rw [scalarDilation_apply, extendTest_apply, extendTest_apply, scalarDilation_apply,
    scalarDilation_apply, Units.smul_def, map_smul]
  rfl

omit [T2Space A] in
/-- The `D₀` of `V` is stable under the dilations `β ↦ β_s`. -/
theorem CenterOrthogonalVanishing.scalarDilation {β : SchwartzBruhat (centerOrthogonal F A)}
    (hβ : CenterOrthogonalVanishing F A β) (s : Fˣ) :
    CenterOrthogonalVanishing F A (UnitConjugation.scalarDilation s β) := by
  intro α Y hY
  have h := RegularOrbitalVanishing.scalarDilation
    (hβ.regularOrbitalVanishing (UnitConjugation.scalarDilation s⁻¹ α)) s
  rw [scalarDilation_extendTest] at h
  have hα : UnitConjugation.scalarDilation s (UnitConjugation.scalarDilation s⁻¹ α) = α := by
    ext Z
    rw [scalarDilation_apply, scalarDilation_apply, inv_inv, smul_smul, mul_inv_cancel, one_smul]
  rw [hα] at h
  intro _ _ μG _ μH _ _ ν hν hconv
  exact (regularOrbitalVanishing_iff F _).1 h (Y : A) hY μG μH ν hν hconv

end Decomposition

end Langlands.HarmonicAnalysis.UnitConjugation
