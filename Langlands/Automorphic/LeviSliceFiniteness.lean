import Langlands.Automorphic.CuspidalAdmissible.FixedMultiplicity
import Langlands.Automorphic.FiniteLevelConstantTermRestriction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Finite-dimensional separate slices and the constant-term reduction -/

noncomputable section
universe u v w
set_option autoImplicit false

namespace Langlands.Automorphic

section Product

variable {D : Type u} [AddCommGroup D] [Module ℂ D] {X : Type v} {Y : Type w}

/-- Hold the second variable fixed in a linear family of functions on a product. -/
def firstFunctionSlice (y : Y) :
    (D →ₗ[ℂ] (X × Y → ℂ)) →ₗ[ℂ] (D →ₗ[ℂ] (X → ℂ)) :=
  LinearMap.llcomp ℂ D _ _ (LinearMap.funLeft ℂ ℂ fun x => (x, y))

/-- Hold the first variable fixed in a linear family of functions on a product. -/
def secondFunctionSlice (x : X) :
    (D →ₗ[ℂ] (X × Y → ℂ)) →ₗ[ℂ] (D →ₗ[ℂ] (Y → ℂ)) :=
  LinearMap.llcomp ℂ D _ _ (LinearMap.funLeft ℂ ℂ fun y => (x, y))

@[simp]
theorem firstFunctionSlice_apply (y : Y) (f : D →ₗ[ℂ] (X × Y → ℂ)) (v : D) (x : X) :
    firstFunctionSlice y f v x = f v (x, y) := rfl

@[simp]
theorem secondFunctionSlice_apply (x : X) (f : D →ₗ[ℂ] (X × Y → ℂ)) (v : D) (y : Y) :
    secondFunctionSlice x f v y = f v (x, y) := rfl

/-- Functions with slices in the respective prescribed subspaces in both variables. -/
def separateSliceSubmodule (A : Submodule ℂ (D →ₗ[ℂ] (X → ℂ)))
    (B : Submodule ℂ (D →ₗ[ℂ] (Y → ℂ))) : Submodule ℂ (D →ₗ[ℂ] (X × Y → ℂ)) :=
  (⨅ y : Y, A.comap (firstFunctionSlice y)) ⊓ (⨅ x : X, B.comap (secondFunctionSlice x))

theorem mem_separateSliceSubmodule (A : Submodule ℂ (D →ₗ[ℂ] (X → ℂ)))
    (B : Submodule ℂ (D →ₗ[ℂ] (Y → ℂ))) (f : D →ₗ[ℂ] (X × Y → ℂ)) :
    f ∈ separateSliceSubmodule A B ↔
      (∀ y, firstFunctionSlice y f ∈ A) ∧ (∀ x, secondFunctionSlice x f ∈ B) := by
  simp only [separateSliceSubmodule, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

/-- Two fixed finite-dimensional spaces of separate slices bound the whole product space. -/
theorem finite_separateSliceSubmodule (A : Submodule ℂ (D →ₗ[ℂ] (X → ℂ)))
    (B : Submodule ℂ (D →ₗ[ℂ] (Y → ℂ))) [Module.Finite ℂ A] [Module.Finite ℂ B] :
    Module.Finite ℂ (separateSliceSubmodule A B) := by
  classical
  let ev (p : D × X) : Module.Dual ℂ A :=
    (LinearMap.proj p.2).comp ((LinearMap.applyₗ p.1).comp A.subtype)
  let E := Submodule.span ℂ (Set.range ev)
  let : Module.Free ℂ A := Module.Free.of_divisionRing ℂ A
  let e : (Fin (Module.finrank ℂ A) → ℂ) ≃ₗ[ℂ] Module.Dual ℂ A :=
    (Module.finBasis ℂ A).constr ℂ
  have hdual : Module.Finite ℂ (Module.Dual ℂ A) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have : IsNoetherian ℂ (Module.Dual ℂ A) :=
    @isNoetherian_of_isNoetherianRing_of_finite ℂ (Module.Dual ℂ A) _ _ _ _ hdual
  have hEfinite : Module.Finite ℂ E := Module.Finite.of_injective E.subtype Subtype.val_injective
  have hfg : E.FG := Module.Finite.iff_fg.mp hEfinite
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range ev)).mp hfg
  choose p hp using fun ℓ : t => ht ℓ.property
  let C := separateSliceSubmodule A B
  let T : C →ₗ[ℂ] (t → B) := LinearMap.pi fun ℓ =>
    ((secondFunctionSlice (p ℓ).2).comp C.subtype).codRestrict B
      (fun f => ((mem_separateSliceSubmodule A B f.val).mp f.property).2 (p ℓ).2)
  have hF : Module.Finite ℂ (t → B) := inferInstance
  have : IsNoetherian ℂ (t → B) :=
    @isNoetherian_of_isNoetherianRing_of_finite ℂ (t → B) _ _ _ _ hF
  refine Module.Finite.of_injective T (fun f g hfg => ?_)
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  funext z
  let a : A := ⟨firstFunctionSlice z.2 f.val - firstFunctionSlice z.2 g.val, A.sub_mem
    (((mem_separateSliceSubmodule A B f.val).mp f.property).1 z.2)
    (((mem_separateSliceSubmodule A B g.val).mp g.property).1 z.2)⟩
  have hE : E ≤ LinearMap.ker (LinearMap.applyₗ a) := by
    change Submodule.span ℂ (Set.range ev) ≤ _
    rw [hspan]
    apply Submodule.span_le.mpr
    intro ℓ hℓ
    let i : t := ⟨ℓ, hℓ⟩
    have hi := congrArg (fun k : B => k.val (p i).1 z.2) (congrFun hfg i)
    apply LinearMap.mem_ker.mpr
    change i.val a = 0
    rw [← hp i]
    exact sub_eq_zero.mpr hi
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp
    (hE (Submodule.subset_span ⟨(v, z.1), rfl⟩)))

end Product

private theorem finiteDomain_of_finite_kernel_range {V W : Type*}
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    (R : V →ₗ[ℂ] W) (hker : Module.Finite ℂ R.ker) (hrange : Module.Finite ℂ R.range) :
    Module.Finite ℂ V := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  have : FiniteDimensional ℂ R.ker := hker
  have : FiniteDimensional ℂ R.range := hrange
  have he : R.range.comap R = (⊤ : Submodule ℂ V) :=
    top_unique (fun x _ => LinearMap.mem_range_self R x)
  have hf : FiniteDimensional ℂ (R.range.comap R) := inferInstance
  have : Module.Finite ℂ (⊤ : Submodule ℂ V) := he ▸ hf
  exact Module.Finite.of_surjective Submodule.topEquiv.toLinearMap Submodule.topEquiv.surjective

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ) [CompactSpace (AdeleQuotient F)]

local instance leviSliceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance leviSliceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance leviSliceFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance leviSliceFormGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

omit [CompactSpace (AdeleQuotient F)] in
/-- Read the actual scalar values of an automorphic form on the adelic group. -/
def automorphicFormValues : AutomorphicForms F n →ₗ[ℂ] (AdelicGL F n → ℂ) :=
  (ContinuousMap.coeFnLinearMap ℂ).comp
    ((ContinuousRationalFunctions.toContinuousMap F n).comp (automorphicToContinuous F n))

omit [CompactSpace (AdeleQuotient F)] in
@[simp]
theorem automorphicFormValues_apply (f : AutomorphicForms F n) (g : AdelicGL F n) :
    automorphicFormValues F n f g = evaluate F n (automorphicToContinuous F n f) g := rfl

variable (J : Ideal (EnvelopingCenter F n)) (L : OpenSubgroup (FiniteAdelicGL F n))
variable {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))

set_option maxHeartbeats 800000 in
/-- The cuspidal kernel and finite-dimensional bounds for the two sets of Levi slices
give finite dimension of the original multiplicity space. -/
theorem finiteDimensional_annihilatedFormMultiplicitySpace_of_slices
    (hJ : Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ))
    (hs : ∀ (p : MaximalBlockCut n) (d : FiniteAdelicGL F n),
      ∃ (A : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] (AdelicGL F p.val.1 → ℂ)))
        (B : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] (AdelicGL F p.val.2 → ℂ))),
        Module.Finite ℂ A ∧ Module.Finite ℂ B ∧
          ∀ φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ,
            (blockConstantTermAt F n p.property.1 d).comp φ.val ∈ separateSliceSubmodule A B) :
    FiniteDimensional ℂ (annihilatedFormMultiplicitySpace F n J L.toSubgroup σ) := by
  classical
  obtain ⟨t, ht⟩ := exists_constantTerm_finite_cover F n L
  let M := annihilatedFormMultiplicitySpace F n J L.toSubgroup σ
  let R := restrictMultiplicityToConstantTerms F n σ J L t
  choose A B hA hB hab using fun (p : MaximalBlockCut n) (d : t) => hs p d.val
  let E (p : MaximalBlockCut n) (d : t) := separateSliceSubmodule (A p d) (B p d)
  have hE (p : MaximalBlockCut n) (d : t) : Module.Finite ℂ (E p d) := by
    have := hA p d
    have := hB p d
    exact finite_separateSliceSubmodule (A p d) (B p d)
  let C := ∀ (p : MaximalBlockCut n) (d : t), E p d
  let i : C →ₗ[ℂ] (∀ (p : MaximalBlockCut n) (_ : t),
      (Fin m → ℂ) →ₗ[ℂ] (AdelicGL F p.val.1 × AdelicGL F p.val.2 → ℂ)) :=
    { toFun := fun f p d => (f p d).val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : R.range ≤ i.range := by
    rintro _ ⟨φ, rfl⟩
    exact ⟨fun p d => ⟨R φ p d, hab p d φ⟩, rfl⟩
  have : Module.Finite ℂ C := inferInstance
  have : Module.Finite ℂ i.range := Module.Finite.range i
  have hrange : Module.Finite ℂ R.range := Submodule.finiteDimensional_of_le hi
  let K := cuspidalAnnihilatedFormMultiplicitySpace F n J L.toSubgroup σ
  have hK : Module.Finite ℂ K :=
    finiteDimensional_cuspidalAnnihilatedFormMultiplicitySpace F n J σ L hJ
  have : IsNoetherian ℂ K := @isNoetherian_of_isNoetherianRing_of_finite ℂ K _ _ _ _ hK
  let j : R.ker →ₗ[ℂ] K := (M.subtype.comp R.ker.subtype).codRestrict K fun φ =>
    (mem_cuspidalAnnihilatedFormMultiplicitySpace F n J L.toSubgroup σ φ.val.val).mpr
      ⟨φ.val.property,
        (mem_ker_restrictMultiplicityToConstantTerms_iff F n σ J L t ht φ.val).mp φ.property⟩
  have hker : Module.Finite ℂ R.ker := Module.Finite.of_injective j
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x : K => x.val) h)))
  exact finiteDomain_of_finite_kernel_range R hker hrange

end Langlands.Automorphic
