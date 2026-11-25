import Langlands.Automorphic.AutomorphicAdmissibilityStatement
import Langlands.Automorphic.FiniteLevelArchimedeanSlices

/-! # Restriction of Harish-Chandra's adelic finiteness problem to archimedean quotients -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ArchimedeanGL.SmoothFunctions F n) :=
  (ArchimedeanGL.smoothFunctions F n).addCommGroup

/-- The archimedean image of the rational stabilizer of the finite-level slice at `b`. -/
def archimedeanSliceStabilizer (L : OpenSubgroup (FiniteAdelicGL F n))
    (b : FiniteAdelicGL F n) : Subgroup (InfiniteAdelicGL F n) :=
  (finiteLevelSliceStabilizer F n L b).map
    ((AdelicGL.infinite F n).toMonoidHom.comp (AdelicGL.rational F n))

/-- Smooth left `Γ`-invariant functions of polynomial growth killed by the center ideal `J`. -/
def archimedeanAnnihilatedForms (Γ : Subgroup (InfiniteAdelicGL F n))
    (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)) :
    Submodule ℂ (ArchimedeanGL.SmoothFunctions F n) where
  carrier := { f | (∀ γ ∈ Γ, ∀ x, f.val (γ * x) = f.val x) ∧
    ArchimedeanGL.HasPolynomialGrowth F n f.val ∧
    ∀ z ∈ J, ArchimedeanGL.centerAction F n z f = 0 }
  zero_mem' := ⟨fun _ _ _ => rfl, ArchimedeanGL.HasPolynomialGrowth.zero,
    fun z _ => map_zero (ArchimedeanGL.centerAction F n z)⟩
  add_mem' := by
    rintro f g ⟨hf, hfg, hfz⟩ ⟨hg, hgg, hgz⟩
    refine ⟨fun γ hγ x => ?_, hfg.add hgg, fun z hz => ?_⟩
    · change f.val (γ * x) + g.val (γ * x) = f.val x + g.val x
      rw [hf γ hγ x, hg γ hγ x]
    · rw [map_add, hfz z hz, hgz z hz, add_zero]
  smul_mem' := by
    rintro a f ⟨hf, hfg, hfz⟩
    refine ⟨fun γ hγ x => ?_, hfg.smul a, fun z hz => ?_⟩
    · change a • f.val (γ * x) = a • f.val x
      rw [hf γ hγ x]
    · rw [map_smul, hfz z hz, smul_zero]

/-- The compact-equivariant maps into the archimedean center-annihilated space. -/
def archimedeanAnnihilatedMultiplicitySpace (Γ : Subgroup (InfiniteAdelicGL F n))
    (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)) {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n) where
  carrier := { φ | (∀ v, φ v ∈ archimedeanAnnihilatedForms F n Γ J) ∧
    ∀ k v, φ (σ k v) = ArchimedeanGL.smoothRightAction F n k.val (φ v) }
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun k v => by simp⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, hφk⟩ ⟨hψ, hψk⟩
    exact ⟨fun v => Submodule.add_mem _ (hφ v) (hψ v), fun k v => by
      simp only [LinearMap.add_apply, map_add, hφk, hψk]⟩
  smul_mem' := by
    rintro a φ ⟨hφ, hφk⟩
    exact ⟨fun v => Submodule.smul_mem _ a (hφ v), fun k v => by
      simp only [LinearMap.smul_apply, map_smul, hφk]⟩

local instance (Γ : Subgroup (InfiniteAdelicGL F n))
    (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)) {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    AddCommGroup (archimedeanAnnihilatedMultiplicitySpace F n Γ J σ) :=
  (archimedeanAnnihilatedMultiplicitySpace F n Γ J σ).addCommGroup

local instance (Γ : Subgroup (InfiniteAdelicGL F n))
    (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)) {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    Module ℂ (archimedeanAnnihilatedMultiplicitySpace F n Γ J σ) :=
  (archimedeanAnnihilatedMultiplicitySpace F n Γ J σ).module

local instance (J : Ideal (ArchimedeanGL.EnvelopingCenter F n))
    (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    AddCommGroup (annihilatedFormMultiplicitySpace F n J L σ) :=
  (annihilatedFormMultiplicitySpace F n J L σ).addCommGroup

local instance (J : Ideal (ArchimedeanGL.EnvelopingCenter F n))
    (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    Module ℂ (annihilatedFormMultiplicitySpace F n J L σ) :=
  (annihilatedFormMultiplicitySpace F n J L σ).module

/-- The archimedean finiteness input for all stabilizers of compact open finite-level slices. -/
def ArchimedeanHarishChandraFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)),
    Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter F n ⧸ J.restrictScalars ℂ) →
    ∀ (L : OpenSubgroup (FiniteAdelicGL F n)), IsCompact (L : Set (FiniteAdelicGL F n)) →
    ∀ (b : FiniteAdelicGL F n) (m : ℕ)
      (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)),
      FiniteDimensional ℂ (archimedeanAnnihilatedMultiplicitySpace F n
        (archimedeanSliceStabilizer F n L b) J σ)

private def formSlice (b : FiniteAdelicGL F n) :
    AutomorphicForms F n →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n :=
  (finiteSmoothSlice F n b).comp (automorphicSubrepresentation F n).toSubmodule.subtype

private theorem level_of_fixed (L : OpenSubgroup (FiniteAdelicGL F n))
    (f : AutomorphicForms F n) (hL : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    f.val.val ∈ levelSubmodule F n L.toSubgroup :=
  fun l => congrArg (fun g : AutomorphicForms F n => g.val.val) (hL l)

/-- A slice at `b` satisfies the specified archimedean conditions for its rational stabilizer. -/
theorem formSlice_mem_archimedeanAnnihilatedForms (L : OpenSubgroup (FiniteAdelicGL F n))
    (b : FiniteAdelicGL F n) (J : Ideal (ArchimedeanGL.EnvelopingCenter F n))
    (f : AutomorphicForms F n) (hL : ∀ l : L, automorphicFiniteRightAction F n l.val f = f)
    (hJ : f ∈ centerAnnihilatedForms F n J) :
    finiteSmoothSlice F n b f.val ∈
      archimedeanAnnihilatedForms F n (archimedeanSliceStabilizer F n L b) J := by
  let A := slicesAtLevel F n L f.val (level_of_fixed F n L f hL)
  refine ⟨?_, ((mem_automorphicSubrepresentation F n f.val).mp f.property).2.2.2 b, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩ x
    let l : L := ⟨b⁻¹ * finiteRationalGL F n γ * b,
      (mem_finiteLevelSliceStabilizer_iff F n L b γ).mp hγ⟩
    have heq : finiteRationalGL F n γ * b = b * l.val := by
      change finiteRationalGL F n γ * b = b * (b⁻¹ * finiteRationalGL F n γ * b)
      rw [← mul_assoc, mul_inv_cancel_left]
    have hslice : A.val (finiteRationalGL F n γ * b) = A.val b := by
      rw [heq, A.property.1 b l]
    have hc := A.property.2 γ b x
    change (A.val (finiteRationalGL F n γ * b)).val
      (AdelicGL.infinite F n (AdelicGL.rational F n γ) * x) = (A.val b).val x at hc
    rw [hslice] at hc
    exact hc
  · intro z hz
    have he := ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hJ z) hz :
      f ∈ LinearMap.ker (automorphicEnvelopingAction F n
        (z : ArchimedeanGL.EnvelopingAlgebra F n)))
    change ArchimedeanGL.envelopingAction F n (z : ArchimedeanGL.EnvelopingAlgebra F n)
      (finiteSmoothSlice F n b f.val) = 0
    rw [← finiteSmoothSlice_envelopingAction, ← automorphicEnvelopingAction_val,
      LinearMap.mem_ker.mp he]
    exact map_zero (formSlice F n b)

private theorem formSlice_compact (b : FiniteAdelicGL F n)
    (k : standardInfiniteCompact F n) (f : AutomorphicForms F n) :
    formSlice F n b (automorphicCompactRightAction F n k f) =
      ArchimedeanGL.smoothRightAction F n k.val (formSlice F n b f) := by
  apply Subtype.ext
  funext x
  change ContinuousRationalFunctions.evaluate F n
      (automorphicToContinuous F n (automorphicCompactRightAction F n k f))
      (AdelicGL.pair F n x b) =
    ContinuousRationalFunctions.evaluate F n (automorphicToContinuous F n f)
      (AdelicGL.pair F n (x * k.val) b)
  rw [evaluate_automorphicCompactRightAction, AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]

variable {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))
  (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)) (L : OpenSubgroup (FiniteAdelicGL F n))

private theorem multiplicity_fixed_equivariant
    (φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ) :
    (∀ v (l : L), automorphicFiniteRightAction F n l.val (φ.val v) = φ.val v) ∧
      ∀ k v, φ.val (σ k v) = automorphicCompactRightAction F n k (φ.val v) :=
  φ.property.1

/-- The restrictions of each adelic multiplicity map to the chosen archimedean slices. -/
def restrictMultiplicityToSlices :
    annihilatedFormMultiplicitySpace F n J L.toSubgroup σ →ₗ[ℂ]
      (∀ c : FiniteLevelDoubleCosets F n L, archimedeanAnnihilatedMultiplicitySpace F n
        (archimedeanSliceStabilizer F n L c.out) J σ) :=
  LinearMap.pi fun c => LinearMap.codRestrict _
    ((LinearMap.llcomp ℂ (Fin m → ℂ) _ _ (formSlice F n c.out)).comp
      (annihilatedFormMultiplicitySpace F n J L.toSubgroup σ).subtype) (by
        intro φ
        have hφ := multiplicity_fixed_equivariant F n σ J L φ
        refine ⟨fun v => formSlice_mem_archimedeanAnnihilatedForms F n L c.out J (φ.val v)
          (hφ.1 v) ((Submodule.mem_iInf _).mp φ.property.2 v), ?_⟩
        intro k v
        change formSlice F n c.out (φ.val (σ k v)) =
          ArchimedeanGL.smoothRightAction F n k.val (formSlice F n c.out (φ.val v))
        rw [hφ.2 k v, formSlice_compact])

/-- The finite product of restrictions is faithful. -/
theorem restrictMultiplicityToSlices_injective :
    Function.Injective (restrictMultiplicityToSlices F n σ J L) := by
  intro φ ψ h
  have hφ := multiplicity_fixed_equivariant F n σ J L φ
  have hψ := multiplicity_fixed_equivariant F n σ J L ψ
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  let A := slicesAtLevel F n L (φ.val v).val (level_of_fixed F n L _ (hφ.1 v))
  let B := slicesAtLevel F n L (ψ.val v).val (level_of_fixed F n L _ (hψ.1 v))
  have hAB : A = B :=
    finiteLevelSmoothSliceFamilies_restrict_injective F n L (funext fun c =>
      congrArg (fun r => (r c).val v) h)
  exact finiteSmoothSlice_injective F n (congrArg Subtype.val hAB)

/-- Shrinking the finite level gives an inclusion of the corresponding multiplicity spaces. -/
theorem annihilatedFormMultiplicitySpace_le_of_level_le
    {L₀ : OpenSubgroup (FiniteAdelicGL F n)} (hL : L₀ ≤ L) :
    annihilatedFormMultiplicitySpace F n J L.toSubgroup σ ≤
      annihilatedFormMultiplicitySpace F n J L₀.toSubgroup σ := by
  intro φ hφ
  have h := multiplicity_fixed_equivariant F n σ J L ⟨φ, hφ⟩
  exact ⟨⟨fun v l => h.1 v ⟨l.val, hL l.property⟩, h.2⟩, hφ.2⟩

/-- The archimedean finiteness input implies the exact adelic finiteness statement. -/
theorem harishChandraFiniteness_of_archimedean
    (h : ArchimedeanHarishChandraFinitenessStatement.{u}) :
    HarishChandraFinitenessStatement.{u} := by
  intro F _ _ n J hJ L m σ
  obtain ⟨L₀, hL₀, hcomp⟩ := OperatorRealization.exists_compact_openSubgroup_le L
  have : Finite (FiniteLevelDoubleCosets F n L₀) := finite_finiteLevelDoubleCosets F n L₀
  have (c : FiniteLevelDoubleCosets F n L₀) :
      FiniteDimensional ℂ (archimedeanAnnihilatedMultiplicitySpace F n
        (archimedeanSliceStabilizer F n L₀ c.out) J σ) :=
    h F n J hJ L₀ hcomp c.out m σ
  have hinc := annihilatedFormMultiplicitySpace_le_of_level_le F n σ J L hL₀
  exact FiniteDimensional.of_injective
    ((restrictMultiplicityToSlices F n σ J L₀).comp (Submodule.inclusion hinc))
    ((restrictMultiplicityToSlices_injective F n σ J L₀).comp
      (Submodule.inclusion_injective hinc))

end Langlands.Automorphic
