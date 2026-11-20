import Langlands.Automorphic.TwoBlockConstantTermRadical
import Langlands.Automorphic.TwoBlockSliceGrowth

/-! # Lower-rank automorphic lifts of constant-term slices -/

noncomputable section
universe u

open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ArchimedeanGL ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F]

local instance blockSliceLiftRationalGroup (r : ℕ) :
    AddCommGroup (RationalInvariantFunctions F r) := Submodule.addCommGroup _
local instance blockSliceLiftContinuousGroup (r : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F r) := Submodule.addCommGroup _
local instance blockSliceLiftFiniteSmoothGroup (r : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F r) := Submodule.addCommGroup _
local instance blockSliceLiftFormGroup (r : ℕ) :
    AddCommGroup (AutomorphicForms F r) := Submodule.addCommGroup _

local notation "A" => AdelicGL F
local notation "G∞" => InfiniteAdelicGL F
local notation "Gf" => FiniteAdelicGL F
local notation "Z" => EnvelopingCenter F
local notation "U" => EnvelopingAlgebra F

private theorem centralIdealRightSpan_annihilates {n : ℕ} (J : Ideal (Z n))
    (f : AutomorphicForms F n) (hf : f ∈ centerAnnihilatedForms F n J)
    (u : U n) (hu : u ∈ centralIdealRightSpan F n J) :
    finiteSmoothEnvelopingAction F n u f.val = 0 := by
  let T := (LinearMap.applyₗ (R := ℂ) f.val).comp (finiteSmoothEnvelopingAction F n).toLinearMap
  have hT : centralIdealRightSpan F n J ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨z, v⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hz := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hf z.val) z.property
    have he := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    change finiteSmoothEnvelopingAction F n (centerInclusion F n z.val) f.val = 0 at he
    change finiteSmoothEnvelopingAction F n (centerInclusion F n z.val * v) f.val = 0
    rw [← centerInclusion_commute F n z.val v, map_mul, Module.End.mul_apply, he, map_zero]
  exact LinearMap.mem_ker.mp (hT hu)

variable [CompactSpace (AdeleQuotient F)] {a b n : ℕ} (h : a + b = n)

private theorem constantTerm_enveloping_eq_zero (J : Ideal (Z n))
    (f : AutomorphicForms F n) (hf : f ∈ centerAnnihilatedForms F n J)
    (u : U n) (hu : u ∈ centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F h)
    (d : Gf n) (p : G∞ a × G∞ b) :
    constantTerm F n h (finiteSmoothEnvelopingAction F n u f.val).val
      (AdelicGL.pair F n (blockDiagonalEmbedding h p) d) = 0 := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add, LinearMap.add_apply, centralIdealRightSpan_annihilates F J f hf v hv, zero_add]
  exact constantTerm_upperBlockEnvelopingSpan F h f.val d p w hw

private theorem firstBlockConstantTerm_annihilated (J : Ideal (Z n)) (I : Ideal (Z a))
    (hI : ∀ z ∈ I, firstBlockEnvelopingInclusion F h (z : U a) ∈
      centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F h)
    (d : Gf n) (y : A b) (f : AutomorphicForms F n) (hJ : f ∈ centerAnnihilatedForms F n J)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f)
    (z : Z a) (hz : z ∈ I) :
    finiteSmoothEnvelopingAction F a (z : U a)
      (firstBlockConstantTermFiniteSmooth F h d y f L hf) = 0 := by
  apply finiteSmoothSlice_injective F a
  funext l
  change finiteSmoothSlice F a l _ = finiteSmoothSlice F a l 0
  rw [map_zero, finiteSmoothSlice_envelopingAction, firstBlockConstantTermFiniteSmooth_slice,
    firstBlockSmoothConstantTerm_enveloping]
  apply Subtype.ext
  funext x
  rw [firstBlockSmoothConstantTerm_apply]
  exact constantTerm_enveloping_eq_zero F h J f hJ _ (hI z hz) _ _

private theorem secondBlockConstantTerm_annihilated (J : Ideal (Z n)) (I : Ideal (Z b))
    (hI : ∀ z ∈ I, secondBlockEnvelopingInclusion F h (z : U b) ∈
      centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F h)
    (d : Gf n) (x : A a) (f : AutomorphicForms F n) (hJ : f ∈ centerAnnihilatedForms F n J)
    (L : OpenSubgroup (Gf n)) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f)
    (z : Z b) (hz : z ∈ I) :
    finiteSmoothEnvelopingAction F b (z : U b)
      (secondBlockConstantTermFiniteSmooth F h d x f L hf) = 0 := by
  apply finiteSmoothSlice_injective F b
  funext l
  change finiteSmoothSlice F b l _ = finiteSmoothSlice F b l 0
  rw [map_zero, finiteSmoothSlice_envelopingAction, secondBlockConstantTermFiniteSmooth_slice,
    secondBlockSmoothConstantTerm_enveloping]
  apply Subtype.ext
  funext y
  rw [secondBlockSmoothConstantTerm_apply]
  exact constantTerm_enveloping_eq_zero F h J f hJ _ (hI z hz) _ _

omit [CompactSpace (AdeleQuotient F)] in
private def automorphicMultiplicityLift {r m : ℕ}
    (I : Ideal (Z r)) (hI : Module.Finite ℂ (Z r ⧸ I.restrictScalars ℂ))
    (L : OpenSubgroup (Gf r)) (σ : Representation ℂ (standardInfiniteCompact F r) (Fin m → ℂ))
    (T : (Fin m → ℂ) →ₗ[ℂ] ContinuousRationalFunctions F r)
    (S : (Fin m → ℂ) → FiniteSmoothRationalFunctions F r)
    (hS : ∀ v, (S v).val = T v)
    (hfixed : ∀ v, T v ∈ levelSubmodule F r L.toSubgroup)
    (hcompact : ∀ k v, T (σ k v) =
      continuousRightAction F r (AdelicGL.ofInfinite F r k.val) (T v))
    (hcenter : ∀ (v : Fin m → ℂ) (z : Z r), z ∈ I →
      finiteSmoothEnvelopingAction F r (z : U r) (S v) = 0)
    (hgrowth : ∀ v, HasPolynomialGrowth F r (T v)) :
    {ψ : annihilatedFormMultiplicitySpace F r I L.toSubgroup σ //
      ∀ v, automorphicToContinuous F r (ψ.val v) = T v} := by
  have hform (v : Fin m → ℂ) : S v ∈ automorphicSubrepresentation F r := by
    apply (mem_automorphicSubrepresentation F r (S v)).mpr
    refine ⟨(hasFiniteLevel_iff_mem_finiteSmooth F r _).mpr (S v).property.2, ?_, ?_, ?_⟩
    · change IsInfiniteFinite F r (standardInfiniteCompact F r) (S v).val
      rw [hS]
      have hle : infiniteOrbitSpan F r (standardInfiniteCompact F r) (T v) ≤ T.range := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact ⟨σ k v, hcompact k v⟩
      have : Module.Finite ℂ T.range := Module.Finite.range T
      exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    · apply (isCenterFinite_iff_exists_ideal F r _).mpr
      refine ⟨I, hI, fun z hz l => ?_⟩
      change envelopingAction F r (z : U r) (finiteSmoothSlice F r l (S v)) = 0
      rw [← finiteSmoothSlice_envelopingAction, hcenter v z hz, map_zero]
    · exact hS v ▸ hgrowth v
  let form (v : Fin m → ℂ) : AutomorphicForms F r := ⟨S v, hform v⟩
  have hvalue (v : Fin m → ℂ) : automorphicToContinuous F r (form v) = T v := hS v
  let ψ : (Fin m → ℂ) →ₗ[ℂ] AutomorphicForms F r :=
    { toFun := form
      map_add' v w := (automorphicToContinuous_injective F r) (by rw [map_add, hvalue, hvalue, hvalue, map_add])
      map_smul' c v := (automorphicToContinuous_injective F r) (by
        rw [map_smul, RingHom.id_apply, hvalue, hvalue, map_smul]) }
  refine ⟨⟨ψ, ⟨?_, ?_⟩⟩, hvalue⟩
  · apply (Langlands.mem_jointMultiplicitySpace _ _ L.toSubgroup σ ψ).mpr
    refine ⟨?_, ?_⟩
    · intro v l
      apply automorphicToContinuous_injective F r
      change automorphicToContinuous F r (automorphicFiniteRightAction F r l.val (form v)) =
        automorphicToContinuous F r (form v)
      rw [automorphicToContinuous_finiteRightAction, hvalue]
      exact hfixed v l
    · intro k v
      apply automorphicToContinuous_injective F r
      change automorphicToContinuous F r (form (σ k v)) =
        automorphicToContinuous F r (automorphicCompactRightAction F r k (form v))
      rw [automorphicToContinuous_compactRightAction, hvalue, hvalue]
      exact hcompact k v
  · refine (Submodule.mem_iInf _).mpr fun v => ?_
    refine (Submodule.mem_iInf _).mpr fun z => (Submodule.mem_iInf _).mpr fun hz => ?_
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact hcenter v z hz

omit [CompactSpace (AdeleQuotient F)] in
private theorem source_hasLevel {m : ℕ} {J : Ideal (Z n)} {L : OpenSubgroup (Gf n)}
    {σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)}
    (φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ) (v : Fin m → ℂ) :
    ∀ l : L, automorphicFiniteRightAction F n l.val (φ.val v) = φ.val v :=
  ((Langlands.mem_jointMultiplicitySpace _ _ L.toSubgroup σ φ.val).mp φ.property.1).1 v

omit [CompactSpace (AdeleQuotient F)] in
private theorem source_hasCompactEquivariance {m : ℕ} {J : Ideal (Z n)} {L : OpenSubgroup (Gf n)}
    {σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)}
    (φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ)
    (k : standardInfiniteCompact F n) (v : Fin m → ℂ) :
    φ.val (σ k v) = automorphicCompactRightAction F n k (φ.val v) :=
  ((Langlands.mem_jointMultiplicitySpace _ _ L.toSubgroup σ φ.val).mp φ.property.1).2 k v

/-- Lift the whole first-variable slice of a fixed-level compact intertwiner into the
lower-rank multiplicity space supplied by a cofinite transferred center ideal. -/
def firstBlockConstantTermMultiplicityLift {m : ℕ}
    (J : Ideal (Z n)) (L : OpenSubgroup (Gf n))
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))
    (I : Ideal (Z a)) (hI : Module.Finite ℂ (Z a ⧸ I.restrictScalars ℂ))
    (htransfer : ∀ z ∈ I, firstBlockEnvelopingInclusion F h (z : U a) ∈
      centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F h)
    (d : Gf n) (φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ) (y : A b) :
    {ψ : annihilatedFormMultiplicitySpace F a I (firstBlockConstantTermLevel F h L d).toSubgroup
      (σ.comp (firstBlockInfiniteCompact F h)) //
      ∀ v x, evaluate F a (automorphicToContinuous F a (ψ.val v)) x =
        blockConstantTermAt F n h d (φ.val v) (x, y)} := by
  let T := (firstBlockConstantTermContinuous F h d y).comp φ.val
  let S (v : Fin m → ℂ) := firstBlockConstantTermFiniteSmooth F h d y (φ.val v) L
    (source_hasLevel F φ v)
  let ψ := automorphicMultiplicityLift F I hI (firstBlockConstantTermLevel F h L d)
    (σ.comp (firstBlockInfiniteCompact F h)) T S (fun _ => rfl)
    (fun v => firstBlockConstantTermContinuous_fixed F h d y (φ.val v) L (source_hasLevel F φ v))
    (fun k v => by
      change firstBlockConstantTermContinuous F h d y
          (φ.val (σ (firstBlockInfiniteCompact F h k) v)) =
        continuousRightAction F a (AdelicGL.ofInfinite F a k.val)
          (firstBlockConstantTermContinuous F h d y (φ.val v))
      rw [source_hasCompactEquivariance F φ, firstBlockConstantTermContinuous_compact])
    (fun v z hz => firstBlockConstantTerm_annihilated F h J I htransfer d y (φ.val v)
      ((Submodule.mem_iInf _).mp φ.property.2 v) L (source_hasLevel F φ v) z hz)
    (fun v => firstBlockConstantTerm_hasPolynomialGrowth F h d y (φ.val v) L (source_hasLevel F φ v))
  exact ⟨ψ.val, fun v x => congrArg (fun f => evaluate F a f x) (ψ.property v)⟩

/-- Lift the whole second-variable slice into the lower-rank multiplicity space supplied
by a cofinite transferred center ideal. -/
def secondBlockConstantTermMultiplicityLift {m : ℕ}
    (J : Ideal (Z n)) (L : OpenSubgroup (Gf n))
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))
    (I : Ideal (Z b)) (hI : Module.Finite ℂ (Z b ⧸ I.restrictScalars ℂ))
    (htransfer : ∀ z ∈ I, secondBlockEnvelopingInclusion F h (z : U b) ∈
      centralIdealRightSpan F n J ⊔ upperBlockEnvelopingSpan F h)
    (d : Gf n) (φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ) (x : A a) :
    {ψ : annihilatedFormMultiplicitySpace F b I (secondBlockConstantTermLevel F h L d).toSubgroup
      (σ.comp (secondBlockInfiniteCompact F h)) //
      ∀ v y, evaluate F b (automorphicToContinuous F b (ψ.val v)) y =
        blockConstantTermAt F n h d (φ.val v) (x, y)} := by
  let T := (secondBlockConstantTermContinuous F h d x).comp φ.val
  let S (v : Fin m → ℂ) := secondBlockConstantTermFiniteSmooth F h d x (φ.val v) L
    (source_hasLevel F φ v)
  let ψ := automorphicMultiplicityLift F I hI (secondBlockConstantTermLevel F h L d)
    (σ.comp (secondBlockInfiniteCompact F h)) T S (fun _ => rfl)
    (fun v => secondBlockConstantTermContinuous_fixed F h d x (φ.val v) L (source_hasLevel F φ v))
    (fun k v => by
      change secondBlockConstantTermContinuous F h d x
          (φ.val (σ (secondBlockInfiniteCompact F h k) v)) =
        continuousRightAction F b (AdelicGL.ofInfinite F b k.val)
          (secondBlockConstantTermContinuous F h d x (φ.val v))
      rw [source_hasCompactEquivariance F φ, secondBlockConstantTermContinuous_compact])
    (fun v z hz => secondBlockConstantTerm_annihilated F h J I htransfer d x (φ.val v)
      ((Submodule.mem_iInf _).mp φ.property.2 v) L (source_hasLevel F φ v) z hz)
    (fun v => secondBlockConstantTerm_hasPolynomialGrowth F h d x (φ.val v) L (source_hasLevel F φ v))
  exact ⟨ψ.val, fun v y => congrArg (fun f => evaluate F b f y) (ψ.property v)⟩

end Langlands.Automorphic
