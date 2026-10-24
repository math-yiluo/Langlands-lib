import Langlands.Automorphic.PresentedLocalCategory
import Langlands.Global.FiniteAdelicGL.PadicComparison

/-! # Canonical p-adic classes of actual automorphic local components -/

noncomputable section
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F]

local instance padicCategoryRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance padicCategoryContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance padicCategorySmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance padicCategoryFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance padicCategoryLocalSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F}
variable {r : ℕ} (S : LocalRealization F (r + 1) v)

section CanonicalTopology

local instance padicCategoryTopology (n : ℕ) : TopologicalSpace (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology n

/-- Smoothness of the actual action for the canonical p-adic matrix topology. -/
theorem isSmooth_canonical {n : ℕ} (S : LocalRealization F n v) :
    Langlands.IsSmooth S.representation := by
  change @Langlands.IsSmooth ℂ (FiniteLocalGL F n v) S.Space _ _ _ _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology n) S.representation
  rw [← localGL_topology_eq F v n]
  exact S.isSmooth

/-- Admissibility agrees across the proved equality of the two group topologies. -/
theorem isAdmissible_canonical_iff {n : ℕ} (S : LocalRealization F n v) :
    Langlands.IsAdmissible S.representation ↔ S.IsAdmissible := by
  change @Langlands.IsAdmissible ℂ (FiniteLocalGL F n v) S.Space _ _ _ _
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopology n) S.representation ↔ _
  rw [← localGL_topology_eq F v n]

/-- An actual form-space object in the canonical positive-rank correspondence category. -/
def padicObject (hI : S.IsIrreducible) (hA : S.IsAdmissible) :
    Correspondence.AutomorphicObject.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  ⟨Langlands.SmoothRep.of S.representation S.isSmooth_canonical,
    hI, S.isAdmissible_canonical_iff.mpr hA⟩

end CanonicalTopology

/-- The corresponding actual p-adic automorphic class, in the form-carrier universe. -/
def padicClass (hI : S.IsIrreducible) (hA : S.IsAdmissible) :
    Correspondence.AutomorphicClass.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  Correspondence.automorphicClassOf _ (S.padicObject hI hA)

/-- Equality is genuine equivalence of the original actual local actions. -/
theorem padicClass_eq_iff (T : LocalRealization F (r + 1) v)
    (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (hI' : T.IsIrreducible) (hA' : T.IsAdmissible) :
    S.padicClass hI hA = T.padicClass hI' hA' ↔
      Nonempty (S.representation.Equiv T.representation) :=
  Correspondence.automorphicClassOf_eq_iff _ _ _

/-- The canonical p-adic class preserves exactly the original smooth-class equality. -/
theorem padicClass_eq_iff_isoClass_eq (T : LocalRealization F (r + 1) v)
    (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (hI' : T.IsIrreducible) (hA' : T.IsAdmissible) :
    S.padicClass hI hA = T.padicClass hI' hA' ↔ S.isoClass = T.isoClass := by
  rw [S.padicClass_eq_iff T hI hA hI' hA', S.isoClass_eq_iff T]

/-- Sphericality in the correspondence is exactly nonzero actual integral fixedness. -/
theorem padicClass_isSpherical_iff (hI : S.IsIrreducible) (hA : S.IsAdmissible) :
    Correspondence.IsSphericalClass (CompletionPadic.padicField v) (S.padicClass hI hA) ↔
      Langlands.fixedVectors S.representation (localIntegral F (r + 1) v).toSubgroup ≠ ⊥ := by
  rw [localIntegral_eq_sphericalSubgroup F v r]
  constructor
  · rintro ⟨A, hAeq, hfixed⟩
    obtain ⟨e⟩ := (Correspondence.automorphicClassOf_eq_iff _ A
      (S.padicObject hI hA)).mp hAeq
    exact (Langlands.fixedVectors_ne_bot_iff_of_equiv e _).mp hfixed
  · intro hfixed
    exact ⟨S.padicObject hI hA, rfl, hfixed⟩

end LocalRealization

namespace FiniteTensorPresentation

variable {r : ℕ} {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)

/-- A presented actual local component, now in the canonical p-adic category. -/
def localPadicObject (hS : S.IsNonzero F (r + 1)) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Correspondence.AutomorphicObject.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  (P.localComponent hS v).padicObject
    ((P.localComponent_isIrreducible_iff hS v).mpr hI)
    ((P.localComponent_isAdmissible_iff hS v).mpr hA)

/-- Its correspondence class retains the actual form-space representative. -/
def localPadicClass (hS : S.IsNonzero F (r + 1)) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Correspondence.AutomorphicClass.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  Correspondence.automorphicClassOf _ (P.localPadicObject hS v hI hA)

/-- Varying a presentation of fixed tensor data preserves the canonical local class. -/
theorem localPadicClass_eq {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS : S.IsNonzero F (r + 1)) (hS' : S'.IsNonzero F (r + 1)) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    P.localPadicClass hS v hI hA = Q.localPadicClass hS' v hI hA :=
  ((P.localComponent hS v).padicClass_eq_iff_isoClass_eq
    (Q.localComponent hS' v) _ _ _ _).mpr (P.localComponentClass_eq Q hS hS' v)

/-- Sphericality is equivalent to nonzero integral fixedness of the specified factor. -/
theorem localPadicClass_isSpherical_iff
    (hS : S.IsNonzero F (r + 1)) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Correspondence.IsSphericalClass (CompletionPadic.padicField v)
      (P.localPadicClass hS v hI hA) ↔
        Langlands.fixedVectors (ρ v) (localIntegral F (r + 1) v).toSubgroup ≠ ⊥ :=
  ((P.localComponent hS v).padicClass_isSpherical_iff _ _).trans
    (Langlands.fixedVectors_ne_bot_iff_of_equiv (P.localComponentEquiv hS v) _).symm

/-- The nonzero integral-fixed reference vector makes the class spherical away from E. -/
theorem localPadicClass_isSpherical (hS : S.IsNonzero F (r + 1))
    (v : FinitePlace F) (hv : v ∉ E)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Correspondence.IsSphericalClass (CompletionPadic.padicField v)
      (P.localPadicClass hS v hI hA) := by
  apply (P.localPadicClass_isSpherical_iff hS v hI hA).mpr
  exact (P.localComponentDualClass_hasFixedVector_iff hS v hI hA _).mp
    (P.localComponentDualClass_hasIntegralFixedVector hS v hv hI hA)

end FiniteTensorPresentation
end Langlands.Automorphic
