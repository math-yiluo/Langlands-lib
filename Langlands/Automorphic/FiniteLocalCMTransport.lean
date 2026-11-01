import Langlands.Automorphic.CuspidalCMTransport
import Langlands.Automorphic.LocalRealization
import Mathlib.RepresentationTheory.Irreducible

/-! # Actual CM images of finite and local automorphic realizations -/

noncomputable section
universe uK uL

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGLTransport

open AdelicFunctoriality

/-- Arithmetic transport carries an identity-supported local matrix to the
corresponding actual local matrix insertion. -/
theorem finiteEquiv_localInclusion
    {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
    (n : ℕ) (e : K ≃+* L) (v : FinitePlace L)
    (g : FiniteLocalGL K n (finitePlaceEquiv e v)) :
    finiteEquiv n e (FiniteAdelicGL.localInclusion K n (finitePlaceEquiv e v) g) =
      FiniteAdelicGL.localInclusion L n v (localEquiv n e v g) := by
  apply FiniteAdelicGL.ext_localProjection L n
  intro w
  rw [localProjection_finiteEquiv]
  by_cases h : w = v
  · subst w
    simp only [FiniteAdelicGL.localProjection_localInclusion]
  · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne K n _ _
      ((finitePlaceEquiv e).injective.ne h),
      FiniteAdelicGL.localProjection_localInclusion_of_ne L n v w h, map_one]

end Langlands.Global.AdelicGLTransport

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance finiteLocalCMRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance finiteLocalCMContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance finiteLocalCMFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance finiteLocalCMFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

private def cmGroupCovariantOrderIso
    {G H V W : Type*} [Monoid G] [Monoid H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ H W)
    (α : H ≃* G) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ g f, τ g (e f) = e (ρ (α g) f)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun P :=
    { toSubmodule := P.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule g _ hf := by
        change ∃ f, f ∈ P.toSubmodule ∧ e f = _ at hf
        obtain ⟨f, hf, rfl⟩ := hf
        rw [hc]
        exact Submodule.mem_map_of_mem (P.apply_mem_toSubmodule (α g) hf) }
  invFun Q :=
    { toSubmodule := Q.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule g f hf := by
        change e (ρ g f) ∈ Q
        have hcov := hc (α.symm g) f
        rw [α.apply_symm_apply] at hcov
        rw [← hcov]
        exact Q.apply_mem_toSubmodule (α.symm g) hf }
  left_inv P := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).symm_apply_apply P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).apply_symm_apply Q.toSubmodule)
  map_rel_iff' := (Submodule.orderIsoMapComap e).map_rel_iff

namespace AutomorphicForms

/-- The local argument moves from the conjugate finite place to the original
one through the actual completion isomorphism. -/
theorem complexConj_localRightAction (v : FinitePlace K)
    (g : FiniteLocalGL K n
      (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v))
    (f : AutomorphicForms K n) :
    complexConj n (automorphicLocalRightAction K n v
        (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj K) v g) f) =
      automorphicLocalRightAction K n
        (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v) g
        (complexConj n f) := by
  have h := complexConj_finiteRightAction n
    (FiniteAdelicGL.localInclusion K n
      (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v) g) f
  rw [← AdelicGLTransport.finiteEquiv_complexConj,
    AdelicGLTransport.finiteEquiv_localInclusion] at h
  exact h

end AutomorphicForms

namespace FiniteRealization

/-- Image and preimage under actual CM function pullback identify the finite
invariant-subspace lattices. -/
def complexConjOrderIso : FiniteRealization K n ≃o FiniteRealization K n :=
  cmGroupCovariantOrderIso (automorphicFiniteRightAction K n)
    (automorphicFiniteRightAction K n) (CMConjugation.finiteConj K n).toMulEquiv
    (AutomorphicForms.complexConj n).toLinearEquiv
    (fun g f => (AutomorphicForms.complexConj_finiteRightAction n g f).symm)

variable (S : FiniteRealization K n)

local instance finiteCMImageSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual CM image of the embedded finite adelic form space. -/
def complexConj : FiniteRealization K n := complexConjOrderIso S

@[simp] theorem complexConj_toSubmodule :
    S.complexConj.toSubmodule = S.toSubmodule.map
      (AutomorphicForms.complexConj n).toLinearMap := rfl

@[simp] theorem complexConj_complexConj : S.complexConj.complexConj = S := by
  apply Subrepresentation.toSubmodule_injective
  change (S.toSubmodule.map (AutomorphicForms.complexConj n).toLinearMap).map
      (AutomorphicForms.complexConj n).toLinearMap = S.toSubmodule
  rw [← Submodule.map_comp]
  have hc : (AutomorphicForms.complexConj (K := K) n).toLinearMap.comp
      (AutomorphicForms.complexConj n).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact AutomorphicForms.complexConj_complexConj n
  rw [hc, Submodule.map_id]

/-- CM pullback is a continuous linear equivalence onto its actual image. -/
def complexConjEquiv : S.Space ≃L[ℂ] S.complexConj.Space :=
  (AutomorphicForms.complexConj n).ofSubmodules _ _ rfl

@[simp] theorem complexConjEquiv_val (f : S.Space) :
    (S.complexConjEquiv f).val = AutomorphicForms.complexConj n f.val := rfl

@[simp] theorem complexConjEquiv_symm_val (f : S.complexConj.Space) :
    (S.complexConjEquiv.symm f).val = AutomorphicForms.complexConj n f.val := by
  change (AutomorphicForms.complexConj n).symm f.val = _
  rw [AutomorphicForms.complexConj_symm]

theorem complexConjEquiv_representation (g : FiniteAdelicGL K n) (f : S.Space) :
    S.complexConj.representation g (S.complexConjEquiv f) =
      S.complexConjEquiv (S.representation (CMConjugation.finiteConj K n g) f) := by
  apply Subtype.ext
  exact (AutomorphicForms.complexConj_finiteRightAction n g f.val).symm

/-- The image representation is equivalent to the actual arithmetic pullback
of the original representation. -/
def complexConjRepresentationEquiv :
    Representation.Equiv
      (S.representation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      S.complexConj.representation :=
  Representation.Equiv.mk S.complexConjEquiv.toLinearEquiv (fun g => by
    apply LinearMap.ext
    intro f
    exact (S.complexConjEquiv_representation g f).symm)

@[simp] theorem complexConjRepresentationEquiv_apply (f : S.Space) :
    S.complexConjRepresentationEquiv f = S.complexConjEquiv f := rfl

@[simp] theorem toContinuous_complexConjEquiv (f : S.Space) :
    S.complexConj.toContinuous (S.complexConjEquiv f) =
      ContinuousRationalFunctions.complexConj n (S.toContinuous f) := rfl

@[simp] theorem evaluate_complexConjEquiv (f : S.Space) (g : AdelicGL K n) :
    evaluate K n (S.complexConj.toContinuous (S.complexConjEquiv f)) g =
      evaluate K n (S.toContinuous f) (CMConjugation.adelicConj K n g) :=
  AutomorphicForms.evaluate_complexConj n f.val g

@[simp] theorem evaluate_complexConjEquiv_symm
    (f : S.complexConj.Space) (g : AdelicGL K n) :
    evaluate K n (S.toContinuous (S.complexConjEquiv.symm f)) g =
      evaluate K n (S.complexConj.toContinuous f) (CMConjugation.adelicConj K n g) := by
  change evaluate K n (automorphicToContinuous K n (S.complexConjEquiv.symm f).val) g = _
  rw [complexConjEquiv_symm_val]
  exact AutomorphicForms.evaluate_complexConj n f.val g

@[simp] theorem complexConj_eq_bot_iff : S.complexConj = ⊥ ↔ S = ⊥ := by
  change complexConjOrderIso S = ⊥ ↔ S = ⊥
  constructor
  · intro h
    exact (complexConjOrderIso (K := K) (n := n)).injective
      (h.trans (complexConjOrderIso (K := K) (n := n)).map_bot.symm)
  · rintro rfl
    exact (complexConjOrderIso (K := K) (n := n)).map_bot

theorem complexConj_mono {T : FiniteRealization K n} (h : S ≤ T) :
    S.complexConj ≤ T.complexConj := complexConjOrderIso.monotone h

/-- The same covariance identifies invariant subspaces of the restricted actions. -/
def complexConjSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o Subrepresentation S.complexConj.representation :=
  cmGroupCovariantOrderIso S.representation S.complexConj.representation
    (CMConjugation.finiteConj K n).toMulEquiv S.complexConjEquiv.toLinearEquiv
    S.complexConjEquiv_representation

@[simp] theorem complexConj_isIrreducible_iff :
    S.complexConj.IsIrreducible ↔ S.IsIrreducible :=
  S.complexConjSubrepresentationOrderIso.isSimpleOrder_iff.symm

theorem complexConj_hasCentralCharacter_iff (χ : HeckeCharacter K) :
    S.complexConj.HasCentralCharacter χ.complexConj ↔ S.HasCentralCharacter χ := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (AutomorphicForms.complexConj_mem_centralCharacter_iff n χ f).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧ AutomorphicForms.complexConj n g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact (AutomorphicForms.complexConj_mem_centralCharacter_iff n χ g).mpr (hs hg)

variable [CompactSpace (AdeleQuotient K)]

@[simp] theorem complexConj_isCuspidal_iff :
    S.complexConj.IsCuspidal ↔ S.IsCuspidal := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (AutomorphicForms.complexConj_mem_cuspidal_iff n f).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧ AutomorphicForms.complexConj n g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact (AutomorphicForms.complexConj_mem_cuspidal_iff n g).mpr (hs hg)

end FiniteRealization

namespace LocalRealization

/-- An actual local realization at v has its CM image at the pulled-back place. -/
def complexConjOrderIso (v : FinitePlace K) :
    LocalRealization K n v ≃o LocalRealization K n
      (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v) :=
  cmGroupCovariantOrderIso (automorphicLocalRightAction K n v)
    (automorphicLocalRightAction K n
      (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v))
    (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj K) v).toMulEquiv
    (AutomorphicForms.complexConj n).toLinearEquiv
    (fun g f => (AutomorphicForms.complexConj_localRightAction v g f).symm)

variable {v : FinitePlace K} (S : LocalRealization K n v)

local instance localCMImageSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

def complexConj : LocalRealization K n
    (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v) :=
  complexConjOrderIso v S

@[simp] theorem complexConj_toSubmodule :
    S.complexConj.toSubmodule = S.toSubmodule.map
      (AutomorphicForms.complexConj n).toLinearMap := rfl

/-- The double image is the original actual subspace; the local indices may
be propositionally, rather than definitionally, equal. -/
@[simp] theorem complexConj_complexConj_toSubmodule :
    S.complexConj.complexConj.toSubmodule = S.toSubmodule := by
  change (S.toSubmodule.map (AutomorphicForms.complexConj n).toLinearMap).map
      (AutomorphicForms.complexConj n).toLinearMap = S.toSubmodule
  rw [← Submodule.map_comp]
  have hc : (AutomorphicForms.complexConj (K := K) n).toLinearMap.comp
      (AutomorphicForms.complexConj n).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact AutomorphicForms.complexConj_complexConj n
  rw [hc, Submodule.map_id]

def complexConjEquiv : S.Space ≃L[ℂ] S.complexConj.Space :=
  (AutomorphicForms.complexConj n).ofSubmodules _ _ rfl

@[simp] theorem complexConjEquiv_val (f : S.Space) :
    (S.complexConjEquiv f).val = AutomorphicForms.complexConj n f.val := rfl

@[simp] theorem complexConjEquiv_symm_val (f : S.complexConj.Space) :
    (S.complexConjEquiv.symm f).val = AutomorphicForms.complexConj n f.val := by
  change (AutomorphicForms.complexConj n).symm f.val = _
  rw [AutomorphicForms.complexConj_symm]

theorem complexConjEquiv_representation
    (g : FiniteLocalGL K n
      (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v)) (f : S.Space) :
    S.complexConj.representation g (S.complexConjEquiv f) =
      S.complexConjEquiv (S.representation
        (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj K) v g) f) := by
  apply Subtype.ext
  exact (AutomorphicForms.complexConj_localRightAction v g f.val).symm

/-- Pullback along the actual corresponding completion group is genuinely
equivalent to the action on the image form space. -/
def complexConjRepresentationEquiv :
    Representation.Equiv
    (S.representation.comp
      (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj K) v).toMonoidHom)
        S.complexConj.representation :=
  Representation.Equiv.mk S.complexConjEquiv.toLinearEquiv (fun g => by
    apply LinearMap.ext
    intro f
    exact (S.complexConjEquiv_representation g f).symm)

@[simp] theorem complexConjRepresentationEquiv_apply (f : S.Space) :
    S.complexConjRepresentationEquiv f = S.complexConjEquiv f := rfl

@[simp] theorem toContinuous_complexConjEquiv (f : S.Space) :
    S.complexConj.toContinuous (S.complexConjEquiv f) =
      ContinuousRationalFunctions.complexConj n (S.toContinuous f) := rfl

@[simp] theorem evaluate_complexConjEquiv (f : S.Space) (g : AdelicGL K n) :
    evaluate K n (S.complexConj.toContinuous (S.complexConjEquiv f)) g =
      evaluate K n (S.toContinuous f) (CMConjugation.adelicConj K n g) :=
  AutomorphicForms.evaluate_complexConj n f.val g

@[simp] theorem evaluate_complexConjEquiv_symm
    (f : S.complexConj.Space) (g : AdelicGL K n) :
    evaluate K n (S.toContinuous (S.complexConjEquiv.symm f)) g =
      evaluate K n (S.complexConj.toContinuous f) (CMConjugation.adelicConj K n g) := by
  change evaluate K n (automorphicToContinuous K n (S.complexConjEquiv.symm f).val) g = _
  rw [complexConjEquiv_symm_val]
  exact AutomorphicForms.evaluate_complexConj n f.val g

@[simp] theorem complexConj_eq_bot_iff : S.complexConj = ⊥ ↔ S = ⊥ := by
  change complexConjOrderIso v S = ⊥ ↔ S = ⊥
  constructor
  · intro h
    exact (complexConjOrderIso (K := K) (n := n) v).injective
      (h.trans (complexConjOrderIso (K := K) (n := n) v).map_bot.symm)
  · rintro rfl
    exact (complexConjOrderIso (K := K) (n := n) v).map_bot

theorem complexConj_mono {T : LocalRealization K n v} (h : S ≤ T) :
    S.complexConj ≤ T.complexConj := (complexConjOrderIso v).monotone h

def complexConjSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o Subrepresentation S.complexConj.representation :=
  cmGroupCovariantOrderIso S.representation S.complexConj.representation
    (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj K) v).toMulEquiv
    S.complexConjEquiv.toLinearEquiv S.complexConjEquiv_representation

@[simp] theorem complexConj_isIrreducible_iff :
    S.complexConj.representation.IsIrreducible ↔ S.representation.IsIrreducible :=
  S.complexConjSubrepresentationOrderIso.isSimpleOrder_iff.symm

theorem complexConj_hasCentralCharacter_iff (χ : HeckeCharacter K) :
    S.complexConj.HasCentralCharacter χ.complexConj ↔ S.HasCentralCharacter χ := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (AutomorphicForms.complexConj_mem_centralCharacter_iff n χ f).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧ AutomorphicForms.complexConj n g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact (AutomorphicForms.complexConj_mem_centralCharacter_iff n χ g).mpr (hs hg)

variable [CompactSpace (AdeleQuotient K)]

@[simp] theorem complexConj_isCuspidal_iff :
    S.complexConj.IsCuspidal ↔ S.IsCuspidal := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (AutomorphicForms.complexConj_mem_cuspidal_iff n f).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧ AutomorphicForms.complexConj n g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact (AutomorphicForms.complexConj_mem_cuspidal_iff n g).mpr (hs hg)

end LocalRealization

/-- CM image and local restriction retain exactly the same embedded form subspace. -/
@[simp] theorem FiniteRealization.toLocal_complexConj
    (S : FiniteRealization K n) (v : FinitePlace K) :
    S.complexConj.toLocal K n
        (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v) =
      (S.toLocal K n v).complexConj :=
  Subrepresentation.toSubmodule_injective rfl

end Langlands.Automorphic
