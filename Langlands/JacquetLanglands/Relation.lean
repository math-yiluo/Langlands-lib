import Langlands.JacquetLanglands.DivisionUnits
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-!
# The local Jacquet–Langlands relation

For a nonarchimedean local field `F` and a central division algebra `D` of dimension `n^2`
over `F`, an irreducible essentially square-integrable representation `ρ` of `GL_n(F)` and an
irreducible admissible representation `ρ'` of `Dˣ` are related when their characters satisfy
`Θ_ρ(g) = (-1)^(n-1) Θ_ρ'(g')` for all corresponding regular elliptic `g` and `g'`.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW uV₂ uW₂

section Irreducible

variable {G : Type*} [Monoid G]

/-- Equivalent representations are irreducible together. -/
theorem isIrreducible_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.bijective).1 h

/-- The trivial representation on `ℂ` is irreducible. -/
theorem isIrreducible_trivial (G : Type*) [Monoid G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  have : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ ℂ)
      (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine { eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Irreducible

section Relation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
  [TopologicalSpace D] [IsModuleTopology F D]

/-- The local Jacquet–Langlands relation between a representation `ρ` of `GL_n(F)` and a
representation `ρ'` of `Dˣ`: `D` has dimension `n^2` over `F`; `ρ` is irreducible and
essentially square-integrable; `ρ'` is irreducible; both are admissible; and for every regular
elliptic `g` and regular `g'` that correspond (same characteristic polynomial), the characters
have values at `g` and `g'` satisfying `Θ_ρ(g) = (-1)^(n-1) Θ_ρ'(g')`. -/
def IsJacquetLanglandsPair (n : ℕ) {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GeneralLinear n F) V)
    (ρ' : Representation ℂ Dˣ W) : Prop :=
  haveI := generalLinear_t2Space F n
  haveI := generalLinear_locallyCompactSpace F n
  haveI := generalLinear_totallyDisconnectedSpace F n
  haveI := units_isTopologicalGroup F D
  haveI := units_t2Space F D
  haveI := units_locallyCompactSpace F D
  haveI := units_totallyDisconnectedSpace F D
  Module.finrank F D = n ^ 2 ∧ ρ.IsIrreducible ∧ IsEssentiallySquareIntegrable ρ ∧
    ρ'.IsIrreducible ∧
    ∃ (hρ : IsAdmissible ρ) (hρ' : IsAdmissible ρ'),
      ∀ (g : GeneralLinear n F) (g' : Dˣ), Corresponds F D g g' →
        ∃ c : ℂ, HasCharacterValue ρ hρ g ((-1) ^ (n - 1) * c) ∧ HasCharacterValue ρ' hρ' g' c

variable {F D} {n : ℕ}
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GeneralLinear n F) V} {ρ' : Representation ℂ Dˣ W}

namespace IsJacquetLanglandsPair

theorem finrank_eq (h : IsJacquetLanglandsPair F D n ρ ρ') : Module.finrank F D = n ^ 2 :=
  h.1

theorem isIrreducible (h : IsJacquetLanglandsPair F D n ρ ρ') : ρ.IsIrreducible :=
  h.2.1

theorem isEssentiallySquareIntegrable (h : IsJacquetLanglandsPair F D n ρ ρ') :
    IsEssentiallySquareIntegrable ρ :=
  h.2.2.1

theorem isIrreducible_right (h : IsJacquetLanglandsPair F D n ρ ρ') : ρ'.IsIrreducible :=
  h.2.2.2.1

theorem isAdmissible (h : IsJacquetLanglandsPair F D n ρ ρ') : IsAdmissible ρ :=
  h.2.2.2.2.1

theorem isAdmissible_right (h : IsJacquetLanglandsPair F D n ρ ρ') : IsAdmissible ρ' :=
  h.2.2.2.2.2.1

/-- The character identity: if the characters of `ρ` and `ρ'` have the values `a` at `g` and
`b` at `g'`, and `g` corresponds to `g'`, then `a = (-1)^(n-1) b`. -/
theorem character_eq (h : IsJacquetLanglandsPair F D n ρ ρ') {g : GeneralLinear n F} {g' : Dˣ}
    (hg : Corresponds F D g g') {a b : ℂ}
    (ha : haveI := generalLinear_t2Space F n
      haveI := generalLinear_locallyCompactSpace F n
      haveI := generalLinear_totallyDisconnectedSpace F n
      HasCharacterValue ρ h.isAdmissible g a)
    (hb : haveI := units_isTopologicalGroup F D
      haveI := units_t2Space F D
      haveI := units_locallyCompactSpace F D
      haveI := units_totallyDisconnectedSpace F D
      HasCharacterValue ρ' h.isAdmissible_right g' b) :
    a = (-1) ^ (n - 1) * b := by
  have := generalLinear_t2Space F n
  have := generalLinear_locallyCompactSpace F n
  have := generalLinear_totallyDisconnectedSpace F n
  have := units_isTopologicalGroup F D
  have := units_t2Space F D
  have := units_locallyCompactSpace F D
  have := units_totallyDisconnectedSpace F D
  exact (exists_hasCharacterValue_mul_iff _ ha hb).1 (h.2.2.2.2.2.2 g g' hg)

end IsJacquetLanglandsPair

variable {V₂ : Type uV₂} {W₂ : Type uW₂} [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂]
  [Module ℂ W₂]

/-- The relation only depends on the equivalence classes of `ρ` and `ρ'`. -/
theorem IsJacquetLanglandsPair.of_equiv {σ : Representation ℂ (GeneralLinear n F) V₂}
    {σ' : Representation ℂ Dˣ W₂} (e : ρ.Equiv σ) (e' : ρ'.Equiv σ')
    (h : IsJacquetLanglandsPair F D n ρ ρ') : IsJacquetLanglandsPair F D n σ σ' := by
  have := generalLinear_t2Space F n
  have := generalLinear_locallyCompactSpace F n
  have := generalLinear_totallyDisconnectedSpace F n
  have := units_isTopologicalGroup F D
  have := units_t2Space F D
  have := units_locallyCompactSpace F D
  have := units_totallyDisconnectedSpace F D
  obtain ⟨hdim, hirr, hess, hirr', hρ, hρ', hc⟩ := h
  have hσ := isAdmissible_of_equiv e hρ
  have hσ' := isAdmissible_of_equiv e' hρ'
  refine ⟨hdim, isIrreducible_of_equiv e hirr,
    (isEssentiallySquareIntegrable_iff_of_equiv e).1 hess, isIrreducible_of_equiv e' hirr',
    hσ, hσ', fun g g' hg => ?_⟩
  obtain ⟨c, hcg, hcg'⟩ := hc g g' hg
  refine ⟨c, ?_, ?_⟩
  · exact (hasCharacterValue_iff_of_equivariant ρ hρ σ hσ e.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v) g _).1 hcg
  · exact (hasCharacterValue_iff_of_equivariant ρ' hρ' σ' hσ' e'.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e'.toIntertwiningMap.isIntertwining' g) v) g' c).1 hcg'

theorem isJacquetLanglandsPair_iff_of_equiv {σ : Representation ℂ (GeneralLinear n F) V₂}
    {σ' : Representation ℂ Dˣ W₂} (e : ρ.Equiv σ) (e' : ρ'.Equiv σ') :
    IsJacquetLanglandsPair F D n ρ ρ' ↔ IsJacquetLanglandsPair F D n σ σ' :=
  ⟨IsJacquetLanglandsPair.of_equiv e e', IsJacquetLanglandsPair.of_equiv e.symm e'.symm⟩

end Relation

section Bundled

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
  [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ)

/-- The Jacquet–Langlands relation between bundled smooth representations of `GL_n(F)` and
`Dˣ`. -/
def IsJacquetLanglandsSmoothPair (A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F))
    (B : SmoothRep.{0, u, uW} ℂ Dˣ) : Prop :=
  IsJacquetLanglandsPair F D n A.representation B.representation

variable {F D n}

theorem isJacquetLanglandsSmoothPair_iff_of_iso {A₁ A₂ : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)}
    {B₁ B₂ : SmoothRep.{0, u, uW} ℂ Dˣ} (e : A₁ ≅ A₂) (e' : B₁ ≅ B₂) :
    IsJacquetLanglandsSmoothPair F D n A₁ B₁ ↔ IsJacquetLanglandsSmoothPair F D n A₂ B₂ :=
  isJacquetLanglandsPair_iff_of_equiv (SmoothRep.equivOfIso e) (SmoothRep.equivOfIso e')

variable (F D n)

/-- The Jacquet–Langlands relation between isomorphism classes of smooth representations of
`GL_n(F)` and `Dˣ`, well defined by `isJacquetLanglandsSmoothPair_iff_of_iso`. -/
def IsJacquetLanglandsClassPair (π : SmoothRep.IsoClass.{0, u, uV} ℂ (GeneralLinear n F))
    (π' : SmoothRep.IsoClass.{0, u, uW} ℂ Dˣ) : Prop :=
  Quotient.lift₂ (s₁ := CategoryTheory.isIsomorphicSetoid (SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)))
    (s₂ := CategoryTheory.isIsomorphicSetoid (SmoothRep.{0, u, uW} ℂ Dˣ))
    (IsJacquetLanglandsSmoothPair F D n)
    (fun A₁ B₁ A₂ B₂ hA hB => by
      obtain ⟨e⟩ : Nonempty (A₁ ≅ A₂) := hA
      obtain ⟨e'⟩ : Nonempty (B₁ ≅ B₂) := hB
      exact propext (isJacquetLanglandsSmoothPair_iff_of_iso e e')) π π'

variable {F D n}

@[simp]
theorem isJacquetLanglandsClassPair_isoClass (A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F))
    (B : SmoothRep.{0, u, uW} ℂ Dˣ) :
    IsJacquetLanglandsClassPair F D n (SmoothRep.isoClass A) (SmoothRep.isoClass B) ↔
      IsJacquetLanglandsSmoothPair F D n A B := by
  unfold IsJacquetLanglandsClassPair SmoothRep.isoClass
  exact Iff.rfl

end Bundled

section Example

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Nonvacuity: for `n = 1` and `D = F`, the trivial representations of `GL_1(F)` and `Fˣ`
on `ℂ` are related. Both characters are the constant `1`. -/
theorem isJacquetLanglandsPair_trivial_one :
    IsJacquetLanglandsPair F F 1 (Representation.trivial ℂ (GeneralLinear 1 F) ℂ)
      (Representation.trivial ℂ Fˣ ℂ) := by
  have := generalLinear_t2Space F 1
  have := generalLinear_locallyCompactSpace F 1
  have := generalLinear_totallyDisconnectedSpace F 1
  have := units_isTopologicalGroup F F
  have := units_t2Space F F
  have := units_locallyCompactSpace F F
  have := units_totallyDisconnectedSpace F F
  have hρ : IsAdmissible (Representation.trivial ℂ (GeneralLinear 1 F) ℂ) :=
    isAdmissible_of_finiteDimensional fun _ => ⟨⊤, fun _ => rfl⟩
  have hρ' : IsAdmissible (Representation.trivial ℂ Fˣ ℂ) :=
    isAdmissible_of_finiteDimensional fun _ => ⟨⊤, fun _ => rfl⟩
  refine ⟨by simp, isIrreducible_trivial _, isEssentiallySquareIntegrable_trivial_one F,
    isIrreducible_trivial _, hρ, hρ', fun g g' _ => ⟨1, ?_, ?_⟩⟩
  · convert hasCharacterValue_trace _ hρ g using 1
    rw [show Representation.trivial ℂ (GeneralLinear 1 F) ℂ g = 1 from rfl, LinearMap.trace_one]
    simp
  · convert hasCharacterValue_trace _ hρ' g' using 1
    rw [show Representation.trivial ℂ Fˣ ℂ g' = 1 from rfl, LinearMap.trace_one]
    simp

end Example

end Langlands.JacquetLanglands
