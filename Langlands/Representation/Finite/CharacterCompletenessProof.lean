import Langlands.Representation.Finite.CharacterCompletenessStatement
import Langlands.Representation.Finite.VirtualCharacterProof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Irreducible

/-!
# Completeness of the irreducible characters of a finite group: proof

For a class function `f` and a representation `ρ`, the operator `Σ_g f(g) ρ(g)` commutes with the
action, hence is a scalar on an irreducible representation (Schur's lemma), and its trace is
`Σ_g f(g) χ_ρ(g)`. If `f` is orthogonal to every irreducible character, the operator vanishes on
every irreducible representation, hence on every representation (complete reducibility), hence on
the regular representation, where it sends `e_1` to `Σ_g f(g) e_g`; so `f = 0`. The irreducible
characters are orthonormal, hence linearly independent and finitely many, and a class function
minus its expansion `Σ_χ ⟨χ, f⟩ χ` is orthogonal to all of them. The class functions are the
functions on conjugacy classes, so their dimension is the number of conjugacy classes, which is
therefore the number of irreducible classes.
-/

noncomputable section

namespace Langlands.FiniteRep.CharacterCompleteness

open Module VirtualCharacter

universe uG uV

variable {G : Type uG} [Group G]

section ClassSum

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The operator `Σ_g f(g) ρ(g)` of a function on a finite group. -/
def classSum [Fintype G] (f : G → ℂ) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V :=
  ∑ g : G, f g • ρ g

variable [Fintype G]

/-- Intertwining maps commute with `Σ_g f(g) ρ(g)`. -/
theorem classSum_naturality {W : Type*} [AddCommGroup W] [Module ℂ W] (f : G → ℂ)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.IntertwiningMap σ) :
    φ.toLinearMap ∘ₗ classSum f ρ = classSum f σ ∘ₗ φ.toLinearMap := by
  refine LinearMap.ext fun v => ?_
  simp only [classSum, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun g _ =>
    congrArg (f g • ·) (LinearMap.congr_fun (φ.isIntertwining' g) v)

/-- For a class function, `Σ_g f(g) ρ(g)` commutes with the action. -/
theorem classSum_comm (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (ρ : Representation ℂ G V) (h : G) :
    classSum f ρ ∘ₗ ρ h = ρ h ∘ₗ classSum f ρ := by
  refine LinearMap.ext fun v => ?_
  simp only [classSum, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hf]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    inv_mul_cancel_right]

/-- `Σ_g f(g) ρ(g)` as a self-intertwiner, for a class function `f`. -/
def classSumIntertwining (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (ρ : Representation ℂ G V) : ρ.IntertwiningMap ρ where
  toLinearMap := classSum f ρ
  isIntertwining' := classSum_comm f hf ρ

/-- The trace of `Σ_g f(g) ρ(g)` is `Σ_g f(g) χ_ρ(g)`. -/
theorem trace_classSum [FiniteDimensional ℂ V] (f : G → ℂ) (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ V (classSum f ρ) = ∑ g : G, f g * ρ.character g := by
  simp only [classSum, map_sum, map_smul, smul_eq_mul]
  rfl

/-- **Schur's lemma for the class sum**: on an irreducible representation, if
`Σ_g f(g) χ_ρ(g) = 0` then `Σ_g f(g) ρ(g) = 0`. -/
theorem classSum_eq_zero_of_isIrreducible [FiniteDimensional ℂ V] (f : G → ℂ)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible ρ) (h0 : ∑ g : G, f g * ρ.character g = 0) :
    classSum f ρ = 0 := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (classSumIntertwining f hf ρ)
  have hcs : classSum f ρ = c • LinearMap.id := by
    have := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Algebra.algebraMap_eq_smul_one] at this
    exact this.symm
  have hdim : finrank ℂ V ≠ 0 := by
    intro h
    have : Subsingleton V := Module.finrank_zero_iff.mp h
    have htop : (⊤ : Subrepresentation ρ) = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      exact Subsingleton.elim _ _
    exact bot_ne_top htop.symm
  have htr := trace_classSum f ρ
  rw [h0, hcs, map_smul, LinearMap.trace_id, smul_eq_mul, mul_eq_zero] at htr
  rcases htr with hc0 | hd
  · rw [hcs, hc0, zero_smul]
  · exact absurd (by exact_mod_cast hd) hdim

end ClassSum

section Vanishing

variable [Fintype G]

/-- **Orthogonality to all irreducible characters kills the class sum** on every
finite-dimensional representation, by induction on the dimension: split off an irreducible
subrepresentation and a complement. -/
theorem classSum_eq_zero (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h0 : ∀ a : IrreducibleClass G, ∑ g : G, f g * character a.1 g = 0) (n : ℕ) :
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V), finrank ℂ V = n → classSum f ρ = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn
  have : NeZero (Nat.card G : ℂ) := FiniteCharacter.neZero_card
  by_cases hV : finrank ℂ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp hV
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨T, hT⟩ := FiniteCharacter.exists_isAtom ρ hV
  have hirr : T.toRepresentation.IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom T hT
  obtain ⟨C, hC⟩ := exists_isCompl T
  -- the irreducible summand
  have hTzero : classSum f T.toRepresentation = 0 := by
    let a : IrreducibleClass G := ⟨classOfRepresentation T.toRepresentation,
      ofRepresentation T.toRepresentation, rfl,
      VirtualCharacter.isIrreducible_of_equiv (modelEquiv T.toRepresentation) hirr⟩
    refine classSum_eq_zero_of_isIrreducible f hf _ hirr ?_
    have := h0 a
    rwa [show character a.1 = T.toRepresentation.character from
      character_classOfRepresentation _] at this
  -- the complement, by induction
  have hCzero : classSum f C.toRepresentation = 0 := by
    have hdim : finrank ℂ C.toSubmodule < n := by
      have h1 := Submodule.finrank_add_eq_of_isCompl (FiniteCharacter.isCompl_toSubmodule hC)
      have h2 : finrank ℂ T.toSubmodule ≠ 0 := by
        rw [Ne, Submodule.finrank_eq_zero]
        exact FiniteCharacter.toSubmodule_ne_bot hT.1
      omega
    exact ih _ hdim C.toRepresentation rfl
  -- the product
  have hprod : classSum f (T.toRepresentation.prod C.toRepresentation) = 0 := by
    refine LinearMap.ext fun z => Prod.ext ?_ ?_
    · have := LinearMap.congr_fun (classSum_naturality f
        (Representation.IntertwiningMap.fst ℂ T.toRepresentation C.toRepresentation)) z
      simp only [LinearMap.comp_apply, hTzero, LinearMap.zero_apply] at this
      exact this
    · have := LinearMap.congr_fun (classSum_naturality f
        (Representation.IntertwiningMap.snd ℂ T.toRepresentation C.toRepresentation)) z
      simp only [LinearMap.comp_apply, hCzero, LinearMap.zero_apply] at this
      exact this
  -- transport to `ρ`
  let e := FiniteCharacter.prodEquivOfIsCompl hC
  refine LinearMap.ext fun v => ?_
  have h := LinearMap.congr_fun (classSum_naturality f e.toIntertwiningMap) (e.symm v)
  simp only [LinearMap.comp_apply, hprod, LinearMap.zero_apply, map_zero] at h
  have hv : e.toIntertwiningMap.toLinearMap (e.symm v) = v := e.apply_symm_apply v
  rw [hv] at h
  exact h.symm

/-- The regular representation of `G` on functions `G → ℂ`: `(g · φ)(x) = φ(g⁻¹ x)`. -/
def regularRep : Representation ℂ G (G → ℂ) where
  toFun g :=
    { toFun := fun φ x => φ (g⁻¹ * x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ x
    simp
  map_mul' g h := by
    ext φ x
    simp [Module.End.mul_apply, mul_assoc]

/-- On the regular representation, the class sum sends the point mass at `1` to `f`. -/
theorem classSum_regularRep_single [DecidableEq G] (f : G → ℂ) :
    classSum f regularRep (Pi.single 1 1) = f := by
  funext x
  simp only [classSum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change ∑ g : G, f g * (Pi.single (1 : G) (1 : ℂ) : G → ℂ) (g⁻¹ * x) = f x
  simp only [Pi.single_apply, inv_mul_eq_one, mul_ite, mul_one, mul_zero]
  simp

/-- **A class function orthogonal to every irreducible character is zero** (sum form). -/
theorem eq_zero_of_sum_mul_character_eq_zero (f : G → ℂ)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h0 : ∀ a : IrreducibleClass G, ∑ g : G, f g * character a.1 g = 0) : f = 0 := by
  classical
  rw [← classSum_regularRep_single f,
    classSum_eq_zero.{uG, uG} f hf h0 _ regularRep rfl, LinearMap.zero_apply]

theorem pairing_apply (f h : G → ℂ) :
    pairing f h = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f g⁻¹ * h g := rfl

theorem pairing_smul (f h : G → ℂ) (c : ℂ) : pairing f (c • h) = c * pairing f h := by
  simp only [pairing_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

/-- **A class function orthogonal to every irreducible character is zero.** -/
theorem eq_zero_of_pairing_eq_zero (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h0 : ∀ a : IrreducibleClass G, pairing (character a.1) f = 0) : f = 0 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let f' : G → ℂ := fun g => f g⁻¹
  have hf' : ∀ g h : G, f' (h * g * h⁻¹) = f' g := by
    intro g h
    simp only [f', mul_inv_rev, inv_inv, ← mul_assoc]
    exact hf g⁻¹ h
  have h0' : ∀ a : IrreducibleClass G, ∑ g : G, f' g * character a.1 g = 0 := by
    intro a
    have h := h0 a
    rw [pairing_apply, mul_eq_zero, or_iff_right (inv_ne_zero hcard)] at h
    rw [← h]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    simp only [f', Equiv.inv_apply, inv_inv, mul_comm]
  have hz := eq_zero_of_sum_mul_character_eq_zero f' hf' h0'
  funext x
  have := congrFun hz x⁻¹
  simpa [f'] using this

end Vanishing

section Expansion

variable [Fintype G]

/-- **The irreducible characters are linearly independent** over `ℂ` (orthonormality). -/
theorem linearIndependent_character :
    LinearIndependent ℂ (fun a : IrreducibleClass G => character a.1) := by
  classical
  rw [linearIndependent_iff']
  intro s c hs b hb
  have h := congrArg (pairing (character b.1)) hs
  rw [map_zero, map_sum] at h
  simp only [pairing_smul, pairing_irreducible, mul_ite, mul_one, mul_zero] at h
  simpa [Finset.sum_ite_eq, hb] using h

/-- There are finitely many irreducible classes. -/
theorem finite_irreducibleClass : Finite (IrreducibleClass G) :=
  linearIndependent_character.finite

/-- **Expansion of a class function in irreducible characters.** -/
theorem eq_sum_pairing_smul [Fintype (IrreducibleClass G)] (f : G → ℂ)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f = ∑ a : IrreducibleClass G, pairing (character a.1) f • character a.1 := by
  classical
  set f₀ := f - ∑ a : IrreducibleClass G, pairing (character a.1) f • character a.1 with hf₀def
  have hf₀ : ∀ g h : G, f₀ (h * g * h⁻¹) = f₀ g := by
    intro g h
    simp only [hf₀def, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, hf, character_conj]
  have h0 : ∀ b : IrreducibleClass G, pairing (character b.1) f₀ = 0 := by
    intro b
    rw [hf₀def, map_sub, map_sum]
    simp only [pairing_smul, pairing_irreducible, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pairing_eq_zero f₀ hf₀ h0)

/-- **The irreducible characters span the class functions.** -/
theorem mem_span_character (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span ℂ (Set.range fun a : IrreducibleClass G => character a.1) := by
  have := finite_irreducibleClass (G := G)
  let := Fintype.ofFinite (IrreducibleClass G)
  rw [eq_sum_pairing_smul f hf]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- A class function with integral pairings is a virtual character. -/
theorem mem_virtualCharacters (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hint : ∀ a : IrreducibleClass G, ∃ n : ℤ, pairing (character a.1) f = n) :
    f ∈ virtualCharacters (k := ℂ) (G := G) := by
  have := finite_irreducibleClass (G := G)
  let := Fintype.ofFinite (IrreducibleClass G)
  choose n hn using hint
  refine ⟨∑ a : IrreducibleClass G, n a • ofClass a.1, ?_⟩
  rw [eq_sum_pairing_smul f hf, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_zsmul, virtualCharacter_ofClass, hn a, Int.cast_smul_eq_zsmul]

/-- A class function with natural pairings is the character of a representation. -/
theorem exists_character_eq (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hnat : ∀ a : IrreducibleClass G, ∃ n : ℕ, pairing (character a.1) f = n) :
    ∃ c : RepClass ℂ G, character c = f := by
  have := finite_irreducibleClass (G := G)
  let := Fintype.ofFinite (IrreducibleClass G)
  choose n hn using hnat
  refine ⟨∑ a : IrreducibleClass G, n a • a.1, ?_⟩
  change characterHom _ = f
  rw [eq_sum_pairing_smul f hf, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_nsmul, hn a, Nat.cast_smul_eq_nsmul]
  rfl

end Expansion

section Counting

variable (G)

/-- The class functions on `G`. -/
def classFunctions : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  add_mem' hf hf' g h := by simp only [Set.mem_ofPred_eq, Pi.add_apply] at *; rw [hf, hf']
  zero_mem' _ _ := rfl
  smul_mem' c f hf g h := by simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *; rw [hf]

variable {G}

/-- The class functions are the functions on conjugacy classes. -/
theorem range_funLeft_mk :
    LinearMap.range (LinearMap.funLeft ℂ ℂ (ConjClasses.mk : G → ConjClasses G)) =
      classFunctions G := by
  ext f
  constructor
  · rintro ⟨φ, rfl⟩ g h
    change φ (ConjClasses.mk (h * g * h⁻¹)) = φ (ConjClasses.mk g)
    rw [ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm]
  · intro hf
    refine ⟨Quotient.lift (s := IsConj.setoid G) f fun a b hab => ?_, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp hab
    exact (hf a c).symm

theorem finrank_classFunctions [Fintype G] :
    finrank ℂ (classFunctions G) = Nat.card (ConjClasses G) := by
  classical
  rw [← range_funLeft_mk, LinearMap.finrank_range_of_inj
    (LinearMap.funLeft_injective_of_surjective _ _ _ ConjClasses.mk_surjective),
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- **There are as many irreducible classes as conjugacy classes.** -/
theorem card_irreducibleClass [Fintype G] :
    Nat.card (IrreducibleClass G) = Nat.card (ConjClasses G) := by
  have := finite_irreducibleClass (G := G)
  let := Fintype.ofFinite (IrreducibleClass G)
  let v : IrreducibleClass G → classFunctions G := fun a =>
    ⟨character a.1, fun g h => character_conj a.1 g h⟩
  have hli : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (classFunctions G).subtype linearIndependent_character
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rintro ⟨f, hf⟩ -
    have hx : (⟨f, hf⟩ : classFunctions G) =
        ∑ a : IrreducibleClass G, pairing (character a.1) f • v a :=
      Subtype.ext (by
        rw [Submodule.coe_sum]
        exact eq_sum_pairing_smul f hf)
    rw [hx]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [← finrank_classFunctions, Module.finrank_eq_card_basis (Basis.mk hli hsp),
    Nat.card_eq_fintype_card]

end Counting

/-- **Completeness of the irreducible characters of a finite group.** -/
theorem finiteCharacterCompleteness (G : Type uG) [Group G] [Fintype G] :
    FiniteCharacterCompletenessStatement G :=
  ⟨finite_irreducibleClass, card_irreducibleClass, mem_span_character, mem_virtualCharacters,
    exists_character_eq⟩

end Langlands.FiniteRep.CharacterCompleteness
