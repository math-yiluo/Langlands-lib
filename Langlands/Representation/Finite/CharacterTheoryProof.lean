import Langlands.Representation.Finite.CharacterStatement
import Langlands.Representation.Category.FiniteIndexRestriction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Finite complex character theory

Proofs of the conjuncts of `Langlands.FiniteCharacterTheoryStatement`.
-/

noncomputable section

namespace Langlands.FiniteCharacter

open Module

universe uG uV uW

section Normalization

variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- The trace of an endomorphism that is diagonal in a finite basis. -/
theorem trace_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (f : V →ₗ[ℂ] V) (c : ι → ℂ) (h : ∀ i, f (b i) = c i • b i) :
    LinearMap.trace ℂ V f = ∑ i, c i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [LinearMap.toMatrix_apply, h]

/-- The character at an inverse is the complex conjugate of the character. -/
theorem character_inv_eq_star (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  classical
  set n := Fintype.card G
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hpow : ρ g ^ n = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have hss : Module.End.IsSemisimple (ρ g) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (Polynomial.X ^ n - Polynomial.C 1 : Polynomial ℂ))
    · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hn)
        one_ne_zero).squarefree
    · simp [hpow]
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Module.End.eigenspaces_iSupIndep (ρ g)) hss.iSup_eigenspace_eq_top
  let I := (ν : ℂ) × Fin (finrank ℂ (Module.End.eigenspace (ρ g) ν))
  let v : Basis I ℂ V := eigenDecomp.collectedBasis fun μ => finBasis ℂ (Module.End.eigenspace (ρ g) μ)
  have : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let μ : I → ℂ := Sigma.fst
  have hvec (i : I) : Module.End.HasEigenvector (ρ g) (μ i) (v i) :=
    ⟨eigenDecomp.collectedBasis_mem _ i, v.ne_zero i⟩
  have hsv (i : I) : ρ g (v i) = μ i • v i := (hvec i).apply_eq_smul
  have hμn (i : I) : μ i ^ n = 1 := by
    have h1 := (hvec i).pow_apply n
    rw [hpow, Module.End.one_apply] at h1
    have h2 : (μ i ^ n - 1) • v i = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (v.ne_zero i))
  have hμ0 (i : I) : μ i ≠ 0 := by
    intro h0
    have := hμn i
    rw [h0, zero_pow hn] at this
    exact zero_ne_one this
  have hinv (i : I) : ρ g⁻¹ (v i) = (μ i)⁻¹ • v i := by
    have h1 : ρ g⁻¹ (ρ g (v i)) = v i := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hsv, map_smul] at h1
    calc ρ g⁻¹ (v i) = (μ i)⁻¹ • (μ i • ρ g⁻¹ (v i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hμ0 i), one_smul]
      _ = (μ i)⁻¹ • v i := by rw [h1]
  rw [Representation.character, Representation.character,
    trace_eq_sum_of_eigenbasis v _ _ hsv, trace_eq_sum_of_eigenbasis v _ _ hinv, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (hμn i) hn)

theorem normalization : FiniteCharacterNormalizationStatement G V := by
  intro ρ
  refine ⟨Representation.char_one ρ, character_inv_eq_star ρ, fun g h =>
    Representation.char_conj ρ g h, fun g => Representation.char_dual ρ g⟩

end Normalization

section Lattice

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

theorem iSupIndep_toSubmodule {ι : Type*} {S : ι → Subrepresentation ρ} (h : iSupIndep S) :
    iSupIndep fun i => (S i).toSubmodule := by
  intro i
  have h2 := congrArg Subrepresentation.toSubmodule (disjoint_iff.mp (h i))
  simp only [Subrepresentation.toSubmodule_inf, Langlands.Subrepresentation.toSubmodule_iSup] at h2
  exact disjoint_iff.mpr h2

theorem isCompl_toSubmodule {p q : Subrepresentation ρ} (h : IsCompl p q) :
    IsCompl p.toSubmodule q.toSubmodule := by
  constructor
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, h.inf_eq_bot]
    rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, h.sup_eq_top]
    rfl

theorem toSubmodule_ne_bot {p : Subrepresentation ρ} (h : p ≠ ⊥) : p.toSubmodule ≠ ⊥ :=
  fun h' => h (Subrepresentation.toSubmodule_injective h')

/-- Complementary subrepresentations decompose the representation as their product. -/
def prodEquivOfIsCompl {p q : Subrepresentation ρ} (h : IsCompl p q) :
    Representation.Equiv (p.toRepresentation.prod q.toRepresentation) ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl _ _ (isCompl_toSubmodule h)) fun g => by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_prodEquivOfIsCompl',
      Representation.prod_apply_apply, map_add]
    rfl

theorem prodEquivOfIsCompl_apply {p q : Subrepresentation ρ} (h : IsCompl p q)
    (z : p.toSubmodule × q.toSubmodule) :
    prodEquivOfIsCompl h z = (z.1 : V) + z.2 :=
  Submodule.coe_prodEquivOfIsCompl' _ _ (isCompl_toSubmodule h) z

/-- An injective intertwining map is an equivalence onto its range. -/
def equivRange {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    Representation.Equiv ρ f.range.toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g => by
    refine LinearMap.ext fun v => Subtype.ext ?_
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v

/-- Equivalences of the factors give an equivalence of the products. -/
def prodCongr {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {σ₁ : Representation ℂ G W₁} {σ₂ : Representation ℂ G W₂}
    (e₁ : Representation.Equiv ρ₁ σ₁) (e₂ : Representation.Equiv ρ₂ σ₂) :
    Representation.Equiv (ρ₁.prod ρ₂) (σ₁.prod σ₂) :=
  Representation.Equiv.mk (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) fun g => by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply,
      Representation.prod_apply_apply]
    exact Prod.ext
      (Representation.IntertwiningMap.isIntertwining _ _ e₁.toIntertwiningMap g x.1)
      (Representation.IntertwiningMap.isIntertwining _ _ e₂.toIntertwiningMap g x.2)

theorem character_prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) :
    (ρ₁.prod ρ₂).character = ρ₁.character + ρ₂.character := by
  funext g
  change LinearMap.trace ℂ (V₁ × V₂) ((ρ₁ g).prodMap (ρ₂ g)) =
    LinearMap.trace ℂ V₁ (ρ₁ g) + LinearMap.trace ℂ V₂ (ρ₂ g)
  exact LinearMap.trace_prodMap' _ _

end Lattice

section HomDimension

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem card_inv_mul_sum_eq_finrank (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g⁻¹ * σ.character g =
      (finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ) := by
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ, Nat.card_eq_fintype_card]
  simp_rw [mul_comm (ρ.character _)]

end HomDimension

section Decomposition

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem neZero_card : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- A finite-dimensional complex representation of a finite group is the internal direct sum
of finitely many atoms of its subrepresentation lattice. -/
theorem exists_decomposition (ρ : Representation ℂ G V) :
    ∃ (n : ℕ) (S : Fin n → Subrepresentation ρ),
      (∀ i, IsAtom (S i)) ∧ iSupIndep S ∧ ⨆ i, S i = ⊤ := by
  classical
  have : NeZero (Nat.card G : ℂ) := neZero_card
  have : IsNoetherian (MonoidAlgebra ℂ G) ρ.asModule := isNoetherian_of_tower ℂ inferInstance
  obtain ⟨s, hind, htop, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (R := MonoidAlgebra ℂ G)
      (M := ρ.asModule)
  have hfin : s.Finite := WellFoundedGT.finite_of_sSupIndep hind
  have := hfin.to_subtype
  let e := Finite.equivFin s
  let O := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  refine ⟨Nat.card s, fun i => O.symm (e.symm i).1, fun i => ?_, ?_, ?_⟩
  · rw [O.symm.isAtom_iff]
    exact isSimpleModule_iff_isAtom.mp (hsimple _ (e.symm i).2)
  · exact (((sSupIndep_iff s).mp hind).comp e.symm.injective).map_orderIso O.symm
  · rw [← O.symm.map_iSup (fun i => (e.symm i).1), e.symm.iSup_comp (g := fun m : s => m.1),
      ← sSup_eq_iSup', htop, O.symm.map_top]

theorem exists_isAtom (ρ : Representation ℂ G V) (h : finrank ℂ V ≠ 0) :
    ∃ T : Subrepresentation ρ, IsAtom T := by
  obtain ⟨n, S, hat, -, htop⟩ := exists_decomposition ρ
  rcases n with _ | n
  · exfalso
    apply h
    have htb : (⊤ : Subrepresentation ρ) = ⊥ := by
      rw [← htop]
      exact iSup_of_empty _
    have h2 := congrArg (fun p : Subrepresentation ρ => finrank ℂ p.toSubmodule) htb
    change finrank ℂ (⊤ : Submodule ℂ V) = finrank ℂ (⊥ : Submodule ℂ V) at h2
    rwa [finrank_top, finrank_bot] at h2
  · exact ⟨S 0, hat 0⟩

theorem completeReducibility : FiniteCompleteReducibilityStatement G V := by
  classical
  intro ρ
  have : NeZero (Nat.card G : ℂ) := neZero_card
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, S, hat, hind, htop⟩ := exists_decomposition ρ
  refine ⟨n, S, fun i =>
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom _ (hat i), ⟨?_⟩⟩
  have hint : DirectSum.IsInternal fun i => (S i).toSubmodule :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_toSubmodule hind) (by
      rw [← Langlands.Subrepresentation.toSubmodule_iSup, htop]
      rfl)
  have hbij : Function.Bijective (DirectSum.coeLinearMap fun i => (S i).toSubmodule) := hint
  refine Representation.Equiv.mk (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hbij)
    fun g => ?_
  refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply,
    Representation.directSum_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  rfl

end Decomposition

section Orthogonality

variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem homDimension : FiniteCharacterHomDimensionStatement G V W :=
  fun ρ σ => card_inv_mul_sum_eq_finrank ρ σ

theorem orthogonality : FiniteCharacterOrthogonalityStatement G V W := by
  intro ρ σ hρ hσ
  refine ⟨fun ⟨e⟩ => ?_, fun he => ?_⟩
  · rw [← Representation.char_iso e, card_inv_mul_sum_eq_finrank,
      Representation.IsIrreducible.finrank_intertwiningMap_self, Nat.cast_one]
  · have : IsEmpty (Representation.Equiv ρ σ) := not_nonempty_iff.mp he
    rw [card_inv_mul_sum_eq_finrank, Module.finrank_zero_of_subsingleton, Nat.cast_zero]

end Orthogonality

section Isomorphism

variable {G : Type uG} [Group G] [Fintype G]

/-- Equal characters give an intertwining equivalence; the proof is by strong induction on
the dimension of the source, splitting off an irreducible subrepresentation. -/
theorem nonempty_equiv_of_character_eq (n : ℕ) :
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
      finrank ℂ V = n → ρ.character = σ.character → Nonempty (Representation.Equiv ρ σ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ W _ _ _ ρ σ hn hχ
  have : NeZero (Nat.card G : ℂ) := neZero_card
  by_cases h0 : finrank ℂ V = 0
  · have hW : finrank ℂ W = 0 := by
      have h1 := congrFun hχ 1
      rw [Representation.char_one, Representation.char_one, h0] at h1
      exact_mod_cast h1.symm
    have : Subsingleton V := Module.finrank_zero_iff.mp h0
    have : Subsingleton W := Module.finrank_zero_iff.mp hW
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton V W) fun g =>
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  obtain ⟨T, hT⟩ := exists_isAtom ρ h0
  have : T.toRepresentation.IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom T hT
  have hTb : T.toSubmodule ≠ ⊥ := toSubmodule_ne_bot hT.1
  let ι : Representation.IntertwiningMap T.toRepresentation ρ :=
    ⟨T.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have hι : ι ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTb
    exact hx0 (congrArg (fun f : Representation.IntertwiningMap T.toRepresentation ρ =>
      f ⟨x, hx⟩) h)
  have hpos : 0 < finrank ℂ (Representation.IntertwiningMap T.toRepresentation σ) := by
    have hTρ := card_inv_mul_sum_eq_finrank T.toRepresentation ρ
    have hTσ := card_inv_mul_sum_eq_finrank T.toRepresentation σ
    rw [hχ] at hTρ
    rw [hTρ] at hTσ
    rw [← Nat.cast_injective hTσ]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨ι, hι⟩
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hfinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  obtain ⟨C, hC⟩ := exists_isCompl T
  obtain ⟨C', hC'⟩ := exists_isCompl f.range
  have hρχ : ρ.character = T.toRepresentation.character + C.toRepresentation.character :=
    (Representation.char_iso (prodEquivOfIsCompl hC)).symm.trans (character_prod _ _)
  have hσχ : σ.character =
      f.range.toRepresentation.character + C'.toRepresentation.character :=
    (Representation.char_iso (prodEquivOfIsCompl hC')).symm.trans (character_prod _ _)
  have hCχ : C.toRepresentation.character = C'.toRepresentation.character := by
    have h := hρχ.symm.trans (hχ.trans hσχ)
    rw [Representation.char_iso (equivRange f hfinj)] at h
    exact add_left_cancel h
  have hdim : finrank ℂ C.toSubmodule < n := by
    have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_toSubmodule hC)
    have h2 : finrank ℂ T.toSubmodule ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact hTb
    omega
  obtain ⟨eC⟩ := ih _ hdim C.toRepresentation C'.toRepresentation rfl hCχ
  exact ⟨((prodEquivOfIsCompl hC).symm.trans (prodCongr (equivRange f hfinj) eC)).trans
    (prodEquivOfIsCompl hC')⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem isomorphism : FiniteCharacterIsomorphismStatement G V W := fun ρ σ =>
  ⟨nonempty_equiv_of_character_eq _ ρ σ rfl, fun ⟨e⟩ => Representation.char_iso e⟩

end Isomorphism

section NormOne

variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem normOne : FiniteCharacterNormOneStatement G V := by
  intro ρ
  rw [card_inv_mul_sum_eq_finrank, Nat.cast_eq_one]
  refine ⟨fun h1 => ?_, fun h => Representation.IsIrreducible.finrank_intertwiningMap_self ρ⟩
  have : NeZero (Nat.card G : ℂ) := neZero_card
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : Subsingleton (Representation.IntertwiningMap ρ ρ) :=
      ⟨fun f g => Representation.IntertwiningMap.ext
        (LinearMap.ext fun _ => Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h1
    exact zero_ne_one h1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    change (⊥ : Submodule ℂ V) = ⊤ at h'
    exact bot_ne_top h'
  by_contra hirr
  obtain ⟨p, hpb, hpt⟩ : ∃ p : Subrepresentation ρ, p ≠ ⊥ ∧ p ≠ ⊤ := by
    by_contra! h
    exact hirr
      { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
        eq_bot_or_eq_top := fun p => (em (p = ⊥)).imp id (h p) }
  obtain ⟨q, hq⟩ := exists_isCompl p
  have hqb : q ≠ ⊥ := fun h => hpt (eq_top_of_isCompl_bot (h ▸ hq))
  let P := p.toSubmodule
  let Q := q.toSubmodule
  have hPQ : IsCompl P Q := isCompl_toSubmodule hq
  let E := prodEquivOfIsCompl hq
  let π : Representation.IntertwiningMap ρ ρ :=
    E.toIntertwiningMap.comp
      ((Representation.IntertwiningMap.inl ℂ p.toRepresentation q.toRepresentation).comp
        ((Representation.IntertwiningMap.fst ℂ p.toRepresentation q.toRepresentation).comp
          E.symm.toIntertwiningMap))
  have hπ (v : V) : π v = E ((E.symm v).1, 0) := rfl
  have hπP (x : V) (hx : x ∈ P) : π x = x := by
    have h1 : E.symm x = (⟨x, hx⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left P Q hPQ ⟨x, hx⟩
    rw [hπ, h1, prodEquivOfIsCompl_apply]
    simp
  have hπQ (y : V) (hy : y ∈ Q) : π y = 0 := by
    have h1 : E.symm y = (0, ⟨y, hy⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right P Q hPQ ⟨y, hy⟩
    rw [hπ, h1, prodEquivOfIsCompl_apply]
    simp
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (toSubmodule_ne_bot hpb)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (toSubmodule_ne_bot hqb)
  have hid : Representation.IntertwiningMap.id ρ ≠ 0 := by
    intro h
    exact hx0 (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).mp h1 π
  have hcy := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f y) hc
  have hcx := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc
  simp only [Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.id_apply]
    at hcy hcx
  rw [hπQ y hy] at hcy
  rw [hπP x hx] at hcx
  have hc0 : c = 0 := (smul_eq_zero.mp hcy).resolve_right hy0
  rw [hc0, zero_smul] at hcx
  exact hx0 hcx.symm

end NormOne

/-- The finite complex character-theory prerequisites used by Henniart. -/
theorem finiteCharacterTheory
    (G : Type uG) [Group G] [Fintype G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    FiniteCharacterTheoryStatement G V W :=
  ⟨normalization, normalization, completeReducibility, completeReducibility, homDimension,
    orthogonality, isomorphism, normOne, normOne⟩

end Langlands.FiniteCharacter
