import Langlands.Representation.FiniteQuotientSemisimplicity
import Langlands.Weil.Representation.UnramifiedDeterminant
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Trace

/-! # The self-twist test for restriction across a cyclic quotient -/

noncomputable section

namespace Langlands.CyclicRestriction

open Representation

universe uG uV uE
variable {G : Type uG} [Group G]

/-- If `N` and `g` generate the quotient decomposition, a subgroup containing
both is the whole group. The cyclic quotient can be infinite. -/
theorem eq_top_of_le_of_generator {N S : Subgroup G} {g : G}
    (hN : N ≤ S) (hg : g ∈ S) (hgen : ∀ x : G, ∃ i : ℤ, x * (g ^ i)⁻¹ ∈ N) :
    S = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hgen x
  simpa using S.mul_mem (hN hi) (S.zpow_mem hg i)

section Eigenline

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]
variable (R : Representation ℂ G E) (x : E)

/-- The subgroup acting on a vector by nonzero scalar multiples. For a nonzero
vector this is the stabilizer of the line it spans. -/
def eigenlineStabilizer : Subgroup G where
  carrier := {g | ∃ c : ℂˣ, R g x = (c : ℂ) • x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨d * c, ?_⟩
    simp [map_mul, Module.End.mul_apply, hd, hc, smul_smul]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have he : R g⁻¹ (R g x) = x := by rw [← Module.End.mul_apply, ← map_mul]; simp
    rw [hc, map_smul] at he
    calc
      R g⁻¹ x = (↑(c⁻¹) : ℂ) • ((c : ℂ) • R g⁻¹ x) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = _ := congrArg ((↑(c⁻¹) : ℂ) • ·) he

/-- The scalar by which an eigenline stabilizer element acts is unique when
its specified eigenvector is nonzero. -/
theorem eigenline_scalar_unique (hx : x ≠ 0) {a b : ℂˣ}
    (h : (a : ℂ) • x = (b : ℂ) • x) : a = b :=
  Units.ext (smul_left_injective ℂ hx h)

variable {R x}

/-- The scalar character when the entire group stabilizes the line. -/
def eigenlineCharacter (hx : x ≠ 0) (h : ∀ g : G, g ∈ eigenlineStabilizer R x) : G →* ℂˣ := by
  let c (g : G) := Classical.choose (h g)
  have hc (g : G) : R g x = (c g : ℂ) • x := Classical.choose_spec (h g)
  refine
    { toFun := c
      map_one' := eigenline_scalar_unique x hx ?_
      map_mul' := fun g k => eigenline_scalar_unique x hx ?_ }
  · exact (hc 1).symm.trans (by simp)
  · calc
      (c (g * k) : ℂ) • x = R (g * k) x := (hc _).symm
      _ = R g (R k x) := by rw [map_mul, Module.End.mul_apply]
      _ = R g ((c k : ℂ) • x) := congrArg (R g) (hc k)
      _ = (c k : ℂ) • ((c g : ℂ) • x) := (map_smul (R g) _ _).trans
        (congrArg ((c k : ℂ) • ·) (hc g))
      _ = ((c g * c k : ℂˣ) : ℂ) • x := by rw [smul_smul, Units.val_mul, mul_comm]

theorem eigenlineCharacter_apply_smul (hx : x ≠ 0)
    (h : ∀ g : G, g ∈ eigenlineStabilizer R x) (g : G) :
    R g x = (eigenlineCharacter hx h g : ℂ) • x := Classical.choose_spec (h g)

end Eigenline

section Representation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V)

/-- A finite-dimensional complex irreducible representation has only scalar
endomorphisms. -/
theorem end_eq_smul_one (hi : ρ.IsIrreducible) (f : ρ.IntertwiningMap ρ) :
    ∃ c : ℂ, f.toLinearMap = c • (1 : Module.End ℂ V) := by
  let:= hi
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective f
  exact ⟨c, (congrArg Representation.IntertwiningMap.toLinearMap hc).symm⟩

/-- Subspace of trace-zero endomorphisms commuting with the action of `N`. -/
def tracelessCentralizer (N : Subgroup G) : Submodule ℂ (Module.End ℂ V) :=
  Representation.invariants ((linHom ρ ρ).comp N.subtype) ⊓ LinearMap.ker (LinearMap.trace ℂ V)

variable (N : Subgroup G) [N.Normal]

omit [FiniteDimensional ℂ V] in
private theorem linHom_conj_normal {f : Module.End ℂ V}
    (hf : ∀ n : N, linHom ρ ρ n f = f) (g : G) (n : N) :
    linHom ρ ρ n (linHom ρ ρ g f) = linHom ρ ρ g f := by
  have hn : g⁻¹ * (n : G) * g ∈ N := Subgroup.Normal.conj_mem' ‹N.Normal› n n.property g
  calc
    linHom ρ ρ n (linHom ρ ρ g f) = linHom ρ ρ g (linHom ρ ρ (g⁻¹ * n * g) f) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 1
      simp [mul_assoc]
    _ = _ := congrArg (linHom ρ ρ g) (hf ⟨_, hn⟩)

omit [FiniteDimensional ℂ V] in
theorem linHom_mem_tracelessCentralizer (g : G) {f : Module.End ℂ V}
    (hf : f ∈ tracelessCentralizer ρ N) : linHom ρ ρ g f ∈ tracelessCentralizer ρ N := by
  rcases Submodule.mem_inf.mp hf with ⟨hN, ht⟩
  refine Submodule.mem_inf.mpr ⟨linHom_conj_normal ρ N hN g, ?_⟩
  have h := LinearMap.trace_conj ℂ f (ρ.asGroupHom g)
  rw [← map_inv, Representation.asGroupHom_apply, Representation.asGroupHom_apply] at h
  exact h.trans ht

omit [N.Normal] in
/-- A nonzero eigenoperator for conjugation with scalar character `χ`
intertwines the twist by `χ` with the original representation. It is an
isomorphism for irreducible `ρ`. -/
theorem equiv_twist_of_linHom_eigen (hi : ρ.IsIrreducible) (χ : G →* ℂˣ)
    {f : Module.End ℂ V} (hf : f ≠ 0)
    (hχ : ∀ g : G, linHom ρ ρ g f = (χ g : ℂ) • f) :
    Nonempty ((Langlands.twist χ ρ).Equiv ρ) := by
  let F : IntertwiningMap (Langlands.twist χ ρ) ρ := ⟨f, fun g => by
    change f * ((χ g : ℂ) • ρ g) = ρ g * f
    rw [mul_smul_comm]
    have he : ρ g * f * ρ g⁻¹ = (χ g : ℂ) • f := hχ g
    have hInv : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul]; simp
    have hp := congrArg (· * ρ g) he
    rwa [mul_assoc (ρ g * f), hInv, mul_one, smul_mul_assoc, eq_comm] at hp⟩
  have hF : F ≠ 0 := fun h => hf (congrArg IntertwiningMap.toLinearMap h)
  let:= hi
  have hs := (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  exact ⟨F.ofBijective ⟨LinearMap.injective_iff_surjective.mpr hs, hs⟩⟩

omit [N.Normal] [FiniteDimensional ℂ V] in
/-- A nonzero semisimple representation with only scalar endomorphisms is
irreducible, by projecting along a complementary subrepresentation. -/
theorem isIrreducible_of_scalar_ends [Nontrivial V] (hsemi : ρ.IsSemisimpleRepresentation)
    (hend : ∀ f : ρ.IntertwiningMap ρ, ∃ c : ℂ, f.toLinearMap = c • (1 : Module.End ℂ V)) :
    ρ.IsIrreducible := by
  let := hsemi
  let : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨W, hW⟩ := exists_isCompl U
  let P := FiniteQuotientAveraging.projectionOfIsCompl ρ U W hW
  have hP := FiniteQuotientAveraging.projectionOfIsCompl_isProj ρ U W hW
  obtain ⟨c, hc⟩ := hend P
  change LinearMap.IsProj U.toSubmodule P.toLinearMap at hP
  by_cases h0 : c = 0
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro v hv
    simpa [hc, h0] using (hP.2 v hv).symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro v _
    have hv := hP.1 (c⁻¹ • v)
    rwa [hc, LinearMap.smul_apply, Module.End.one_apply, smul_smul,
      mul_inv_cancel₀ h0, one_smul] at hv

omit [N.Normal] in
/-- In a nonzero semisimple representation, absence of a nonzero trace-zero
endomorphism implies irreducibility. -/
theorem isIrreducible_of_traceless_ends [Nontrivial V] (hsemi : ρ.IsSemisimpleRepresentation)
    (hend : ∀ f : ρ.IntertwiningMap ρ, LinearMap.trace ℂ V f.toLinearMap = 0 → f = 0) :
    ρ.IsIrreducible := by
  apply isIrreducible_of_scalar_ends ρ hsemi
  intro f
  let c := LinearMap.trace ℂ V f.toLinearMap / (Module.finrank ℂ V : ℂ)
  let F := f - c • IntertwiningMap.id ρ
  have hdim : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hF : LinearMap.trace ℂ V F.toLinearMap = 0 := by
    change LinearMap.trace ℂ V (f.toLinearMap - c • (1 : Module.End ℂ V)) = 0
    rw [map_sub, map_smul, LinearMap.trace_one, smul_eq_mul, div_mul_cancel₀ _ hdim, sub_self]
  exact ⟨c, congrArg IntertwiningMap.toLinearMap (sub_eq_zero.mp (hend F hF))⟩

/-- If an irreducible complex representation restricts semisimply to a normal
subgroup with cyclic quotient and admits no nontrivial self-twist trivial on that
subgroup, its restriction is irreducible. -/
theorem isIrreducible_comp_of_no_character_self_twist
    (hi : ρ.IsIrreducible) (hsemi : IsSemisimpleRepresentation (ρ.comp N.subtype))
    (g : G) (hgen : ∀ w : G, ∃ i : ℤ, w * (g ^ i)⁻¹ ∈ N)
    (hself : ∀ χ : G →* ℂˣ, N ≤ χ.ker →
      Nonempty ((Langlands.twist χ ρ).Equiv ρ) → χ = 1) :
    Representation.IsIrreducible (ρ.comp N.subtype) := by
  let:= hi
  let: Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let S := tracelessCentralizer ρ N
  have hS : S = ⊥ := by
    by_contra hS
    let: Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS
    let C : Module.End ℂ S := (linHom ρ ρ g).restrict
      (fun _ hf => linHom_mem_tracelessCentralizer ρ N g hf)
    obtain ⟨c, hc⟩ := C.exists_eigenvalue
    obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
    have hf_ne : (f : Module.End ℂ V) ≠ 0 := fun h => hf.2 (Subtype.ext h)
    have hf_g : linHom ρ ρ g (f : Module.End ℂ V) = c • (f : Module.End ℂ V) :=
      congrArg Subtype.val hf.apply_eq_smul
    have hc0 : c ≠ 0 := by
      intro h0
      apply hf_ne
      have hh := congrArg (linHom ρ ρ g⁻¹) hf_g
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        h0, zero_smul, map_zero] at hh
      exact hh
    have hn : ∀ n : N, linHom ρ ρ n (f : Module.End ℂ V) = f :=
      (Submodule.mem_inf.mp f.property).1
    let J := eigenlineStabilizer (linHom ρ ρ) (f : Module.End ℂ V)
    have hNJ : N ≤ J := fun n h => ⟨1, by simpa using hn ⟨n, h⟩⟩
    have hgJ : g ∈ J := ⟨Units.mk0 c hc0, hf_g⟩
    have hJ := eq_top_of_le_of_generator hNJ hgJ hgen
    let H (w : G) : w ∈ J := hJ ▸ Subgroup.mem_top w
    let χ := eigenlineCharacter hf_ne H
    have hχ (w : G) : linHom ρ ρ w (f : Module.End ℂ V) = (χ w : ℂ) • (f : Module.End ℂ V) :=
      eigenlineCharacter_apply_smul hf_ne H w
    have hχN : N ≤ χ.ker := by
      intro n h
      exact eigenline_scalar_unique _ hf_ne (by rw [← hχ n, hn ⟨n, h⟩]; simp)
    have hχ0 := hself χ hχN (equiv_twist_of_linHom_eigen ρ hi χ hf_ne hχ)
    have hfix (w : G) : linHom ρ ρ w (f : Module.End ℂ V) = f := by
      simpa [hχ0] using hχ w
    let U : (linHom ρ ρ).invariants := ⟨f, hfix⟩
    obtain ⟨a, ha⟩ := end_eq_smul_one ρ hi (invariantsEquivIntertwiningMap ρ ρ U)
    change (f : Module.End ℂ V) = a • (1 : Module.End ℂ V) at ha
    have ht : LinearMap.trace ℂ V (f : Module.End ℂ V) = 0 := (Submodule.mem_inf.mp f.property).2
    rw [ha, map_smul, smul_eq_mul, LinearMap.trace_one] at ht
    have ha0 := (mul_eq_zero.mp ht).resolve_right (by exact_mod_cast Module.finrank_pos.ne')
    exact hf_ne (by simp [ha, ha0])
  apply isIrreducible_of_traceless_ends _ hsemi
  intro f ht
  have hf : f.toLinearMap ∈ S := Submodule.mem_inf.mpr ⟨
    (mem_linHom_invariants_iff_isIntertwining f.toLinearMap).mpr ⟨f.isIntertwining⟩, ht⟩
  rw [hS, Submodule.mem_bot] at hf
  exact IntertwiningMap.ext hf

omit [N.Normal] in
/-- An irreducible restriction forbids all nontrivial self-twists trivial on the
subgroup. This direction does not require cyclicity. -/
theorem no_character_self_twist_of_irreducible_comp
    (hi : Representation.IsIrreducible (ρ.comp N.subtype)) (χ : G →* ℂˣ)
    (hχ : N ≤ χ.ker) (e : (Langlands.twist χ ρ).Equiv ρ) : χ = 1 := by
  let R : Representation ℂ N V := ρ.comp N.subtype
  let f : R.IntertwiningMap R := ⟨e.toLinearMap, fun n => by
    have he := e.isIntertwining' (n : G)
    have hn : χ n = 1 := hχ n.property
    change e.toLinearMap ∘ₗ ((χ n : ℂ) • ρ n) = ρ n ∘ₗ e.toLinearMap at he
    change e.toLinearMap ∘ₗ ρ n = ρ n ∘ₗ e.toLinearMap
    simpa only [hn, Units.val_one, one_smul] using he⟩
  obtain ⟨c, hc⟩ := end_eq_smul_one R hi f
  change e.toLinearMap = c • (1 : Module.End ℂ V) at hc
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) R.asModule
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply e.toLinearEquiv.injective
    change e.toLinearMap v = e.toLinearMap 0
    simp [hc, h0]
  ext g
  have he := e.isIntertwining' g
  change e.toLinearMap * ((χ g : ℂ) • ρ g) = ρ g * e.toLinearMap at he
  rw [mul_smul_comm, hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul] at he
  have hg0 : ρ g ≠ 0 := (ρ.asGroupHom g).ne_zero
  have hval := smul_left_injective ℂ hg0 he
  exact mul_right_cancel₀ hc0 (hval.trans (one_mul c).symm)

omit [N.Normal] [FiniteDimensional ℂ V] in
/-- A genuine self-twist has character values of order dividing the rank, by
taking determinants of the two equivalent matrices. -/
theorem pow_finrank_eq_one_of_equiv_twist {χ : G →* ℂˣ}
    (e : (Langlands.twist χ ρ).Equiv ρ) (g : G) :
    χ g ^ Module.finrank ℂ V = 1 := by
  have he : e.toLinearEquiv.conj (Langlands.twist χ ρ g) = ρ g := by
    ext v
    change e.toLinearEquiv (Langlands.twist χ ρ g (e.toLinearEquiv.symm v)) = ρ g v
    have hh := Representation.IntertwiningMap.isIntertwining _ _
      e.toIntertwiningMap g (e.toLinearEquiv.symm v)
    change _ = ρ g (e.toLinearEquiv (e.toLinearEquiv.symm v)) at hh
    rwa [LinearEquiv.apply_symm_apply] at hh
  have hd : LinearMap.det (Langlands.twist χ ρ g) = LinearMap.det (ρ g) :=
    (LinearMap.det_conj (Langlands.twist χ ρ g) e.toLinearEquiv).symm.trans
      (congrArg LinearMap.det he)
  rw [Langlands.det_twist] at hd
  have h0 : LinearMap.det (ρ g) ≠ 0 :=
    (Units.map (LinearMap.det : Module.End ℂ V →* ℂ) (ρ.asGroupHom g)).ne_zero
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact mul_right_cancel₀ h0 (hd.trans (one_mul _).symm)

/-- Coprimality of the cyclic quotient's index with the rank forces
irreducibility of a semisimple restriction. -/
theorem isIrreducible_comp_of_cyclic_coprime [IsCyclic (G ⧸ N)]
    (hi : ρ.IsIrreducible) (hsemi : IsSemisimpleRepresentation (ρ.comp N.subtype))
    (hc : Nat.Coprime N.index (Module.finrank ℂ V)) :
    Representation.IsIrreducible (ρ.comp N.subtype) := by
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (G ⧸ N))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
  apply isIrreducible_comp_of_no_character_self_twist ρ N hi hsemi g
  · intro w
    have hw : QuotientGroup.mk' N w ∈ Subgroup.zpowers (QuotientGroup.mk' N g) := by
      rw [ha]
      exact Subgroup.mem_top _
    obtain ⟨i, hi⟩ := hw
    change QuotientGroup.mk' N g ^ i = QuotientGroup.mk' N w at hi
    refine ⟨i, (QuotientGroup.eq_one_iff _).mp ?_⟩
    change QuotientGroup.mk' N (w * (g ^ i)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, hi, mul_inv_cancel]
  · rintro χ hχ ⟨e⟩
    ext w
    have hpow : χ w ^ N.index = 1 := by
      simpa only [MonoidHom.mem_ker, map_pow] using hχ (N.pow_index_mem w)
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_of_pow_eq_one (pow_finrank_eq_one_of_equiv_twist ρ e w))
    rw [hc.gcd_eq_one, Nat.dvd_one] at hd
    exact congrArg Units.val (orderOf_eq_one_iff.mp hd)

end Representation

section Semisimplicity

variable {H : Type*} [Group H] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Pullback along a surjective group homomorphism preserves semisimplicity:
subspaces stable under the pullback are stable under the whole target action. -/
theorem isSemisimpleRepresentation_comp_of_surjective
    (ρ : Representation ℂ H V) (π : G →* H) (hπ : Function.Surjective π)
    (hρ : IsSemisimpleRepresentation ρ) : IsSemisimpleRepresentation (ρ.comp π) := by
  let := hρ
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ := ⟨U.toSubmodule, fun h v hv => by
    obtain ⟨g, rfl⟩ := hπ h
    exact U.apply_mem_toSubmodule g hv⟩
  obtain ⟨W, hW⟩ := exists_isCompl U'
  let W' : Subrepresentation (ρ.comp π) :=
    ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (π g) hv⟩
  refine ⟨W', disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
  · exact Subrepresentation.toSubmodule_injective
      (congrArg (Subrepresentation.toSubmodule : Subrepresentation ρ → Submodule ℂ V)
        hW.inf_eq_bot)
  · exact Subrepresentation.toSubmodule_injective
      (congrArg (Subrepresentation.toSubmodule : Subrepresentation ρ → Submodule ℂ V)
        hW.sup_eq_top)

end Semisimplicity

end Langlands.CyclicRestriction
