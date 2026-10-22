import Langlands.Representation.Classification.SupercuspidalContragredientStatement
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.RingTheory.SimpleModule.Basic

noncomputable section

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G]

section Smooth

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact-open fixed-vector duality reflects admissibility for smooth representations. -/
theorem isAdmissible_of_smoothContragredient
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hdual : IsAdmissible (smoothContragredient ρ)) : IsAdmissible ρ := by
  refine ⟨hρ, fun K => ?_⟩
  obtain ⟨L, hLc, hLK⟩ := hcofinal K
  let := hdual.2 L
  let e := LinearEquiv.ofBijective (smoothDualFixedRestriction ρ L.toSubgroup)
    (smoothDualFixedRestriction_bijective ρ hρ L hLc)
  have : Module.Finite ℂ (Module.Dual ℂ (fixedVectors ρ L.toSubgroup)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have : Module.Finite ℂ (fixedVectors ρ L.toSubgroup) :=
    (Module.finite_dual_iff ℂ).mp inferInstance
  exact finite_fixedVectors_of_le (show L.toSubgroup ≤ K.toSubgroup from hLK)


/-- Injectivity of smooth evaluation says precisely that smooth functionals separate vectors. -/
theorem eq_zero_of_smoothDual_annihilates (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hinj : Function.Injective (smoothBidual hρ))
    {v : V} (hv : ∀ ℓ : SmoothDual ρ, ℓ.1 v = 0) : v = 0 := by
  apply hinj
  apply Subtype.ext
  ext ℓ
  change ℓ.1 v = ℓ.1 0
  simpa only [map_zero] using hv ℓ

/-- Smooth separation on a representation and its quotients reflects irreducibility. -/
theorem isIrreducible_of_smoothContragredient
    (hsep : ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ G W) (hσ : IsSmooth σ),
      Function.Injective (smoothBidual hσ))
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hdual : Representation.IsIrreducible (smoothContragredient ρ)) :
    Representation.IsIrreducible ρ := by
  let := hdual
  have hnonzero : Nontrivial (SmoothDual ρ) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) (smoothContragredient ρ).asModule
  have hV : Nontrivial V := by
    by_contra h
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton (SmoothDual ρ) := inferInstance
    exact not_subsingleton (SmoothDual ρ) this
  have : Nontrivial (Subrepresentation ρ) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have hmem : v ∈ (⊥ : Subrepresentation ρ) := h.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from trivial)
    exact hv hmem
  refine { eq_bot_or_eq_top := fun W => ?_ }
  let A : Subrepresentation (smoothContragredient ρ) :=
    { toSubmodule := W.toSubmodule.dualAnnihilator.comap (smoothVectors ρ.dual).subtype
      apply_mem_toSubmodule := by
        intro g ℓ hℓ
        apply (Submodule.mem_dualAnnihilator _).mpr
        intro v hv
        exact (Submodule.mem_dualAnnihilator _).mp hℓ
          (ρ g⁻¹ v) (W.apply_mem_toSubmodule g⁻¹ hv) }
  rcases eq_bot_or_eq_top A with hA | hA
  · right
    let σ := Representation.quotient ρ W.toSubmodule W.apply_mem_toSubmodule
    let q : ρ.IntertwiningMap σ :=
      { toLinearMap := W.toSubmodule.mkQ
        isIntertwining' := fun _ => rfl }
    have hσ : IsSmooth σ := isSmooth_of_surjective q W.toSubmodule.mkQ_surjective hρ
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    apply eq_zero_of_smoothDual_annihilates σ hσ (hsep _ σ hσ)
    intro ℓ
    have hℓ : contragredientMap q ℓ ∈ A := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro w hw
      change ℓ.1 (W.toSubmodule.mkQ w) = 0
      have hwq : W.toSubmodule.mkQ w = 0 :=
        (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr hw
      rw [hwq, map_zero]
    have hz : contragredientMap q ℓ ∈ (⊥ : Subrepresentation (smoothContragredient ρ)) := hA ▸ hℓ
    change contragredientMap q ℓ = 0 at hz
    exact congrArg (fun f : SmoothDual ρ => f.1 v) hz
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply eq_zero_of_smoothDual_annihilates ρ hρ (hsep _ ρ hρ)
    intro ℓ
    have hℓ : ℓ ∈ A := hA.symm ▸ (show ℓ ∈ (⊤ : Subrepresentation (smoothContragredient ρ)) from trivial)
    exact (Submodule.mem_dualAnnihilator _).mp hℓ v hv

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- An actual representation equivalence preserves irreducibility. -/
theorem isIrreducible_iff_of_equiv
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.bijective

/-- Smooth separation and canonical bidual reflexivity give irreducibility in both directions. -/
theorem isIrreducible_smoothContragredient_iff_of_bidual
    (hsep : ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ G W) (hσ : IsSmooth σ),
      Function.Injective (smoothBidual hσ))
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hbidual : Function.Bijective (smoothBidual hρ)) :
    Representation.IsIrreducible (smoothContragredient ρ) ↔
      Representation.IsIrreducible ρ := by
  constructor
  · exact isIrreducible_of_smoothContragredient hsep ρ hρ
  · intro hirr
    apply isIrreducible_of_smoothContragredient hsep (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ)
    exact (isIrreducible_iff_of_equiv ((smoothBidual hρ).ofBijective hbidual)).mp hirr

end Smooth

namespace Jacquet

variable {R : Type*} [CommRing R]
variable {U : Type*} [AddCommGroup U] [Module R U]

/-- Conjugation acts on the actual quotient by sending `[v]` to `[rho(g)v]`. -/
def coinvariantsConjEquiv (ρ : Representation R G U) (N : Subgroup G) (g : G) :
    Coinvariants ρ N ≃ₗ[R] Coinvariants ρ (N.map (MulAut.conj g).toMonoidHom) := by
  let N' := N.map (MulAut.conj g).toMonoidHom
  let f : Coinvariants ρ N →ₗ[R] Coinvariants ρ N' :=
    lift ρ N ((mk ρ N').comp (ρ g)) (by
      intro n
      ext v
      have hn : g * n * g⁻¹ ∈ N' := ⟨n, n.property, rfl⟩
      have h := mk_apply_subgroup ρ N' ⟨g * n * g⁻¹, hn⟩ (ρ g v)
      simpa [map_mul, Module.End.mul_apply] using h)
  let b : Coinvariants ρ N' →ₗ[R] Coinvariants ρ N :=
    lift ρ N' ((mk ρ N).comp (ρ g⁻¹)) (by
      intro n
      ext v
      obtain ⟨m, hm, hmn⟩ := n.property
      have hn : g⁻¹ * n * g ∈ N := by
        rw [← hmn]
        simpa [MulAut.conj_apply, mul_assoc] using hm
      have h := mk_apply_subgroup ρ N ⟨g⁻¹ * n * g, hn⟩ (ρ g⁻¹ v)
      simpa [map_mul, Module.End.mul_apply] using h)
  exact
    { f with
      invFun := b
      left_inv := by
        intro x
        obtain ⟨v, rfl⟩ := mk_surjective ρ N x
        change mk ρ N (ρ g⁻¹ (ρ g v)) = mk ρ N v
        simp
      right_inv := by
        intro x
        obtain ⟨v, rfl⟩ := mk_surjective ρ N' x
        change mk ρ N' (ρ g (ρ g⁻¹ v)) = mk ρ N' v
        simp }

/-- Jacquet vanishing is unchanged under conjugation of the subgroup. -/
theorem coinvariants_conj_subsingleton_iff (ρ : Representation R G U)
    (N : Subgroup G) (g : G) :
    Subsingleton (Coinvariants ρ (N.map (MulAut.conj g).toMonoidHom)) ↔
      Subsingleton (Coinvariants ρ N) := by
  let e := coinvariantsConjEquiv ρ N g
  constructor
  · intro h
    exact ⟨fun x y => e.injective (h.elim _ _)⟩
  · intro h
    exact ⟨fun x y => e.symm.injective (h.elim _ _)⟩

end Jacquet

namespace GeneralLinear

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual all-conjugates condition can be tested on the standard block radicals. -/
theorem isSupercuspidal_iff_standard (ρ : Representation ℂ (GeneralLinear n F) V) :
    IsSupercuspidal ρ ↔
      IsAdmissible ρ ∧ ∀ B : BlockShape n, B.parabolic F ≠ ⊤ →
        Subsingleton (Jacquet.Coinvariants ρ (B.unipotentSubgroup F)) := by
  constructor
  · rintro ⟨hadm, hvan⟩
    exact ⟨hadm, fun B hB =>
      (Jacquet.coinvariants_conj_subsingleton_iff ρ _ 1).mp (hvan B hB 1)⟩
  · rintro ⟨hadm, hvan⟩
    exact ⟨hadm, fun B hB g =>
      (Jacquet.coinvariants_conj_subsingleton_iff ρ _ g).mpr (hvan B hB)⟩

end GeneralLinear
end Langlands
