import Langlands.MathlibBase
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyIrreducible
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Restriction

/-!
# Monodromy of lisse sheaves: simple objects and change of group

Let `M` be a monodromy of lisse `ℓ`-adic sheaves on a scheme `Y` which is an equivalence at a
geometric point `t` (weil-conjectures's `AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`).

* On a locally Noetherian `Y`, a lisse sheaf is a simple object of the category of lisse sheaves
  exactly when its monodromy representation is irreducible
  (`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt.simple_iff_isIrreducible`).
* For a group `H` with a homomorphism `f : H →* π₁(Y, t)` which is a bijective homeomorphism, the
  restricted representations `M.rep t G ∘ f` have continuous matrix coefficients, every
  `H`-equivariant linear map of stalks is the stalk of a morphism, and every finite-dimensional
  representation of `H` with continuous matrix coefficients is equivalent to some `M.rep t G ∘ f`.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt

open Scheme.FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} {M : LisseMonodromy l Y Ω}

/-- A lisse sheaf is zero in the category of lisse sheaves when it is zero as an `ℓ`-adic
sheaf. -/
lemma isZero_of_isZero_obj {G : LisseSheaf l Y} (h : IsZero G.obj) : IsZero G :=
  ⟨fun H => ⟨⟨⟨ObjectProperty.homMk (h.to_ H.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_src _ _)⟩⟩,
    fun H => ⟨⟨⟨ObjectProperty.homMk (h.from_ H.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_tgt _ _)⟩⟩⟩

/-- The zero morphism of lisse sheaves has zero stalk map. -/
lemma lisseStalkMap_eq_zero {G H : LisseSheaf l Y} :
    lisseStalkMap t (0 : G ⟶ H) = 0 := by
  have : (0 : G ⟶ H) = ObjectProperty.homMk (0 : G.obj ⟶ H.obj) := rfl
  rw [this, lisseStalkMap_zero]

/-- **Simple lisse sheaves and irreducible monodromy.** On a locally Noetherian scheme, a lisse
sheaf is a simple object of the category of lisse sheaves if and only if its monodromy
representation at a base point at which the monodromy is an equivalence is irreducible. -/
theorem simple_iff_isIrreducible (hM : M.IsEquivalenceAt t) [IsLocallyNoetherian Y]
    (G : LisseSheaf l Y) : Simple G ↔ (M.rep t G).IsIrreducible := by
  rw [Representation.isIrreducible_iff]
  constructor
  · intro hG
    refine ⟨?_, fun S hS => ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      exact Simple.not_isZero G (isZero_of_isZero_obj (hM.isZero_of_subsingleton G))
    · obtain ⟨G', a, hinj, hrange⟩ := hM.exists_hom_range_eq ⟨S, hS⟩
      have hrange' : LinearMap.range (lisseStalkMap t a) = S := hrange
      have : Mono a.hom := hM.mono_of_injective a hinj
      have : Mono a := (ObjectProperty.ι _).mono_of_mono_map this
      by_cases ha : a = 0
      · left
        rw [← hrange', ha, lisseStalkMap_eq_zero, LinearMap.range_zero]
      · right
        have : IsIso a := (Simple.mono_isIso_iff_nonzero a).2 ha
        rw [← hrange', LinearMap.range_eq_top]
        exact (lisseStalkMap_bijective t a).2
  · rintro ⟨hV, hS⟩
    refine ⟨fun {G'} a _ => ?_⟩
    have hinj := hM.injective_of_mono a
    have hR : ∀ g, ∀ v ∈ LinearMap.range (lisseStalkMap t a),
        M.rep t G g v ∈ LinearMap.range (lisseStalkMap t a) := by
      rintro g _ ⟨w, rfl⟩
      exact ⟨M.rep t _ g w, M.rep_naturality t a g w⟩
    rcases hS _ hR with h | h
    · have hv (v : StalkSpace t G') : v = 0 := hinj <| by
        rw [map_zero]
        exact (Submodule.mem_bot _).1 (h ▸ LinearMap.mem_range_self _ v)
      have : Subsingleton (StalkSpace t G') := ⟨fun v w => (hv v).trans (hv w).symm⟩
      have hz : IsZero G' := isZero_of_isZero_obj (hM.isZero_of_subsingleton G')
      have ha0 : a = 0 := hz.eq_of_src _ _
      refine ⟨fun hiso => absurd ha0 ?_, fun hne => absurd ha0 hne⟩
      intro ha
      have hb := lisseStalkMap_bijective t a
      rw [ha, lisseStalkMap_eq_zero] at hb
      obtain ⟨v, hv⟩ := exists_ne (0 : StalkSpace t G)
      obtain ⟨w, hw⟩ := hb.2 v
      exact hv (hw.symm.trans rfl)
    · have hiso : IsIso a := hM.isIso_of_bijective a ⟨hinj, LinearMap.range_eq_top.1 h⟩
      refine ⟨fun _ ha => ?_, fun _ => hiso⟩
      have hb := lisseStalkMap_bijective t a
      rw [ha, lisseStalkMap_eq_zero] at hb
      obtain ⟨v, hv⟩ := exists_ne (0 : StalkSpace t G)
      obtain ⟨w, hw⟩ := hb.2 v
      exact hv (hw.symm.trans rfl)

section Transport

variable {H : Type*} [Group H] [TopologicalSpace H] (f : H →* Aut (fiber t))

/-- The restriction of a monodromy representation along a continuous homomorphism has continuous
matrix coefficients. -/
theorem continuous_rep_comp (hM : M.IsEquivalenceAt t) (hf : Continuous f)
    (G : LisseSheaf l Y) (φ : Module.Dual (PadicAlgCl l) (StalkSpace t G))
    (v : StalkSpace t G) : Continuous fun h => φ ((M.rep t G).comp f h v) :=
  (hM.continuous_rep G φ v).comp hf

omit [TopologicalSpace H] in
/-- Along a surjective homomorphism, every equivariant linear map of stalks is the stalk of a
morphism of lisse sheaves. -/
theorem full_comp (hM : M.IsEquivalenceAt t) (hf : Function.Surjective f)
    {G G' : LisseSheaf l Y}
    (φ : StalkSpace t G →ₗ[PadicAlgCl l] StalkSpace t G')
    (hφ : ∀ h v, φ ((M.rep t G).comp f h v) = (M.rep t G').comp f h (φ v)) :
    ∃ a : G ⟶ G', lisseStalkMap t a = φ := by
  refine hM.full φ fun g v => ?_
  obtain ⟨h, rfl⟩ := hf g
  exact hφ h v

/-- **Essential surjectivity along a homeomorphic isomorphism.** If `f : H →* π₁(Y, t)` is a
bijective homeomorphism, every finite-dimensional representation of `H` with continuous matrix
coefficients, on a carrier in universe `u + 1`, is equivalent to the restriction along `f` of the
monodromy representation of a lisse sheaf. -/
theorem essSurj_comp (hM : M.IsEquivalenceAt t) (hf : IsHomeomorph f)
    (V : Type (u + 1)) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (σ : Representation (PadicAlgCl l) H V)
    (hσ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V), Continuous fun h => φ (σ h v)) :
    ∃ (G : LisseSheaf l Y) (e : StalkSpace t G ≃ₗ[PadicAlgCl l] V),
      ∀ h v, e ((M.rep t G).comp f h v) = σ h (e v) := by
  let e₀ : H ≃* Aut (fiber t) := MulEquiv.ofBijective f hf.bijective
  let σ' : Representation (PadicAlgCl l) (Aut (fiber t)) V := σ.comp e₀.symm.toMonoidHom
  have hinv : Continuous e₀.symm := by
    have : (e₀.symm : Aut (fiber t) → H) = hf.homeomorph.symm := by
      funext a
      apply hf.bijective.1
      have h₁ : f (e₀.symm a) = a := e₀.apply_symm_apply a
      have h₂ : f (hf.homeomorph.symm a) = a := hf.homeomorph.apply_symm_apply a
      rw [h₁, h₂]
    rw [this]
    exact hf.homeomorph.symm.continuous
  have hσ' : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V),
      Continuous fun g => φ (σ' g v) := fun φ v => (hσ φ v).comp hinv
  obtain ⟨G, e, he⟩ := hM.essSurj V σ' hσ'
  refine ⟨G, e, fun h v => ?_⟩
  have := he (f h) v
  change e (M.rep t G (f h) v) = σ h (e v)
  rw [this]
  change σ (e₀.symm (e₀ h)) (e v) = σ h (e v)
  rw [MulEquiv.symm_apply_apply]

omit [TopologicalSpace H] in
/-- Along a surjective homomorphism, irreducibility of the restricted monodromy representation is
irreducibility of the monodromy representation. -/
theorem isIrreducible_comp_iff (hf : Function.Surjective f) (G : LisseSheaf l Y) :
    Representation.IsIrreducible ((M.rep t G).comp f) ↔ (M.rep t G).IsIrreducible :=
  Representation.isIrreducible_comp_iff f hf

end Transport

end AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt
