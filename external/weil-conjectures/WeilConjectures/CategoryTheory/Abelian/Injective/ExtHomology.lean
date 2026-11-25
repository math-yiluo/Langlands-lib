/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Injective.ExtMap
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# `Ext` as the homology of a complex of modules

Let `R` be an injective resolution of `Y`, and `S` a short complex of modules identified, through
additive equivalences `(X ⟶ Rⁿ) ≃ S.X₂` and `(X ⟶ Rⁿ⁺¹) ≃ S.X₃`, with the degree-`n` piece of
the complex `Hom(X, R)`, the boundaries corresponding to the coboundaries. Then
`Ext X Y n ≃ H(S)` (`CategoryTheory.InjectiveResolution.extAddEquivHomology`), the class of a
cocycle `f` corresponding to the homology class of `f`.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Abelian Limits

namespace CategoryTheory.ShortComplex

variable {A : Type u'} [Ring A] (S : ShortComplex (ModuleCat.{v'} A))

/-- An element of the cycles of a short complex of modules vanishes in homology if and only if
it is a boundary. -/
lemma moduleCat_homologyπ_eq_zero_iff (c : S.cycles) :
    S.homologyπ c = 0 ↔ ∃ x : S.X₁, S.f x = S.iCycles c := by
  have hc : (S.moduleCatCyclesIso.hom c).1 = S.iCycles c :=
    S.moduleCatCyclesIso_hom_i_apply c
  have h₁ := ConcreteCategory.congr_hom S.π_moduleCatCyclesIso_hom c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₁
  constructor
  · intro h
    rw [h, map_zero] at h₁
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 h₁.symm
    refine ⟨x, ?_⟩
    have := congrArg Subtype.val hx
    rw [hc] at this
    exact this
  · rintro ⟨x, hx⟩
    apply (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).1 inferInstance
    rw [h₁, map_zero]
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨x, Subtype.ext ?_⟩
    rw [hc]
    exact hx

/-- An element of a module in a short complex of modules which is killed by `g` is a cycle. -/
lemma moduleCat_exists_iCycles (y : S.X₂) (hy : S.g y = 0) : ∃ c : S.cycles, S.iCycles c = y :=
  ⟨S.moduleCatCyclesIso.inv ⟨y, hy⟩, S.moduleCatCyclesIso_inv_iCycles_apply _⟩

end CategoryTheory.ShortComplex

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y) {A : Type u'} [Ring A] {n : ℕ} (S : ShortComplex (ModuleCat.{v'} A))
  (e₂ : (X ⟶ R.cocomplex.X n) ≃+ S.X₂) (e₃ : (X ⟶ R.cocomplex.X (n + 1)) ≃+ S.X₃)

omit [HasExt C] in
lemma cocycle_of_g_eq_zero (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (f : X ⟶ R.cocomplex.X n) (hf : S.g (e₂ f) = 0) :
    f ≫ R.cocomplex.d n (n + 1) = 0 :=
  e₃.injective (by rw [← hg, hf, map_zero])

omit [HasExt C] in
lemma g_eq_zero_of_cocycle (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    S.g (e₂ f) = 0 := by
  rw [hg, hf, map_zero]

variable {R S e₂ e₃} in
lemma homologyπ_eq_of_extMk_eq
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f)
    {f f' : X ⟶ R.cocomplex.X n} (hf : f ≫ R.cocomplex.d n (n + 1) = 0)
    (hf' : f' ≫ R.cocomplex.d n (n + 1) = 0)
    (h : R.extMk f (n + 1) rfl hf = R.extMk f' (n + 1) rfl hf') {c c' : S.cycles}
    (hc : S.iCycles c = e₂ f) (hc' : S.iCycles c' = e₂ f') :
    S.homologyπ c = S.homologyπ c' := by
  rw [← sub_eq_zero, sub_extMk, hbd] at h
  obtain ⟨x, hx⟩ := h
  rw [← sub_eq_zero, ← map_sub, S.moduleCat_homologyπ_eq_zero_iff, map_sub, hc, hc']
  exact ⟨x, by rw [hx, map_sub]⟩

/-- The map `Ext X Y n ⟶ H(S)` sending the class of a cocycle `f` to the homology class of
`e₂ f`, as a function. -/
noncomputable def extToHomologyFun (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (x : Ext X Y n) : S.homology :=
  S.homologyπ (S.moduleCat_exists_iCycles (e₂ (R.extMk_surjective x (n + 1) rfl).choose)
    (g_eq_zero_of_cocycle R S e₂ e₃ hg _
      (R.extMk_surjective x (n + 1) rfl).choose_spec.choose)).choose

lemma extToHomologyFun_extMk (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f)
    (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) (c : S.cycles)
    (hc : S.iCycles c = e₂ f) :
    extToHomologyFun R S e₂ e₃ hg (R.extMk f (n + 1) rfl hf) = S.homologyπ c :=
  homologyπ_eq_of_extMk_eq hbd _ _ (R.extMk_surjective _ (n + 1) rfl).choose_spec.choose_spec
    (S.moduleCat_exists_iCycles _ (g_eq_zero_of_cocycle R S e₂ e₃ hg _
      (R.extMk_surjective _ (n + 1) rfl).choose_spec.choose)).choose_spec hc

/-- **`Ext` as homology.** The class of a cocycle `f` is sent to the homology class of `e₂ f`. -/
noncomputable def extToHomology (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f) :
    Ext X Y n →+ S.homology :=
  AddMonoidHom.mk' (extToHomologyFun R S e₂ e₃ hg) fun x y ↦ by
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
    obtain ⟨g, hg', rfl⟩ := R.extMk_surjective y (n + 1) rfl
    obtain ⟨c, hc⟩ := S.moduleCat_exists_iCycles (e₂ f) (g_eq_zero_of_cocycle R S e₂ e₃ hg _ hf)
    obtain ⟨c', hc'⟩ := S.moduleCat_exists_iCycles (e₂ g)
      (g_eq_zero_of_cocycle R S e₂ e₃ hg _ hg')
    rw [add_extMk, extToHomologyFun_extMk R S e₂ e₃ hg hbd _ _ (c + c')
        (by rw [map_add, hc, hc', map_add]),
      extToHomologyFun_extMk R S e₂ e₃ hg hbd _ _ c hc,
      extToHomologyFun_extMk R S e₂ e₃ hg hbd _ _ c' hc', map_add]

lemma extToHomology_extMk (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f)
    (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) (c : S.cycles)
    (hc : S.iCycles c = e₂ f) :
    extToHomology R S e₂ e₃ hg hbd (R.extMk f (n + 1) rfl hf) = S.homologyπ c :=
  extToHomologyFun_extMk R S e₂ e₃ hg hbd f hf c hc

lemma extToHomology_bijective (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f) :
    Function.Bijective (extToHomology R S e₂ e₃ hg hbd) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
    obtain ⟨c, hc⟩ := S.moduleCat_exists_iCycles (e₂ f) (g_eq_zero_of_cocycle R S e₂ e₃ hg _ hf)
    rw [extToHomology_extMk R S e₂ e₃ hg hbd f hf c hc, S.moduleCat_homologyπ_eq_zero_iff,
      hc] at hx
    exact (hbd f hf).2 hx
  · obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance h
    have hy : S.g (e₂ (e₂.symm (S.iCycles c))) = 0 := by
      rw [AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply, S.iCycles_g]
      rfl
    exact ⟨_, extToHomology_extMk R S e₂ e₃ hg hbd _ (cocycle_of_g_eq_zero R S e₂ e₃ hg _ hy) c
      (e₂.apply_symm_apply _).symm⟩

/-- **`Ext` as homology.** `Ext X Y n ≃ H(S)`, the class of a cocycle `f` corresponding to the
homology class of `e₂ f`. -/
noncomputable def extAddEquivHomology (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f) :
    Ext X Y n ≃+ S.homology :=
  AddEquiv.ofBijective _ (extToHomology_bijective R S e₂ e₃ hg hbd)

lemma extAddEquivHomology_extMk (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f)
    (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) (c : S.cycles)
    (hc : S.iCycles c = e₂ f) :
    extAddEquivHomology R S e₂ e₃ hg hbd (R.extMk f (n + 1) rfl hf) = S.homologyπ c :=
  extToHomology_extMk R S e₂ e₃ hg hbd f hf c hc

variable {R S e₂ e₃} {X' Y' : C} {R' : InjectiveResolution Y'}
  {S' : ShortComplex (ModuleCat.{v'} A)}
  {e₂' : (X' ⟶ R'.cocomplex.X n) ≃+ S'.X₂} {e₃' : (X' ⟶ R'.cocomplex.X (n + 1)) ≃+ S'.X₃}

/-- **Naturality of `Ext` as homology.** A map of cocycles `Φ` corresponding to a morphism of
short complexes `φ` induces on `Ext` the map induced by `φ` on homology. -/
lemma extAddEquivHomology_extMap
    (hg : ∀ f, S.g (e₂ f) = e₃ (f ≫ R.cocomplex.d n (n + 1)))
    (hbd : ∀ f (hf : f ≫ R.cocomplex.d n (n + 1) = 0),
      R.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S.X₁, S.f x = e₂ f)
    (hg' : ∀ f, S'.g (e₂' f) = e₃' (f ≫ R'.cocomplex.d n (n + 1)))
    (hbd' : ∀ f (hf : f ≫ R'.cocomplex.d n (n + 1) = 0),
      R'.extMk f (n + 1) rfl hf = 0 ↔ ∃ x : S'.X₁, S'.f x = e₂' f)
    (Φ : ∀ n, (X ⟶ R.cocomplex.X n) →+ (X' ⟶ R'.cocomplex.X n))
    (hΦ : ∀ n m (f : X ⟶ R.cocomplex.X n),
      Φ m (f ≫ R.cocomplex.d n m) = Φ n f ≫ R'.cocomplex.d n m)
    (φ : S ⟶ S') (hφ : ∀ f, φ.τ₂ (e₂ f) = e₂' (Φ n f)) (x : Ext X Y n) :
    extAddEquivHomology R' S' e₂' e₃' hg' hbd' (extMap R' Φ hΦ n x) =
      ShortComplex.homologyMap φ (extAddEquivHomology R S e₂ e₃ hg hbd x) := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  obtain ⟨c, hc⟩ := S.moduleCat_exists_iCycles (e₂ f) (g_eq_zero_of_cocycle R S e₂ e₃ hg _ hf)
  have h₁ := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) c
  have h₂ := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) c
  simp only [ConcreteCategory.comp_apply] at h₁ h₂
  rw [extMap_extMk, extAddEquivHomology_extMk R S e₂ e₃ hg hbd f hf c hc,
    extAddEquivHomology_extMk R' S' e₂' e₃' hg' hbd' _ _ (ShortComplex.cyclesMap φ c)
      (by rw [h₁, hc, hφ]), h₂]

end CategoryTheory.InjectiveResolution
