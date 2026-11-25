/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularProjective
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar

/-!
# Restriction of scalars along a quotient by a nonzerodivisor

Let `C` be a closed symmetric monoidal abelian category whose unit is projective, `R ⟶ S` a
morphism `φ` of commutative algebra objects and `k` an integer such that
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, i.e. `S = R ⧸ k`. Then restriction of scalars
along `φ` sends finitely presented `S`-modules to finitely presented `R`-modules
(`CategoryTheory.Mod.IsFinitelyPresented.comap_of_shortExact`).

If `N = coker (f : Sᵐ ⟶ Sⁿ)`, the restriction of scalars of `Sʲ` is the cokernel of `k` on `Rʲ`
(`CategoryTheory.Mod.finiteFreeReduction`), and, `Rᵐ` being projective, the composite
`Rᵐ ⟶ Sᵐ ⟶ Sⁿ` lifts to `g : Rᵐ ⟶ Rⁿ`. Then `N` is, as an `R`-module, the cokernel of
`(g, k) : Rᵐ ⊕ Rⁿ ⟶ Rⁿ` (`CategoryTheory.Limits.isColimitCokernelCoforkOfLift`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Limits

variable {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜]

/-- **Cokernels of lifts.** Let `πQ : Q ⟶ Q'` be a cokernel of `a : Q₀ ⟶ Q`, `πP : P ⟶ P'` an
epimorphism, `c : Q' ⟶ T` a cokernel of `f' : P' ⟶ Q'`, and `g : P ⟶ Q` a lift of `f'`, i.e.
`g ≫ πQ = πP ≫ f'`. If `G : Z ⟶ Q` is a morphism such that `G ≫ h = 0` iff `g ≫ h = 0` and
`a ≫ h = 0` (e.g. `G = (g, a)`), then `πQ ≫ c` is a cokernel of `G`. -/
noncomputable def isColimitCokernelCoforkOfLift {P P' Q₀ Q Q' T Z : 𝒜} (πP : P ⟶ P') [Epi πP]
    (a : Q₀ ⟶ Q) (πQ : Q ⟶ Q') [Epi πQ]
    (hπQ : ∀ {W : 𝒜} (h : Q ⟶ W), a ≫ h = 0 → ∃ h' : Q' ⟶ W, πQ ≫ h' = h)
    (f' : P' ⟶ Q') (c : Q' ⟶ T) [Epi c]
    (hc : ∀ {W : 𝒜} (h : Q' ⟶ W), f' ≫ h = 0 → ∃ h' : T ⟶ W, c ≫ h' = h)
    (wc : f' ≫ c = 0) (wQ : a ≫ πQ = 0)
    (g : P ⟶ Q) (hg : g ≫ πQ = πP ≫ f') (G : Z ⟶ Q)
    (hG : ∀ {W : 𝒜} (h : Q ⟶ W), G ≫ h = 0 ↔ g ≫ h = 0 ∧ a ≫ h = 0) :
    IsColimit (CokernelCofork.ofπ (f := G) (πQ ≫ c)
      ((hG _).2 ⟨by rw [reassoc_of% hg, wc, Limits.comp_zero], by rw [reassoc_of% wQ,
        Limits.zero_comp]⟩)) := by
  have key {W : 𝒜} (h : Q ⟶ W) (hh : G ≫ h = 0) : ∃ h'' : T ⟶ W, (πQ ≫ c) ≫ h'' = h := by
    obtain ⟨hg', ha⟩ := (hG h).1 hh
    obtain ⟨h', rfl⟩ := hπQ h ha
    obtain ⟨h'', rfl⟩ := hc h' (by
      rw [← cancel_epi πP, Limits.comp_zero, ← Category.assoc, ← hg, Category.assoc, hg'])
    exact ⟨h'', Category.assoc _ _ _⟩
  refine CokernelCofork.IsColimit.ofπ _ _ (fun h hh ↦ (key h hh).choose)
    (fun h hh ↦ (key h hh).choose_spec) (fun h hh m hm ↦ ?_)
  rw [← cancel_epi (πQ ≫ c), hm, (key h hh).choose_spec]

/-- A biproduct of projective objects, indexed by a type of any universe, is projective. -/
lemma projective_biproduct {β : Type*} (g : β → 𝒜) [HasBiproduct g] [∀ b, Projective (g b)] :
    Projective (⨁ g) where
  factors f e _ := ⟨biproduct.desc fun b ↦ Projective.factorThru (biproduct.ι g b ≫ f) e,
    by cat_disch⟩

end CategoryTheory.Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The reduction `Rʲ ⟶ Sʲ` of free modules along `φ : R ⟶ S`, as a map of `R`-modules: the unit
`Rʲ ⟶ S ⊗_R Rʲ` followed by `S ⊗_R Rʲ ≅ Sʲ`. -/
noncomputable def finiteFreeReduction (j : ℕ) :
    finiteFree R j ⟶ (comap φ).obj (finiteFree S j) :=
  extendUnit φ (finiteFree R j) ≫
    (comap φ).map (finiteFreeIsoMap (extendScalars φ) (extendScalarsObjRegularIso φ) j).hom

variable {φ}

/-- If `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, the reduction `Rʲ ⟶ Sʲ` is an epimorphism
and every map out of `Rʲ` killing `k` factors through it: `Sʲ = Rʲ ⧸ k`. -/
lemma finiteFreeReduction_cokernel (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (j : ℕ) :
    Epi (finiteFreeReduction φ j) ∧ (k • 𝟙 (finiteFree R j)) ≫ finiteFreeReduction φ j = 0 ∧
      ∀ {W : Mod C R} (h : finiteFree R j ⟶ W), (k • 𝟙 (finiteFree R j)) ≫ h = 0 →
        ∃ h' : (comap φ).obj (finiteFree S j) ⟶ W, finiteFreeReduction φ j ≫ h' = h := by
  obtain ⟨hex, _⟩ := exact_extendUnit k w hφ (finiteFree R j)
  refine ⟨epi_comp _ _, ?_, fun h hh ↦ ?_⟩
  · rw [finiteFreeReduction, ← Category.assoc, zsmul_comp_extendUnit k w, Limits.zero_comp]
  · let hc := hex.gIsCokernel
    refine ⟨(comap φ).map (finiteFreeIsoMap (extendScalars φ)
      (extendScalarsObjRegularIso φ) j).inv ≫ hc.desc (CokernelCofork.ofπ h hh), ?_⟩
    rw [finiteFreeReduction, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact hc.fac (CokernelCofork.ofπ h hh) WalkingParallelPair.one

/-- **Restriction of scalars along a quotient by a nonzerodivisor preserves finite
presentation.** If the unit of `C` is projective and `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short
exact, the restriction of scalars of a finitely presented `S`-module `N = coker (f : Sᵐ ⟶ Sⁿ)`
is the cokernel of `(g, k) : R^{m + n} ⟶ Rⁿ`, where `g : Rᵐ ⟶ Rⁿ` lifts `f`. -/
theorem IsFinitelyPresented.comap_of_shortExact [Projective (𝟙_ C)] (k : ℤ)
    (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact) {N : Mod C S}
    (h : IsFinitelyPresented S N) : IsFinitelyPresented R ((Mod.comap φ).obj N) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := h
  have : Projective (regular R) := projective_regular
  have : Projective (finiteFree R m) := projective_biproduct _
  obtain ⟨hm, -, -⟩ := finiteFreeReduction_cokernel k w hφ m
  obtain ⟨hn, wn, hfn⟩ := finiteFreeReduction_cokernel k w hφ n
  obtain ⟨g, hg⟩ := Projective.factors (finiteFreeReduction φ m ≫ (Mod.comap φ).map f)
    (finiteFreeReduction φ n)
  let G : finiteFree R (m + n) ⟶ finiteFree R n := biproduct.desc
    (Fin.addCases (motive := fun _ ↦ regular R ⟶ finiteFree R n)
      (fun i ↦ biproduct.ι (fun _ : Fin m ↦ regular R) i ≫ g)
      (fun i ↦ biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ (k • 𝟙 (finiteFree R n))))
  have hG {W : Mod C R} (h : finiteFree R n ⟶ W) :
      G ≫ h = 0 ↔ g ≫ h = 0 ∧ (k • 𝟙 (finiteFree R n)) ≫ h = 0 := by
    constructor
    · intro hh
      refine ⟨biproduct.hom_ext' _ _ fun i ↦ ?_, biproduct.hom_ext' _ _ fun i ↦ ?_⟩
      · have := biproduct.ι _ (Fin.castAdd n i) ≫= hh
        simpa [G] using this
      · have := biproduct.ι _ (Fin.natAdd m i) ≫= hh
        simpa [G] using this
    · rintro ⟨h₁, h₂⟩
      refine biproduct.hom_ext' _ _ fun i ↦ ?_
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
      · simp [G, h₁]
      · have h₂' : k • h = 0 := by simpa using h₂
        simp [G, ← Preadditive.comp_zsmul, h₂']
  have hc := isColimitOfHasCokernelOfPreservesColimit (Mod.comap φ) f
  have : Epi ((Mod.comap φ).map (cokernel.π f)) := Functor.map_epi _ _
  refine ⟨n, m + n, G, ⟨(Mod.comap φ).mapIso e ≪≫ IsColimit.coconePointUniqueUpToIso
    (isColimitCokernelCoforkOfLift (finiteFreeReduction φ m) (k • 𝟙 (finiteFree R n))
      (finiteFreeReduction φ n) hfn ((Mod.comap φ).map f) ((Mod.comap φ).map (cokernel.π f))
      (fun h hh ↦ ⟨hc.desc (CokernelCofork.ofπ h hh),
        hc.fac (CokernelCofork.ofπ h hh) WalkingParallelPair.one⟩)
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]) wn g hg G hG)
    (colimit.isColimit _)⟩⟩

end CategoryTheory.Mod
