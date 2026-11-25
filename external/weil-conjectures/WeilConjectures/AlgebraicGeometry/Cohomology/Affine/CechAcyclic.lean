/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
public import WeilConjectures.CategoryTheory.Abelian.DimensionShifting

/-!
# Sheaves which are Čech-acyclic on affine opens

The class `AlgebraicGeometry.Scheme.Modules.cechAcyclicOnAffines` of abelian sheaves which are
Čech-acyclic on affine opens: it contains the quasi-coherent sheaves and the injective sheaves,
and is stable under cokernels of monomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Sheaves which are Čech-acyclic on affine opens -/

section CechAcyclic

open TopCat.Presheaf Opposite

/-- Every open covering of an affine open `V` is refined by a standard covering
`D(f₁), …, D(fₙ)` of `V` by finitely many basic opens. -/
lemma exists_basicOpen_cover_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V)
    (W : V → X.Opens) (hW : ∀ x, x.1 ∈ W x) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, V)), ⨆ i, X.basicOpen (f i) = V ∧
      ∀ i, ∃ x, X.basicOpen (f i) ≤ W x := by
  choose g hgW hxg using fun x : V ↦ hV.exists_basicOpen_le (V := W x) ⟨x.1, hW x⟩ x.2
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V ↦ (X.basicOpen (g x) : Set X))
    (fun x ↦ (X.basicOpen (g x)).isOpen) (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxg _⟩)
  have hsup : ⨆ i, X.basicOpen (g (t.equivFin.symm i).1) = V := by
    refine le_antisymm (iSup_le fun i ↦ X.basicOpen_le _) fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩
  exact ⟨t.card, fun i ↦ g (t.equivFin.symm i).1, hsup, fun i ↦ ⟨(t.equivFin.symm i).1, hgW _⟩⟩

variable (X) in
/-- The abelian sheaves on `X` whose Čech complexes on the standard coverings
`D(f₁), …, D(fₙ)` of the affine opens `V` of `X` are exact in positive degrees. Quasi-coherent
modules (`exactAt_cechComplex_basicOpen`) and injective abelian sheaves have this property. -/
def cechAcyclicOnAffines :
    ObjectProperty (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  fun F ↦ ∀ ⦃V : X.Opens⦄, IsAffineOpen V → ∀ {n : ℕ} (f : Fin n → Γ(X, V)),
    ⨆ i, X.basicOpen (f i) = V → ∀ q : ℕ,
      ((cechComplex fun i ↦ X.basicOpen (f i)).obj F.obj).ExactAt (q + 1)

/-- The underlying abelian sheaf of a quasi-coherent module is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_of_isQuasicoherent (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) :=
  fun _ hV _ f hf q ↦ exactAt_cechComplex_basicOpen ℱ hV f hf q

/-- An injective abelian sheaf is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_of_injective (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [Injective I] : cechAcyclicOnAffines X I :=
  fun _ _ _ _ _ q ↦ exactAt_cechComplex_of_injective _ I q

/-- A short exact sequence `0 → F → G → H → 0` of abelian sheaves with `F` Čech-acyclic on
affine opens is surjective on the sections over every affine open. -/
lemma surjective_app_of_cechAcyclicOnAffines
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h : cechAcyclicOnAffines X S.X₁) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (S.g.hom.app (op V)) :=
  TopCat.Sheaf.surjective_app_of_exactAt_cechComplex hS IsAffineOpen
    (fun {n} U ↦ ∃ (V : X.Opens) (_ : IsAffineOpen V) (f : Fin n → Γ(X, V)),
      U = (fun i ↦ X.basicOpen (f i)) ∧ ⨆ i, X.basicOpen (f i) = V)
    (fun V hV W hW ↦ by
      obtain ⟨n, f, hf, hfW⟩ := exists_basicOpen_cover_of_isAffineOpen hV W hW
      exact ⟨n, _, ⟨V, hV, f, rfl, hf⟩, hf, hfW⟩)
    (by
      rintro n _ ⟨V, hV, f, rfl, hf⟩
      exact h hV f hf 0) V hV

/-- In a short exact sequence `0 → F → G → H → 0` of abelian sheaves with `F` and `G`
Čech-acyclic on affine opens, `H` is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_X₃
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h₁ : cechAcyclicOnAffines X S.X₁) (h₂ : cechAcyclicOnAffines X S.X₂) :
    cechAcyclicOnAffines X S.X₃ := by
  intro V hV n f hf q
  refine exactAt_cechComplex_of_sectionwise _ S.f.hom S.g.hom TopCat.Sheaf.app_g_app_f
    (TopCat.Sheaf.injective_app_f hS) (TopCat.Sheaf.exists_app_f_eq hS) (fun k y ↦ ?_) q
    (h₁ hV f hf (q + 1)) (h₂ hV f hf q)
  refine surjective_app_of_cechAcyclicOnAffines hS h₁ ?_
  rw [Scheme.iInf_basicOpen_eq_basicOpen_prod]
  exact hV.basicOpen _

/-- Being Čech-acyclic on affine opens passes from `F` to the chosen injective sheaf under `F`
and to the cokernel of `F ⟶ I`. -/
lemma cechAcyclicOnAffines_under_cokernel
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (h : cechAcyclicOnAffines X F) :
    cechAcyclicOnAffines X (Injective.under F) ∧
      cechAcyclicOnAffines X (cokernel (Injective.ι F)) := by
  have h₂ : cechAcyclicOnAffines X (Injective.under F) :=
    cechAcyclicOnAffines_of_injective (Injective.under F)
  have hS := ObjectProperty.shortExact_injectiveShortComplex F
  have h₃ := cechAcyclicOnAffines_X₃ hS h h₂
  exact ⟨h₂, h₃⟩

end CechAcyclic

end AlgebraicGeometry.Scheme.Modules
