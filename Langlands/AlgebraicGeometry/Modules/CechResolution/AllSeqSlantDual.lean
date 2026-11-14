import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqSlant
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Shuffle slant from an actual degree-one cohomology dual -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open DerivedSections

section Extension

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of K))
  {ι : Type u} [Fintype ι] (U : ι → X.Opens) (M : X.Modules)

/-- A chosen linear extension of the positive-degree cocycle class map to all cochains. -/
def cochainClassExtension (n : ℕ) :
    cochain π U M (n + 1) →ₗ[K] (cochainComplex π U M).homology (n + 1) :=
  (classMap π U M n).comp
    (LinearMap.ker (dCochain π U M (n + 1))).subtype.leftInverse

lemma cochainClassExtension_cocycle (n : ℕ)
    (z : LinearMap.ker (dCochain π U M (n + 1))) :
    cochainClassExtension π U M n z.1 = classMap π U M n z := by
  simp only [cochainClassExtension, LinearMap.comp_apply]
  congr 1
  exact LinearMap.leftInverse_apply_of_inj (Submodule.ker_subtype _) z

lemma cochainClassExtension_dCochain (n : ℕ) (c : cochain π U M n) :
    cochainClassExtension π U M n (dCochain π U M n c) = 0 := by
  have hc : dCochain π U M n c ∈ LinearMap.ker (dCochain π U M (n + 1)) := by
    have h := LinearMap.congr_fun (dCochain_comp_dCochain π U M n) c
    exact h
  rw [cochainClassExtension_cocycle π U M n ⟨_, hc⟩]
  exact (classMap_eq_zero_iff π U M n ⟨_, hc⟩).2 ⟨c, rfl⟩

end Extension

section CanonicalExtension

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of K))
  [IsSeparated π] {ι : Type u} [Fintype ι] (U : ι → X.Opens)
  (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))

/-- The chosen cochain-class extension transported to actual structure-sheaf cohomology. -/
def canonicalClassExtension (n : ℕ) :
    cochain π U (unitModule X) (n + 1) →ₗ[K]
      (relativeCohomology π (n + 1)).obj (unitModule X) :=
  (cohomologyEquiv π U hU hUa (n + 1)).toLinearMap.comp
    (cochainClassExtension π U (unitModule X) n)

lemma canonicalClassExtension_cocycle (n : ℕ)
    (z : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    canonicalClassExtension π U hU hUa n z.1 = canonicalClass π U hU hUa n z := by
  change cohomologyEquiv π U hU hUa (n + 1)
    (cochainClassExtension π U (unitModule X) n z.1) =
      cohomologyEquiv π U hU hUa (n + 1) (classMap π U (unitModule X) n z)
  rw [cochainClassExtension_cocycle]

lemma canonicalClassExtension_dCochain (n : ℕ) (c : cochain π U (unitModule X) n) :
    canonicalClassExtension π U hU hUa n (dCochain π U (unitModule X) n c) = 0 := by
  change cohomologyEquiv π U hU hUa (n + 1)
    (cochainClassExtension π U (unitModule X) n (dCochain π U (unitModule X) n c)) = 0
  rw [cochainClassExtension_dCochain]
  exact map_zero _

variable [∀ W : X.Opens, Algebra (CommRingCat.of K) Γ(X, W)]
  (halg : ∀ W : X.Opens, algebraMap (CommRingCat.of K) Γ(X, W) = (secHom π W).hom)

/-- An actual H1 dual extended to all raw one-cochains, using the fixed cocycle retraction. -/
def h1DualCochainFunctional :
    ((relativeCohomology π 1).obj (unitModule X) →ₗ[K] K) →ₗ[K]
      ((∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[K] K) where
  toFun ell := ell.comp ((canonicalClassExtension π U hU hUa 0).comp
    (cochainSecEquiv π U halg 1).symm.toLinearMap)
  map_add' _ _ := by ext c; rfl
  map_smul' _ _ := by ext c; rfl

lemma h1DualCochainFunctional_cocycle
    (ell : (relativeCohomology π 1).obj (unitModule X) →ₗ[K] K)
    (z : LinearMap.ker (dCochain π U (unitModule X) 1)) :
    h1DualCochainFunctional π U hU hUa halg ell
        (cochainSecEquiv π U halg 1 z.1) =
      ell (canonicalClass π U hU hUa 0 z) := by
  change ell (canonicalClassExtension π U hU hUa 0 z.1) = _
  rw [canonicalClassExtension_cocycle]

lemma h1DualCochainFunctional_d
    (ell : (relativeCohomology π 1).obj (unitModule X) →ₗ[K] K)
    (c : C (ab X.presheaf) U 0) :
    h1DualCochainFunctional π U hU hUa halg ell (Cech.d (ab X.presheaf) U 0 c) = 0 := by
  change ell (canonicalClassExtension π U hU hUa 0
    (show cochain π U (unitModule X) 1 from Cech.d (ab X.presheaf) U 0 c)) = 0
  rw [← dCochain_unit π U 0 (show cochain π U (unitModule X) 0 from c),
    canonicalClassExtension_dCochain, map_zero]

end CanonicalExtension

section SlantByDual

variable {K : Type u} [Field K] {X Y P : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of K)} {πY : Y ⟶ Spec (CommRingCat.of K)}
  {πP : P ⟶ Spec (CommRingCat.of K)}
  [IsSeparated πX] [IsSeparated πY] [IsSeparated πP]
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra (CommRingCat.of K) Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap (CommRingCat.of K) Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra (CommRingCat.of K) Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap (CommRingCat.of K) Γ(Y, W) = (secHom πY W).hom)
  [∀ W : P.Opens, Algebra (CommRingCat.of K) Γ(P, W)]
  (halgP : ∀ W : P.Opens, algebraMap (CommRingCat.of K) Γ(P, W) = (secHom πP W).hom)
  (hπ : p₁ ≫ πX = πP)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.Opens) (V : κ → Y.Opens)
  (hUtop : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (hVtop : ⨆ j, V j = ⊤) (hVa : ∀ j, IsAffineOpen (V j))
  (hUVtop : ⨆ j, prodCover p₁ p₂ U V j = ⊤)
  (hUVa : ∀ j, IsAffineOpen (prodCover p₁ p₂ U V j))
  (ell : (relativeCohomology πX 1).obj (unitModule X) →ₗ[K] K)

/-- Shuffle slant on actual cohomology from an arbitrary actual first-factor H1 dual. -/
def slantByH1Dual (n : ℕ) :
    (relativeCohomology πP (n + 1)).obj (unitModule P) →ₗ[K]
      (relativeCohomology πY n).obj (unitModule Y) :=
  slantCanonical hP halgX halgY halgP hπ U V hU hV
    (h1DualCochainFunctional πX U hUtop hUa halgX ell)
    (h1DualCochainFunctional_d πX U hUtop hUa halgX ell)
    hVtop hVa hUVtop hUVa n

end SlantByDual

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
