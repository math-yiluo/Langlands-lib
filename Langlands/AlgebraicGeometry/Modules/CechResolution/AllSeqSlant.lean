import Langlands.AlgebraicGeometry.CechSlantDescent
import Langlands.AbelianScheme.CanonicalH1Primitive
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Scalar-linear shuffle slant on actual cohomology -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Cech Cech.KunnethDetection
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}}
  {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R} {πP : P ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  [∀ W : P.Opens, Algebra R Γ(P, W)]
  (halgP : ∀ W : P.Opens, algebraMap R Γ(P, W) = (secHom πP W).hom)
  (hπ : p₁ ≫ πX = πP)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)
  (hl : ∀ y : C (ab X.presheaf) U 0, l (Cech.d (ab X.presheaf) U 0 y) = 0)

/-- The scalar-linear shuffle slant morphism on the actual ordered cochain objects. -/
def slantCochainMap (n : ℕ) :
    (cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).X (n + 1) ⟶
      (cochainComplex πY V (unitModule Y)).X n :=
  ModuleCat.ofHom
    ((cochainSecEquiv πY V halgY n).symm.toLinearMap.comp
      ((LLinearMap hP halgX halgY halgP hπ U hU l V hV n).comp
        (cochainSecEquiv πP (prodCover p₁ p₂ U V) halgP (n + 1)).toLinearMap))

lemma slantCochainMap_apply (n : ℕ)
    (c : cochain πP (prodCover p₁ p₂ U V) (unitModule P) (n + 1)) :
    (slantCochainMap hP halgX halgY halgP hπ U V hU hV l n c :
      C (ab Y.presheaf) V n) =
      L hP halgX halgY U V hU hV l n
        (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1)) := rfl

include hl

lemma slantCochainMap_anticomm (n : ℕ) :
    (cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).d (n + 1) (n + 2) ≫
        slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1) =
      -(slantCochainMap hP halgX halgY halgP hπ U V hU hV l n ≫
        (cochainComplex πY V (unitModule Y)).d n (n + 1)) := by
  rw [cochainComplex_d, cochainComplex_d]
  ext c
  have h := L_d hP halgX halgY U V hU hV l hl n
    (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1))
  rw [← dCochain_unit πP (prodCover p₁ p₂ U V) (n + 1) c,
    ← dCochain_unit πY V n
      (show cochain πY V (unitModule Y) n from L hP halgX halgY U V hU hV l n c)] at h
  exact h

lemma slantCochainMap_bottom :
    (cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).d 0 1 ≫
        slantCochainMap hP halgX halgY halgP hπ U V hU hV l 0 = 0 := by
  rw [cochainComplex_d]
  ext c
  have h := L_zero_d hP halgX halgY U V hU hV l hl
    (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) 0)
  rw [← dCochain_unit πP (prodCover p₁ p₂ U V) 0 c] at h
  exact h

/-- The shuffle slant morphism on scalar-linear ordered Čech homology. -/
def slantH (n : ℕ) :
    (cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).homology (n + 1) ⟶
      (cochainComplex πY V (unitModule Y)).homology n :=
  slantHomologyMap _ _
    (slantCochainMap hP halgX halgY halgP hπ U V hU hV l)
    (slantCochainMap_anticomm hP halgX halgY halgP hπ U V hU hV l hl)
    (slantCochainMap_bottom hP halgX halgY halgP hπ U V hU hV l hl) n

lemma slantH_π_ι (n : ℕ) :
    (cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).homologyπ (n + 1) ≫
        slantH hP halgX halgY halgP hπ U V hU hV l hl n ≫
        (cochainComplex πY V (unitModule Y)).homologyι n =
      (cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).iCycles (n + 1) ≫
        slantCochainMap hP halgX halgY halgP hπ U V hU hV l n ≫
        (cochainComplex πY V (unitModule Y)).pOpcycles n := by
  change ((cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).sc (n + 1)).homologyπ ≫
      ShortComplex.homologyMap (slantShortComplexMap _ _ _ _ _ n) ≫
      ((cochainComplex πY V (unitModule Y)).sc n).homologyι = _
  rw [ShortComplex.π_homologyMap_ι, slantShortComplexMap_τ₂]
  rfl

lemma slantCochainMap_mem_ker (n : ℕ)
    (b : LinearMap.ker
      (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) (n + 2))) :
    slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1) b.1 ∈
      LinearMap.ker (dCochain πY V (unitModule Y) (n + 1)) := by
  rw [LinearMap.mem_ker]
  have h := congrArg
    (fun f => f (b : cochain πP (prodCover p₁ p₂ U V) (unitModule P) (n + 2)))
    (slantCochainMap_anticomm hP halgX halgY halgP hπ U V hU hV l hl (n + 1))
  rw [cochainComplex_d, cochainComplex_d] at h
  change slantCochainMap hP halgX halgY halgP hπ U V hU hV l ((n + 1) + 1)
      (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) (n + 2) b.1) =
    -dCochain πY V (unitModule Y) (n + 1)
      (slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1) b.1) at h
  rw [b.2, map_zero] at h
  exact neg_eq_zero.mp h.symm

/-- Slant on a positive-degree class is represented by the shuffle slant of the cocycle. -/
lemma slantH_classMap (n : ℕ)
    (b : LinearMap.ker
      (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) (n + 2))) :
    slantH hP halgX halgY halgP hπ U V hU hV l hl (n + 1)
        (classMap πP (prodCover p₁ p₂ U V) (unitModule P) (n + 1) b) =
      classMap πY V (unitModule Y) n
        ⟨slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1) b.1,
          slantCochainMap_mem_ker hP halgX halgY halgP hπ U V hU hV l hl n b⟩ := by
  rw [classMap_apply, classMap_apply, ← ConcreteCategory.comp_apply,
    slantH, slantHomologyMap_homologyπ, ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective
    ((cochainComplex πY V (unitModule Y)).iCycles (n + 1))).1 inferInstance
  have h := congrArg (fun f =>
    f (cyclesOfKer πP (prodCover p₁ p₂ U V) (unitModule P) (n + 1) b))
    (slantCyclesMap_i _ _
      (slantCochainMap hP halgX halgY halgP hπ U V hU hV l)
      (slantCochainMap_anticomm hP halgX halgY halgP hπ U V hU hV l hl)
      (slantCochainMap_bottom hP halgX halgY halgP hπ U V hU hV l hl) (n + 1))
  simp only [ConcreteCategory.comp_apply] at h ⊢
  refine h.trans ?_
  change slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1)
      ((cochainComplex πP (prodCover p₁ p₂ U V) (unitModule P)).iCycles (n + 2)
        (cyclesOfKer πP (prodCover p₁ p₂ U V) (unitModule P) (n + 1) b)) =
    (cochainComplex πY V (unitModule Y)).iCycles (n + 1)
      (cyclesOfKer πY V (unitModule Y) n
        ⟨slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1) b.1,
          slantCochainMap_mem_ker hP halgX halgY halgP hπ U V hU hV l hl n b⟩)
  rw [cyclesOfKer_i, cyclesOfKer_i]

section Canonical

open DerivedSections

variable [IsSeparated πY] [IsSeparated πP]
  (hVtop : ⨆ j, V j = ⊤) (hVa : ∀ j, IsAffineOpen (V j))
  (hUVtop : ⨆ j, prodCover p₁ p₂ U V j = ⊤)
  (hUVa : ∀ j, IsAffineOpen (prodCover p₁ p₂ U V j))

/-- Scalar-linear shuffle slant on actual right-derived structure-sheaf cohomology. -/
def slantCanonical (n : ℕ) :
    (relativeCohomology πP (n + 1)).obj (unitModule P) →ₗ[R]
      (relativeCohomology πY n).obj (unitModule Y) :=
  (cohomologyEquiv πY V hVtop hVa n).toLinearMap.comp
    ((slantH hP halgX halgY halgP hπ U V hU hV l hl n).hom.comp
      (cohomologyEquiv πP (prodCover p₁ p₂ U V) hUVtop hUVa (n + 1)).symm.toLinearMap)

lemma slantCanonical_apply (n : ℕ)
    (x : (relativeCohomology πP (n + 1)).obj (unitModule P)) :
    slantCanonical hP halgX halgY halgP hπ U V hU hV l hl hVtop hVa hUVtop hUVa n x =
      cohomologyEquiv πY V hVtop hVa n
        (slantH hP halgX halgY halgP hπ U V hU hV l hl n
          ((cohomologyEquiv πP (prodCover p₁ p₂ U V) hUVtop hUVa (n + 1)).symm x)) := rfl

lemma slantCanonical_canonicalClass (n : ℕ)
    (b : LinearMap.ker
      (dCochain πP (prodCover p₁ p₂ U V) (unitModule P) (n + 2))) :
    slantCanonical hP halgX halgY halgP hπ U V hU hV l hl hVtop hVa hUVtop hUVa (n + 1)
        (canonicalClass πP (prodCover p₁ p₂ U V) hUVtop hUVa (n + 1) b) =
      canonicalClass πY V hVtop hVa n
        ⟨slantCochainMap hP halgX halgY halgP hπ U V hU hV l (n + 1) b.1,
          slantCochainMap_mem_ker hP halgX halgY halgP hπ U V hU hV l hl n b⟩ := by
  simp only [canonicalClass, LinearMap.comp_apply, LinearEquiv.coe_coe,
    slantCanonical_apply, LinearEquiv.symm_apply_apply]
  rw [slantH_classMap]

end Canonical

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
