/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Vector bundles and their zero sections

A *vector bundle of constant rank `c`* over a scheme `Z` is a morphism `p : E ⟶ Z` with a section
`z : Z ⟶ E` which is Zariski-locally on `Z` isomorphic to `(𝔸^c_V ⟶ V, 0)`, the coordinates of two
charts being related by linear substitutions with coefficients in `𝒪_Z`
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas`). This is the geometric vector bundle of
Hartshorne (Exercise II.5.18): the sheaf `ℰ` of fibrewise linear functions on `E` (locally spanned
by the coordinates of a chart) is locally free of rank `c` and `E ≅ Spec_Z (Sym^• ℰ)` over `Z`,
the zero section being the closed immersion defined by the augmentation `Sym^• ℰ ⟶ 𝒪_Z`, which
kills the coordinates. The pinned Mathlib has no relative `Spec` of a quasi-coherent algebra and
no symmetric algebra of a sheaf of modules, so the bundle is described through its linear charts.

The charts are taken over open immersions `v : V ⟶ Z` jointly covering `Z`, a chart being an
isomorphism `E ×_Z V ≅ 𝔸^c_V` over `V`.

A *trivialization* of `E` (`AlgebraicGeometry.Scheme.Hom.VectorBundleTrivialization`) is an étale
`Z' ⟶ Z` with an isomorphism `E ×_Z Z' ≅ 𝔸^c_{Z'}` over `Z'`; the charts of an atlas are
trivializations (`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas.exists_trivialization`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {E Z : Scheme.{u}}

namespace Scheme.Hom

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

A *linear atlas of rank `c`* of `p : E ⟶ Z` with section `z`: open immersions `vᵢ : Vᵢ ⟶ Z`
covering `Z`, with isomorphisms `φᵢ : E ×_Z Vᵢ ≅ 𝔸^c_{Vᵢ}` over `Vᵢ` carrying `z` to the zero
section, such that over `Vᵢ ×_Z Vⱼ` every coordinate of the chart `φⱼ` is a linear combination,
with coefficients in `Γ(Vᵢ ×_Z Vⱼ, 𝒪)`, of the coordinates of `φᵢ`. -/
structure VectorBundleAtlas (c : ℕ) (p : E ⟶ Z) (z : Z ⟶ E) where
  /-- The index set of the charts. -/
  ι : Type u
  /-- The opens of `Z` over which the bundle is trivialized. -/
  V : ι → Scheme.{u}
  /-- The open immersions `Vᵢ ⟶ Z`. -/
  v (i : ι) : V i ⟶ Z
  isOpenImmersion (i : ι) : IsOpenImmersion (v i)
  exists_mem_range (x : Z) : ∃ i, x ∈ Set.range (v i).base
  /-- The charts `E ×_Z Vᵢ ≅ 𝔸^c_{Vᵢ}`. -/
  chart (i : ι) : pullback p (v i) ≅ 𝔸(ULift.{u} (Fin c); V i)
  chart_hom_over (i : ι) : (chart i).hom ≫ 𝔸(ULift.{u} (Fin c); V i) ↘ V i = pullback.snd p (v i)
  /-- In the charts the section `z` is the zero section, defined by the augmentation. -/
  zeroSection_chart (i : ι) : ∃ σ : V i ⟶ pullback p (v i), σ ≫ pullback.fst p (v i) = v i ≫ z ∧
    σ ≫ pullback.snd p (v i) = 𝟙 _ ∧
      σ ≫ (chart i).hom = AffineSpace.zeroSection (ULift.{u} (Fin c)) (V i)
  /-- The transition functions are linear: locally on `Vᵢ ×_Z Vⱼ`, each coordinate of `φⱼ` is a
  linear combination of the coordinates of `φᵢ`. -/
  linear (i j : ι) (k : Fin c) (y : ↥(pullback (v i) (v j))) :
    ∃ (U : (pullback (v i) (v j)).Opens) (_ : y ∈ U) (a : Fin c → Γ(pullback (v i) (v j), U)),
      (pullback p (pullback.fst (v i) (v j) ≫ v i)).presheaf.map (homOfLE le_top).op
      ((pullback.map p (pullback.fst (v i) (v j) ≫ v i) p (v j) (𝟙 E) (pullback.snd (v i) (v j))
        (𝟙 Z) (by simp) (by simp [pullback.condition])).appTop
        ((chart j).hom.appTop (AffineSpace.coord (V j) (ULift.up k)))) =
      ∑ l, (pullback.snd p (pullback.fst (v i) (v j) ≫ v i)).app U (a l) *
        (pullback p (pullback.fst (v i) (v j) ≫ v i)).presheaf.map (homOfLE le_top).op
          ((pullback.map p (pullback.fst (v i) (v j) ≫ v i) p (v i) (𝟙 E)
            (pullback.fst (v i) (v j)) (𝟙 Z) (by simp) (by simp)).appTop
            ((chart i).hom.appTop (AffineSpace.coord (V i) (ULift.up l))))

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

`p : E ⟶ Z` is a *vector bundle of constant rank `c`* with *zero section* `z` if `z` is a section
of `p` and a closed immersion, and `(p, z)` admits a linear atlas of rank `c`
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas`): Zariski-locally on `Z`, `(E, z)` is
`(𝔸^c, 0)` with linear transition functions, i.e. `E ≅ Spec_Z (Sym^• ℰ)` for the locally free
sheaf `ℰ` of rank `c` of fibrewise linear functions, `z` being given by the augmentation. -/
structure IsVectorBundle (c : ℕ) (p : E ⟶ Z) (z : Z ⟶ E) : Prop where
  zeroSection_comp : z ≫ p = 𝟙 Z
  isClosedImmersion_zeroSection : IsClosedImmersion z
  nonempty_atlas : Nonempty (VectorBundleAtlas c p z)

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

A *trivialization* of `p : E ⟶ Z`: an étale open `v : Z' ⟶ Z` together with an isomorphism
`E ×_Z Z' ≅ 𝔸^c_{Z'}` over `Z'`. -/
structure VectorBundleTrivialization (c : ℕ) (p : E ⟶ Z) where
  /-- The étale open `Z'`. -/
  base : Scheme.{u}
  /-- The étale morphism `Z' ⟶ Z`. -/
  map : base ⟶ Z
  etale_map : Etale map
  /-- The isomorphism `E ×_Z Z' ≅ 𝔸^c_{Z'}`. -/
  iso : pullback p map ≅ 𝔸(ULift.{u} (Fin c); base)
  iso_hom_over : iso.hom ≫ 𝔸(ULift.{u} (Fin c); base) ↘ base = pullback.snd p map

namespace VectorBundleAtlas

variable {c : ℕ} {p : E ⟶ Z} {z : Z ⟶ E}

/-- A chart of an atlas, as a trivialization over the open immersion `Vᵢ ⟶ Z`. -/
noncomputable def trivialization (A : VectorBundleAtlas c p z) (i : A.ι) :
    VectorBundleTrivialization c p where
  base := A.V i
  map := A.v i
  etale_map := have := A.isOpenImmersion i; inferInstance
  iso := A.chart i
  iso_hom_over := A.chart_hom_over i

/-- Every point of `Z` lies in the image of a trivialization coming from the atlas. -/
lemma exists_trivialization (A : VectorBundleAtlas c p z) (x : Z) :
    ∃ τ : VectorBundleTrivialization c p, x ∈ Set.range τ.map := by
  obtain ⟨i, hi⟩ := A.exists_mem_range x
  exact ⟨A.trivialization i, hi⟩

end VectorBundleAtlas

end Scheme.Hom

end AlgebraicGeometry
