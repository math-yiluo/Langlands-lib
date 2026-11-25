/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatDescentChart
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.AffineOpenDirectedRingSystem
import WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange

/-!
# Tensor-spectrum comparisons for one affine triple

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph.
(blueprint: lem-weil-pbc-flat-descent-chart-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- One affine triple admits a ring diagram whose tensor spectra identify the restricted
base changes at every stage and at the limit. The stage source open is exactly the inverse
image of the given source open. No flatness hypothesis or conclusion occurs here.

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph, and Situation 081D;
the affine limit comparison is Tag 01YW.
(blueprint: lem-weil-pbc-flat-descent-chart-comparison).

Proof: For j in the upper tail, take W_j to be the inverse image of W₀ in D(j).
Affine transition morphisms make each W_j affine. Their section rings and the section
maps of the restricted transitions form the covariant ring diagram. Identify W at the
limit with Spec of its colimit by the affine-open limit theorem and uniqueness of limits.
At the initial stage identify the section ring of the inverse image along the identity
transition with Γ(W₀), using D.map_id. Take B = Γ(V₀.toScheme, ⊤) and C = Γ(U₀.toScheme, ⊤), and put
f = f₀.resLE V₀ U₀ hUV. The base map to B is induced by the composite
V₀ → W₀ → Spec(F(j₀)); the base map to C is its composite with f.appTop.
The algebra map is f.appTop, so compatibility holds by construction. Local finite
presentation is preserved by restriction and its affine criterion gives finite
presentation of f.appTop. Naturality of isoSpec and the Γ-Spec triangle identity
give the two required compatibility equations.
For q a transition or the limit projection, choose U and V to be the inverse images
of U₀ and V₀ under the pullback first projections. The pullback square and the two
containments show that these opens are U₀ ×_{W₀} q⁻¹(W₀) and
V₀ ×_{W₀} q⁻¹(W₀). Open pullback comparison and pullbackSpecIso identify them
with Spec(R ⊗ Γ(U₀)) and Spec(R ⊗ Γ(V₀)), respectively, swapping the tensor factors
if needed. The restricted morphism becomes Spec(id ⊗ f₀.appLE): both maps into
the target pullback have the same components, so pullback.hom_ext proves equality.
These source and target isomorphisms together give the asserted arrow isomorphism.
This construction also works for an empty source open (its section ring is the zero
ring), a zero base ring, and a preorder with a single stage. It uses neither flatness
nor the eventual flatness theorem. -/
theorem exists_flat_descent_chart_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFinitePresentation f₀.left]
    (W₀ : (D.obj (op i₀)).Opens) (V₀ : Y₀.left.Opens) (U₀ : X₀.left.Opens)
    (hW : IsAffineOpen W₀) (hV : IsAffineOpen V₀) (hU : IsAffineOpen U₀)
    (hVW : V₀ ≤ Y₀.hom ⁻¹ᵁ W₀) (hUV : U₀ ≤ f₀.left ⁻¹ᵁ V₀) :
    ∃ a : FlatDescentChart {i : I // i₀ ≤ i} ⟨i₀, le_rfl⟩,
      letI := a.sourceAlgebra
      letI := a.targetAlgebra
      (∀ j : {i : I // i₀ ≤ i},
        let q := D.map (homOfLE j.property).op
        let F := ((Over.pullback q).map f₀).left
        let R := a.rings.obj j
        letI := (a.rings.map (homOfLE (show (⟨i₀, le_rfl⟩ : {i : I // i₀ ≤ i}) ≤ j
          from j.property))).hom.toAlgebra
        ∃ (V : ((Over.pullback q).obj Y₀).left.Opens)
          (U : ((Over.pullback q).obj X₀).left.Opens) (h : U ≤ F ⁻¹ᵁ V),
          U = (pullback.fst X₀.hom q) ⁻¹ᵁ U₀ ∧
          Nonempty (Arrow.mk (F.resLE V U h) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom)))) ∧
      (let q := c.π.app (op i₀)
        let F := ((Over.pullback q).map f₀).left
        let R := colimit a.rings
        letI := (colimit.ι a.rings ⟨i₀, le_rfl⟩).hom.toAlgebra
        ∃ (V : ((Over.pullback q).obj Y₀).left.Opens)
          (U : ((Over.pullback q).obj X₀).left.Opens) (h : U ≤ F ⁻¹ᵁ V),
          Nonempty (Arrow.mk (F.resLE V U h) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom)))) := by
  classical
  obtain ⟨F, e0, hi, eL, hL⟩ := exists_affineOpen_ringSystem_of_isLimit D c hc i₀ W₀ hW
  let R := F.obj ⟨i₀, le_rfl⟩
  let B := Γ(V₀.toScheme, ⊤)
  let C := Γ(U₀.toScheme, ⊤)
  let : IsAffine V₀.toScheme := hV
  let : IsAffine U₀.toScheme := hU
  let f := f₀.left.resLE V₀ U₀ hUV
  let q := Y₀.hom.resLE W₀ V₀ hVW ≫ e0.hom
  let aB : R →+* B := ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
  let aC : R →+* C := f.appTop.hom.comp aB
  let : Algebra R B := aB.toAlgebra
  let : Algebra R C := aC.toAlgebra
  let φ : B →ₐ[R] C := { f.appTop.hom with commutes' := fun _ ↦ rfl }
  have hφ : φ.toRingHom.FinitePresentation := by
    change f.appTop.hom.FinitePresentation
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      f.finitePresentation_appLE (isAffineOpen_top V₀.toScheme)
        (isAffineOpen_top U₀.toScheme) (by simp)
  have hB : V₀.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom aB) = q := by
    change V₀.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ q.appTop) = q
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
    change q ≫ (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = q
    rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hC : U₀.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
      f ≫ V₀.toScheme.isoSpec.hom := Scheme.isoSpec_hom_naturality f
  let a : FlatDescentChart {i : I // i₀ ≤ i} ⟨i₀, le_rfl⟩ :=
    ⟨F, B, C, aB.toAlgebra, aC.toAlgebra, φ, hφ⟩
  refine ⟨a, ?_, ?_⟩
  · intro j
    let Aj := F.obj j
    let : Algebra R Aj := (F.map
      (homOfLE (show (⟨i₀, le_rfl⟩ : {i : I // i₀ ≤ i}) ≤ j from j.property))).hom.toAlgebra
    obtain ⟨ej, hj⟩ := hi j
    exact affine_triple_tensor_base_change X₀ Y₀ f₀ W₀ V₀ U₀ hVW hUV R B C φ
      e0 V₀.toScheme.isoSpec U₀.toScheme.isoSpec hB hC
      (D.obj (op j.val)) (D.map (homOfLE j.property).op) Aj ej hj
  · let AL := colimit F
    let : Algebra R AL := (colimit.ι F ⟨i₀, le_rfl⟩).hom.toAlgebra
    obtain ⟨V, U, h, _, e⟩ :=
      affine_triple_tensor_base_change X₀ Y₀ f₀ W₀ V₀ U₀ hVW hUV R B C φ
        e0 V₀.toScheme.isoSpec U₀.toScheme.isoSpec hB hC
        c.pt (c.π.app (op i₀)) AL eL hL
    exact ⟨V, U, h, e⟩

end AlgebraicGeometry
