/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso

/-!
# Tensor-product comparison for a single affine chart

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Morphisms, Tag 01TQ.
(blueprint: lem-weil-pbc-affine-chart-tensor-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A fixed affine triple admits one finitely presented algebra map whose tensor
base changes describe the restricted chart morphism for every compatible affine base open.
There is no inverse system or limiting cone in this statement.

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Morphisms, Tag 01TQ;
Limits, Tag 07RP, affine reduction.
(blueprint: lem-weil-pbc-affine-chart-tensor-comparison).

Proof: Set B = Γ(Y₀,V) and C = Γ(X₀,U). The isomorphism e0 identifies R with
Γ(S,W). Transport the algebra structures given by Y₀.hom.appLE W V eV and
X₀.hom.appLE W U along this identification. The inclusion needed for the latter
follows from eU, eV, and f₀.left ≫ Y₀.hom = X₀.hom. The restriction
f₀.left.appLE V U eU is an R-algebra map φ by functoriality of appLE.
Its underlying ring map is finitely presented by finitePresentation_appLE hV hU eU;
this is precisely φ.FinitePresentation. For any t and compatible e, the inverse
image of V in Y_T is V ×_W W_T, and the inverse image of U in X_T is U ×_W W_T.
Indeed their structure maps factor through W_T by the two given open inclusions;
the open pullback universal property identifies these schemes and projections.
Apply hV.isoSpec, hU.isoSpec, e0 and e, then pullbackSpecIso, to identify them
with Spec(A ⊗[R] B) and Spec(A ⊗[R] C). Compatibility h ensures that these are
pullbacks over the algebraMap R A. The chart map corresponds to Spec(id ⊗ φ):
check its two projections using the identities on a ⊗ 1 and 1 ⊗ b, and use
pullback uniqueness. The restricted map factors the original source-chart map through the target
chart inclusion, giving the asserted equality. Empty charts cause no exception: the same
pullback and spectrum identities hold for zero coordinate rings. -/
theorem exists_affineChart_tensorComparison
    {S : Scheme.{u}} (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFinitePresentation f₀.left]
    (W : S.Opens) (hW : IsAffineOpen W)
    (V : Y₀.left.Opens) (hV : IsAffineOpen V) (eV : V ≤ Y₀.hom ⁻¹ᵁ W)
    (U : X₀.left.Opens) (hU : IsAffineOpen U) (eU : U ≤ f₀.left ⁻¹ᵁ V)
    (R : CommRingCat.{u}) (e0 : W.toScheme ≅ Spec R) :
    ∃ (B C : CommRingCat.{u}) (aB : Algebra R B) (aC : Algebra R C),
      letI := aB
      letI := aC
      ∃ φ : B →ₐ[R] C, φ.FinitePresentation ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ S) (A : CommRingCat.{u}) (aA : Algebra R A),
          letI := aA
          ∀ (e : (t ⁻¹ᵁ W).toScheme ≅ Spec A),
            t.resLE W _ le_rfl ≫ e0.hom =
              e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            ∃ g : ((pullback.fst X₀.hom t) ⁻¹ᵁ U).toScheme ⟶
                ((pullback.fst Y₀.hom t) ⁻¹ᵁ V).toScheme,
              g ≫ ((pullback.fst Y₀.hom t) ⁻¹ᵁ V).ι =
                ((pullback.fst X₀.hom t) ⁻¹ᵁ U).ι ≫
                  ((Over.pullback t).map f₀).left ∧
              Nonempty (Arrow.mk g ≅ Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  let B := Γ(Y₀.left, V)
  let C := Γ(X₀.left, U)
  let q : B ⟶ C := f₀.left.appLE V U eU
  let rW : R ⟶ Γ(S, W) := Spec.preimage (hW.isoSpec.inv ≫ e0.hom)
  let rB : R ⟶ B := rW ≫ Y₀.hom.appLE W V eV
  let aB : Algebra R B := rB.hom.toAlgebra
  let aC : Algebra R C := (rB ≫ q).hom.toAlgebra
  let φ : B →ₐ[R] C :=
    { q.hom with commutes' := fun r ↦ rfl }
  refine ⟨B, C, aB, aC, φ, ?_, ?_⟩
  · exact f₀.left.finitePresentation_appLE hV hU eU
  · intro T t A aA
    let := aA
    intro e h
    have hB : Y₀.hom.resLE W V eV ≫ e0.hom =
        hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      change _ = hV.isoSpec.hom ≫ Spec.map (rW ≫ Y₀.hom.appLE W V eV)
      rw [Spec.map_comp, ← Category.assoc]
      change _ = (V.toSpecΓ ≫ Spec.map (Y₀.hom.appLE W V eV)) ≫ Spec.map rW
      rw [Scheme.Opens.toSpecΓ_SpecMap_appLE]
      simp [rW, ← hW.isoSpec_hom]
    have hφ : f₀.left.resLE V U eU ≫ hV.isoSpec.hom =
        hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
      exact (Scheme.Opens.toSpecΓ_SpecMap_appLE f₀.left V U eU).symm
    have eUW : U ≤ X₀.hom ⁻¹ᵁ W := by
      rw [← Over.w f₀, Scheme.Hom.comp_preimage]
      exact eU.trans ((TopologicalSpace.Opens.map f₀.left.base).map (homOfLE eV)).le
    have hC : X₀.hom.resLE W U eUW ≫ e0.hom =
        hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
      change _ = hU.isoSpec.hom ≫ Spec.map (rB ≫ q)
      have hφ' : f₀.left.resLE V U eU ≫ hV.isoSpec.hom =
          hU.isoSpec.hom ≫ Spec.map q := hφ
      have hB' : Y₀.hom.resLE W V eV ≫ e0.hom =
          hV.isoSpec.hom ≫ Spec.map rB := hB
      rw [Spec.map_comp, ← Category.assoc, ← hφ', Category.assoc, ← hB']
      rw [← Category.assoc]
      apply congrArg (fun k : U.toScheme ⟶ W.toScheme ↦ k ≫ e0.hom)
      rw [← cancel_mono W.ι]
      simp only [Scheme.Hom.resLE_comp_ι, Category.assoc,
        Scheme.Hom.resLE_comp_ι_assoc, Over.w]
    obtain ⟨iB, hiB₁, hiB₂⟩ := exists_affineChart_baseChangeIso
      Y₀.hom W V eV R B e0 hV.isoSpec hB T t A e h
    obtain ⟨iC, hiC₁, hiC₂⟩ := exists_affineChart_baseChangeIso
      X₀.hom W U eUW R C e0 hU.isoSpec hC T t A e h
    let fT := ((Over.pullback t).map f₀).left
    have hf₁ : fT ≫ pullback.fst Y₀.hom t = pullback.fst X₀.hom t ≫ f₀.left := by
      simp [fT, Over.pullback_map_left]
    have hf₂ : fT ≫ pullback.snd Y₀.hom t = pullback.snd X₀.hom t := by
      simp [fT, Over.pullback_map_left]
    have eUT : (pullback.fst X₀.hom t) ⁻¹ᵁ U ≤
        fT ⁻¹ᵁ ((pullback.fst Y₀.hom t) ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, hf₁, Scheme.Hom.comp_preimage]
      exact ((TopologicalSpace.Opens.map (pullback.fst X₀.hom t).base).map
        (homOfLE eU)).le
    let g := fT.resLE _ _ eUT
    let ψ := Algebra.TensorProduct.map (AlgHom.id R A) φ
    let sψ := Spec.map (CommRingCat.ofHom ψ.toRingHom)
    have hRight : sψ ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫
          Spec.map q := by
      dsimp [sψ]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
    have hLeft : sψ ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] C)) := by
      dsimp [sψ]
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [ψ]
    refine ⟨g, Scheme.Hom.resLE_comp_ι fT eUT, ⟨?_⟩⟩
    refine Arrow.isoMk' g sψ iC iB ?_
    rw [← cancel_epi iC.inv, ← cancel_mono iB.inv,
      ← cancel_mono (((pullback.fst Y₀.hom t) ⁻¹ᵁ V).ι)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hiB₁, reassoc_of% hRight]
      dsimp [g]
      rw [Scheme.Hom.resLE_comp_ι_assoc, hf₁, reassoc_of% hiC₁]
      have hh := IsAffineOpen.SpecMap_appLE_fromSpec f₀.left hV hU eU
      change Spec.map q ≫ hV.isoSpec.inv ≫ V.ι = hU.isoSpec.inv ≫ U.ι ≫ f₀.left at hh
      simpa only [Category.assoc, IsAffineOpen.fromSpec, AlgHom.toRingHom_eq_coe] using
        congrArg
        (fun k ↦ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫ k) hh
    · simp only [Category.assoc]
      rw [hiB₂, reassoc_of% hLeft]
      dsimp [g]
      rw [Scheme.Hom.resLE_comp_ι_assoc, hf₂, hiC₂]

end AlgebraicGeometry
