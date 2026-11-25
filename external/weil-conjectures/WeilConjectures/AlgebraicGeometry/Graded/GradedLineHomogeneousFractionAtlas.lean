/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Graded.GradedImmersionAmpleCriterion
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import all WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Graded.GradedLineFractionOverlap
import WeilConjectures.AlgebraicGeometry.Graded.GradedLineFractionTest
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# Homogeneous-fraction charts for affine-basis graded line maps

Source: Stacks Project, Constructions, Tag 01O9
(blueprint: lem-trf-graded-line-homogeneous-fraction-atlas).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem atlasFramePower_generator {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (W : T.Opens) (l : Γ(L, W)) (hl : IsFreeGenerator l) (n : ℕ) :
    IsFreeGenerator (P l n) := by
  induction n with
  | zero => rw [hP0]; exact isFreeGenerator_one W
  | succ n ih => rw [hPs]; exact hl.tmulSection ih

private theorem atlasFramePower_eq {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (W : T.Opens) (l : Γ(L, W)) (n : ℕ) : P l n = tensorPowLocalSection l n := by
  induction n with
  | zero => exact hP0 W l
  | succ n ih => rw [hPs, ih]; rfl

private theorem atlasFramePower_mul {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (W : T.Opens) (l : Γ(L, W)) (m n : ℕ) :
    (L.tensorPowAddIso m n).inv.app W (tmulSection (P l m) (P l n)) =
      P l (m + n) := by
  simp only [atlasFramePower_eq P hP0 hPs]
  exact tensorPowLocalSection_mul l m n

section Coefficients

variable {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
  (ψ : RelativeGradedLineMap h A L)
  (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
  (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
  (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
    P l (n + 1) = tmulSection l (P l n))
  (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
  (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
  (c : (n : ℕ) → A.grading U n → Γ(T, W.1))
  (hc : ∀ (n : ℕ) (a : A.grading U n), c n a • P l n =
    (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))

include ψ P hP0 hPs U W hWU l hl c hc

private theorem atlasCoefficient_zero (n : ℕ) : c n 0 = 0 := by
  apply (atlasFramePower_generator P hP0 hPs W.1 l hl n).smul_left_injective
  simp only [hc, map_zero, zero_smul]

private theorem atlasCoefficient_add (n : ℕ) (a b : A.grading U n) :
    c n (a + b) = c n a + c n b := by
  apply (atlasFramePower_generator P hP0 hPs W.1 l hl n).smul_left_injective
  simp only [add_smul, hc, map_add]

private noncomputable def atlasCoefficientAddHom (n : ℕ) :
    A.grading U n →+ Γ(T, W.1) where
  toFun := c n
  map_zero' := atlasCoefficient_zero ψ P hP0 hPs U W hWU l hl c hc n
  map_add' := atlasCoefficient_add ψ P hP0 hPs U W hWU l hl c hc n

private theorem atlasCoefficient_smul (n : ℕ) (r : Γ(S, U.1))
    (a : A.grading U n) : c n (r • a) = h.appLE U.1 W.1 hWU r * c n a := by
  apply (atlasFramePower_generator P hP0 hPs W.1 l hl n).smul_left_injective
  dsimp only
  rw [hc, mul_smul, hc, ψ.smul]
  erw [map_smul]
  rfl

private theorem atlasCoefficient_one :
    c 0 ⟨1, SetLike.one_mem_graded (A.grading U)⟩ = 1 := by
  apply (atlasFramePower_generator P hP0 hPs W.1 l hl 0).smul_left_injective
  dsimp only
  rw [hc, ψ.one, hP0, one_smul]
  change (𝟙_ T.Modules).presheaf.map (homOfLE hWU).op
    (unitSectionsEquiv (h ⁻¹ᵁ U.1) 1) = unitSectionsEquiv W.1 1
  rw [presheaf_map_unitSectionsEquiv]
  exact congrArg (unitSectionsEquiv W.1)
    (map_one (T.presheaf.map (homOfLE hWU).op).hom)

private theorem atlasCoefficient_mul (m n : ℕ) (a : A.grading U m)
    (b : A.grading U n) :
    c (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ = c m a * c n b := by
  apply (atlasFramePower_generator P hP0 hPs W.1 l hl (m + n)).smul_left_injective
  dsimp only
  rw [hc, ψ.mul]
  erw [← Hom.app_presheaf_map]
  rw [tmulSection_map]
  erw [← hc m a, ← hc n b]
  rw [smul_tmulSection, tmulSection_smul, smul_smul, Hom.app_smul,
    atlasFramePower_mul P hP0 hPs]

private noncomputable def atlasCoefficientRingHom : A.obj U →+* Γ(T, W.1) := by
  letI := A.gradedAlgebra U
  exact (DirectSum.toSemiring
    (fun n ↦ atlasCoefficientAddHom ψ P hP0 hPs U W hWU l hl c hc n)
    (atlasCoefficient_one ψ P hP0 hPs U W hWU l hl c hc)
    (fun {m n} a b ↦ atlasCoefficient_mul ψ P hP0 hPs U W hWU l hl c hc m n a b)).comp
      (DirectSum.decomposeRingEquiv (A.grading U)).toRingHom

private theorem atlasCoefficientRingHom_apply (n : ℕ) (a : A.grading U n) :
    atlasCoefficientRingHom ψ P hP0 hPs U W hWU l hl c hc a.val = c n a := by
  let := A.gradedAlgebra U
  unfold atlasCoefficientRingHom
  change (DirectSum.toSemiring _
    (atlasCoefficient_one ψ P hP0 hPs U W hWU l hl c hc)
    (fun {m n} a b ↦ atlasCoefficient_mul ψ P hP0 hPs U W hWU l hl c hc m n a b))
    (DirectSum.decompose (A.grading U) a.val) = _
  rw [DirectSum.decompose_coe, DirectSum.toSemiring_of]
  rfl

private theorem atlasCoefficient_powers (d : ℕ) (e : A.grading U d) :
    Submonoid.powers e.val ≤ (Submonoid.powers (c d e)).comap
      (atlasCoefficientRingHom ψ P hP0 hPs U W hWU l hl c hc) := by
  rintro x ⟨n, rfl⟩
  change atlasCoefficientRingHom ψ P hP0 hPs U W hWU l hl c hc (e.val ^ n) ∈
    Submonoid.powers (c d e)
  rw [map_pow, atlasCoefficientRingHom_apply]
  exact ⟨n, rfl⟩

private noncomputable def atlasFractionMap (d : ℕ) (e : A.grading U d) :
    HomogeneousLocalization.Away (A.grading U) e.val →+* Localization.Away (c d e) := by
  letI := A.gradedAlgebra U
  exact (IsLocalization.map (Localization.Away (c d e))
    (atlasCoefficientRingHom ψ P hP0 hPs U W hWU l hl c hc)
    (atlasCoefficient_powers ψ P hP0 hPs U W hWU l hl c hc d e)).comp
      (algebraMap (HomogeneousLocalization.Away (A.grading U) e.val)
        (Localization.Away e.val))

private theorem atlasFractionMap_apply (d : ℕ) (e : A.grading U d)
    (n : ℕ) (a : A.grading U (n • d)) :
    atlasFractionMap ψ P hP0 hPs U W hWU l hl c hc d e
        (HomogeneousLocalization.Away.mk (A.grading U) e.property n a.val a.property) =
      Localization.mk (c (n • d) a)
        (⟨c d e ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (c d e)) := by
  let := A.gradedAlgebra U
  simp only [atlasFractionMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk', map_pow, atlasCoefficientRingHom_apply]

private theorem atlasCoefficient_scalar (r : Γ(S, U.1)) :
    c 0 ⟨algebraMap Γ(S, U.1) (A.obj U) r,
      SetLike.algebraMap_mem_graded (A.grading U) r⟩ = h.appLE U.1 W.1 hWU r := by
  have he : (⟨algebraMap Γ(S, U.1) (A.obj U) r,
      SetLike.algebraMap_mem_graded (A.grading U) r⟩ : A.grading U 0) =
      r • ⟨1, SetLike.one_mem_graded (A.grading U)⟩ := by
    apply Subtype.ext
    simp [Algebra.smul_def]
  rw [he, atlasCoefficient_smul ψ P hP0 hPs U W hWU l hl c hc,
    atlasCoefficient_one ψ P hP0 hPs U W hWU l hl c hc, mul_one]

private theorem atlasFractionMap_scalar (d : ℕ) (e : A.grading U d) (r : Γ(S, U.1)) :
    atlasFractionMap ψ P hP0 hPs U W hWU l hl c hc d e
      (HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers e.val)
        ⟨algebraMap Γ(S, U.1) (A.obj U) r,
          SetLike.algebraMap_mem_graded (A.grading U) r⟩) =
      algebraMap Γ(T, W.1) (Localization.Away (c d e)) (h.appLE U.1 W.1 hWU r) := by
  let := A.gradedAlgebra U
  change IsLocalization.map (Localization.Away (c d e))
    (atlasCoefficientRingHom ψ P hP0 hPs U W hWU l hl c hc)
    (atlasCoefficient_powers ψ P hP0 hPs U W hWU l hl c hc d e)
    (algebraMap (A.obj U) (Localization.Away e.val)
      (algebraMap Γ(S, U.1) (A.obj U) r)) = _
  rw [IsLocalization.map_eq]
  rw [atlasCoefficientRingHom_apply ψ P hP0 hPs U W hWU l hl c hc 0
    ⟨algebraMap Γ(S, U.1) (A.obj U) r,
      SetLike.algebraMap_mem_graded (A.grading U) r⟩]
  rw [atlasCoefficient_scalar ψ P hP0 hPs U W hWU l hl c hc]

end Coefficients

/-- The relative-Proj construction for a graded line map specified on affine base opens.
The frame powers and coefficients are supplied explicitly, with their defining equations;
no sheaf-level graded decomposition or choice of such a decomposition is required.

Source: Stacks Project, Constructions, Tag 01O9, characterizations (2) and (3), and
Tag 01NK for the affine homogeneous-localization construction
(blueprint: lem-trf-graded-line-homogeneous-fraction-atlas).

Proof: Over an affine base U, trivialize L on affine source opens W. The unit and product
laws for the graded line map, together with the recursive frame-power equations, make
the coefficients a graded algebra homomorphism to O(W)[t]. On the open D(b), where b is
the coefficient of a positive-degree homogeneous element e, send a/e^n to c(a)/b^n.
The ordinary localization relation proves well-definedness even when b is a zero divisor:
multiply an equality of fractions by a further power of e, apply the graded map, and
cancel the now invertible image of b. Addition, multiplication and the degree-zero law
prove that this is a unital ring map over O(U). The affine adjunction gives a morphism
from Spec O(W)[1/b] to the standard chart D_+(e). On double generator opens, both maps
send a/(ee')^n to the same quotient of coefficients, so they agree by the affine
adjunction. The restriction law of the graded line map gives the same equality under
affine source and base refinements. Cover intersections by common affine refinements;
no separatedness hypothesis is needed. The generating hypothesis says these generator
opens cover T: in a local frame, a section outside the maximal-ideal multiple has unit
coefficient. Glue the chart maps. Their scalar formulas show that the glued morphism
lies over S. Rescaling a frame multiplies numerator and denominator by the same power
of a unit, so the construction satisfies the displayed formula for every frame.
Finally, on any open immersion with a trivialization and a prescribed homogeneous-section
ring map, the same affine adjunction and localization formulas identify its restriction
with Proj.fromOfGlobalSections. Equality on the generator-open cover proves precisely
IsCanonicalMap. Empty opens, nilpotent denominators and degree-zero numerators are
covered by the same localization identities. -/
theorem graded_line_homogeneous_fraction_atlas {S T : Scheme.{u}} (h : T ⟶ S)
    (A : S.GradedAlgebraData) (L : T.Modules) [L.IsInvertible]
    (ψ : RelativeGradedLineMap h A L) (hgen : ψ.GeneratesEverywhere)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : ∀ (U : S.affineOpens) (W : T.affineOpens),
      W.1 ≤ h ⁻¹ᵁ U.1 → Γ(L, W.1) → (n : ℕ) → A.grading U n → Γ(T, W.1))
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a)) :
    ∃ F : T ⟶ A.relProj, ψ.IsCanonicalMap F ∧
      ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
        (l : Γ(L, W.1)), IsFreeGenerator l →
        ∀ (d : ℕ) (hd : 0 < d) (e : A.grading U d),
        ∃ ρ : HomogeneousLocalization.Away (A.grading U) e.val →+*
            Localization.Away (c U W hWU l d e),
          (∀ (n : ℕ) (a : A.grading U (n • d)),
            ρ (HomogeneousLocalization.Away.mk (A.grading U) e.property n a.val
                a.property) =
              Localization.mk (c U W hWU l (n • d) a)
                (⟨c U W hWU l d e ^ n, ⟨n, rfl⟩⟩ :
                  Submonoid.powers (c U W hWU l d e))) ∧
          (∀ r : Γ(S, U.1),
            ρ (HomogeneousLocalization.fromZeroRingHom (A.grading U)
                (Submonoid.powers e.val)
                ⟨algebraMap Γ(S, U.1) (A.obj U) r,
                  SetLike.algebraMap_mem_graded (A.grading U) r⟩) =
              algebraMap Γ(T, W.1) (Localization.Away (c U W hWU l d e))
                (h.appLE U.1 W.1 hWU r)) ∧
          (Spec.map (CommRingCat.ofHom
              (algebraMap Γ(T, W.1) (Localization.Away (c U W hWU l d e)))) ≫
              W.2.isoSpec.inv ≫ W.1.ι) ≫ F =
            Spec.map (CommRingCat.ofHom ρ) ≫
              Proj.awayι (A.grading U) e.val e.property hd ≫ A.relProjι U := by
  classical
  let ρ (i : GradedLineFractionChart h A L) :=
    atlasFractionMap ψ P hP0 hPs i.U i.W i.hWU i.l i.hl
      (c i.U i.W i.hWU i.l) (hc i.U i.W i.hWU i.l i.hl) i.d i.e
  have hρ : GradedLineFractionChart.FractionFormula c ρ := by
    intro i n a
    exact atlasFractionMap_apply ψ P hP0 hPs i.U i.W i.hWU i.l i.hl
      (c i.U i.W i.hWU i.l) (hc i.U i.W i.hWU i.l i.hl) i.d i.e n a
  have hscalar (i : GradedLineFractionChart h A L) (r : Γ(S, i.U.1)) :
      ρ i (algebraMap Γ(S, i.U.1)
        (HomogeneousLocalization.Away (A.grading i.U) i.e.val) r) =
        algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))
          (h.appLE i.U.1 i.W.1 i.hWU r) := by
    exact atlasFractionMap_scalar ψ P hP0 hPs i.U i.W i.hWU i.l i.hl
      (c i.U i.W i.hWU i.l) (hc i.U i.W i.hWU i.l i.hl) i.d i.e r
  have hrange (i : GradedLineFractionChart h A L) :
      (i.source c).opensRange = T.basicOpen (i.coefficient c) := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c)))) ≫
        i.W.2.fromSpec).opensRange = _
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
      i.W.2.fromSpec_image_basicOpen]
  have hcover (x : T) :
      ∃ i : GradedLineFractionChart h A L, x ∈ (i.source c).opensRange := by
    obtain ⟨U, hxU, d, hd, e, he⟩ := hgen x
    let : SheafOfModules.IsInvertible.{u, u, u} L :=
      IsInvertible.sheafOfModules_isInvertible L
    obtain ⟨W, hxW, hWU, l, hl⟩ := exists_isFreeGenerator L hxU
    let i : GradedLineFractionChart h A L := ⟨U, W, hWU, l, hl, d, hd, e⟩
    refine ⟨i, ?_⟩
    rw [hrange]
    apply (T.mem_basicOpen (i.coefficient c) x hxW).mpr
    by_contra hn
    apply he
    have hg := congrArg ((L.tensorPow d).presheaf.germ W.1 x hxW)
      (hc U W hWU l hl d e)
    rw [germ_smul] at hg
    have hres := (L.tensorPow d).presheaf.germ_res_apply (homOfLE hWU) x hxW
      (ψ.component U d e)
    exact (hg.trans hres) ▸
      Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hn) Submodule.mem_top
  let 𝒰 : T.OpenCover :=
    { I₀ := GradedLineFractionChart h A L
      X i := i.domain c
      f i := i.source c
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨hcover, fun i ↦ inferInstance⟩ }
  have hover := gradedLineFraction_overlap ψ P hP0 hPs c hc ρ hρ
  let F : T ⟶ A.relProj := 𝒰.glueMorphisms (fun i ↦ i.target c ρ) hover
  have hF (i : GradedLineFractionChart h A L) : i.source c ≫ F = i.target c ρ :=
    𝒰.ι_glueMorphisms _ hover i
  have hoverS (i : GradedLineFractionChart h A L) :
      i.target c ρ ≫ A.relProjHom = i.source c ≫ h := by
    dsimp only [GradedLineFractionChart.target, GradedLineFractionChart.source]
    rw [Category.assoc, Category.assoc, A.relProjι_relProjHom]
    change Spec.map (CommRingCat.ofHom (ρ i)) ≫
      Proj.awayι (A.grading i.U) i.e.val i.e.property i.hd ≫
        Proj.toSpecOfAlgebra (A.grading i.U) ≫ i.U.2.fromSpec = _
    rw [Proj.awayι_toSpecOfAlgebra_assoc, ← Spec.map_comp_assoc]
    have hs : CommRingCat.ofHom
        (algebraMap Γ(S, i.U.1)
          (HomogeneousLocalization.Away (A.grading i.U) i.e.val)) ≫
          CommRingCat.ofHom (ρ i) =
        h.appLE i.U.1 i.W.1 i.hWU ≫ CommRingCat.ofHom
          (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))) := by
      ext r
      exact hscalar i r
    rw [hs, Spec.map_comp_assoc, IsAffineOpen.SpecMap_appLE_fromSpec]
    rfl
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · apply 𝒰.hom_ext
    intro i
    rw [← Category.assoc, hF, hoverS]
  · intro W j hj V q e α hα hαgen
    exact gradedLineFraction_test ψ P hP0 hPs c hc ρ hρ F hF
      W j hj V q e α hα hαgen
  · intro U W hWU l hl d hd e
    let i : GradedLineFractionChart h A L := ⟨U, W, hWU, l, hl, d, hd, e⟩
    refine ⟨ρ i, ?_, ?_, ?_⟩
    · exact hρ i
    · exact hscalar i
    · exact hF i

end AlgebraicGeometry.Scheme.Modules
