/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeSourceIso
import WeilConjectures.AlgebraicGeometry.SingleComplexNestedCoefficientCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Comparison invariance under nested source-open restriction

Source: Stacks Project, Tag 0DJ9, restriction to a source open in the induction step,
and Tag 08HY, canonical base-change map.
(blueprint: lem-pc-single-complex-open-nested-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Computing the comparison on a smaller open after restricting to a larger open
preserves and reflects invertibility. This is a coordinate transport statement:
it has no cover, compactness, quasi-coherence or local-isomorphism hypotheses.
Source: Stacks Project, Tag 0DJ9, induction step on a source open, and Tag 08HY.
(blueprint: lem-pc-single-complex-open-nested-comparison).

Proof: Write A = W.ι⁻¹(Z). The composite A → W → X has image Z since Z ≤ W.
The canonical isomorphism A ≅ Z over X identifies the smaller source. Pasting
pullback squares identifies (X' ×_X W) ×_W A with X' ×_X Z over both X' and Z.
The derived pullback composition comparisons identify the twice-restricted K
with its restriction to Z, and the twice-restricted K' with its restriction to
X' ×_X Z. Their associativity law and naturality with respect to φ identify the
twice-restricted coefficient morphism with the coefficient morphism restricted
once. More explicitly, let e : A ≅ Z be the image isomorphism and let
e′ : ((X′ ×_X W) ×_W A) ≅ (X′ ×_X Z) be the pullback-pasting
isomorphism. The structural maps to S and S′ agree after composition
with e and e′. The pullback comparisons and their right-adjoint mates
therefore identify the two comparison domains and codomains; the units
and counits for e and e′ are invertible since these maps are isomorphisms.
The open immersion W → X itself needs no invertible adjunction unit.
The direct-image comparisons are the mates of these same pullback
comparisons under the canonical derived adjunctions. Transpose the two
base-change arrows under their direct-image adjunctions: by Tag 08HY both
transposes consist of the pullback composition comparison followed by the
counit of the source adjunction. Naturality of that counit and the associativity
law identify the transposes. Thus the two comparison arrows are conjugate by
isomorphisms on their domain and codomain, which preserves and reflects IsIso.
For Z empty the same constructions take place in the zero module category;
for Z = W this is the identity restriction comparison. No affine hypothesis is
used, and no arbitrary coefficient witness is chosen. -/
theorem singleComplexOpenComparison_nested_isIso_iff
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (W Z : X.Opens) (hZW : Z ≤ W) :
    let hW : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
        (pullback.fst g' W.ι ≫ f') ≫ g := by
      rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
    let φW : (derivedPullback (pullback.snd g' W.ι)).obj
        ((derivedPullback W.ι).obj K) ⟶
        (derivedPullback (pullback.fst g' W.ι)).obj K' :=
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' W.ι) W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' W.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' W.ι)).map φ)
    IsIso (singleComplexOpenComparison f f' g g' h K K' φ Z) ↔
      IsIso (singleComplexOpenComparison (W.ι ≫ f) (pullback.fst g' W.ι ≫ f')
        g (pullback.snd g' W.ι) hW ((derivedPullback W.ι).obj K)
        ((derivedPullback (pullback.fst g' W.ι)).obj K') φW (W.ι ⁻¹ᵁ Z)) := by
  classical
  intro hW phiW
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let A := W.ι ⁻¹ᵁ Z
  let e := Scheme.Opens.isoOfLE hZW
  let q := pullback.snd g' W.ι
  let p := pullback.fst g' W.ι
  let t := pullback.snd q A.ι
  let r := pullback.fst q A.ι
  let e' : pullback q A.ι ≅ pullback g' Z.ι :=
    pullbackLeftPullbackSndIso g' W.ι A.ι ≪≫
      asIso (pullback.map g' (A.ι ≫ W.ι) g' Z.ι (𝟙 _) e.hom (𝟙 _)
        (by simp) (by simp [e, A]))
  have hp : e'.hom ≫ pullback.fst g' Z.ι = r ≫ p := by
    simp [e', r, p, q]
  have hq : e'.hom ≫ pullback.snd g' Z.ι = t ≫ e.hom := by
    simp [e', t, q]
  let KW := (derivedPullback W.ι).obj K
  let KW' := (derivedPullback p).obj K'
  let KZ := (derivedPullback Z.ι).obj K
  let KZ' := (derivedPullback (pullback.fst g' Z.ι)).obj K'
  let phiZ := (c (pullback.snd g' Z.ι) Z.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := Z.ι)).symm) ≫
    (c (pullback.fst g' Z.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' Z.ι)).map φ
  let phiA := (c t A.ι).hom.app KW ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KW)
      (pullback.condition (f := q) (g := A.ι)).symm) ≫
    (c r q).inv.app KW ≫ (derivedPullback r).map phiW
  let alpha : (derivedPullback e.hom).obj KZ ≅ (derivedPullback A.ι).obj KW :=
    (c e.hom Z.ι).app K ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K)
        (Scheme.Opens.isoOfLE_hom_ι hZW)) ≪≫ (c A.ι W.ι).symm.app K
  let beta : (derivedPullback e'.hom).obj KZ' ≅ (derivedPullback r).obj KW' :=
    (c e'.hom (pullback.fst g' Z.ι)).app K' ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K') hp) ≪≫
      (c r p).symm.app K'
  have hphi : (derivedPullback t).map alpha.hom ≫ phiA =
      (c t e.hom).hom.app KZ ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KZ) hq.symm) ≫
      (c e'.hom (pullback.snd g' Z.ι)).inv.app KZ ≫
      (derivedPullback e'.hom).map phiZ ≫ beta.hom := by
    exact singleComplex_nested_coefficient_coherence g' K K' φ W Z hZW e' hp hq
  have hf : e.hom ≫ (Z.ι ≫ f) = A.ι ≫ (W.ι ≫ f) := by
    simp [e, A]
  have hf' : e'.hom ≫ (pullback.fst g' Z.ι ≫ f') = r ≫ (p ≫ f') := by
    rw [← Category.assoc, hp, Category.assoc]
  have hZ : pullback.snd g' Z.ι ≫ (Z.ι ≫ f) =
      (pullback.fst g' Z.ι ≫ f') ≫ g := by
    rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
  have h0 : t ≫ (e.hom ≫ (Z.ι ≫ f)) =
      (e'.hom ≫ (pullback.fst g' Z.ι ≫ f')) ≫ g := by
    rw [← Category.assoc, ← hq, Category.assoc, hZ, ← Category.assoc]
  have transport := exists_derivedBaseChange_source_iso
    (Z.ι ≫ f) (pullback.fst g' Z.ι ≫ f') g (pullback.snd g' Z.ι) hZ
    e e' t hq.symm h0 KZ KZ' ((derivedPullback A.ι).obj KW)
    ((derivedPullback r).obj KW') phiZ phiA alpha beta hphi
  revert transport h0
  rw [hf, hf']
  intro h0 transport
  obtain ⟨a, b, hab⟩ := transport
  change IsIso (schemeDerivedBaseChangeMap (Z.ι ≫ f)
      (pullback.fst g' Z.ι ≫ f') g (pullback.snd g' Z.ι) hZ KZ ≫
        (schemeDerivedDirectImage (pullback.fst g' Z.ι ≫ f')).map phiZ) ↔
    IsIso (schemeDerivedBaseChangeMap (A.ι ≫ (W.ι ≫ f))
      (r ≫ (p ≫ f')) g t _ ((derivedPullback A.ι).obj KW) ≫
        (schemeDerivedDirectImage (r ≫ (p ≫ f'))).map phiA)
  rw [← isIso_comp_right_iff _ b.hom, hab, isIso_comp_left_iff a.hom]

end AlgebraicGeometry
