/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.RelativeMVBoundaryCompletion
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionSquares

/-! # Canonically identified relative Mayer--Vietoris triangles

Source: Stacks Project, Tag 0DJ9, induction step, and Tags 08BV, 08HZ and 08HY.
-/

@[expose] public section

universe um wm
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Construct the two relative Mayer--Vietoris triangles with their open terms
identified by the canonical composition comparisons, and construct the morphism
whose components are exactly the given global and local base-change composites.
No local isomorphism hypothesis or global isomorphism conclusion is assumed.

Source: Stacks Project, Tag 0DJ9, induction diagram; Cohomology, Tags 08BV, 08HZ and 08HY
(blueprint: lem-pc-relative-mv-canonical-triangles).
Proof:
1. The sources X and X' are qcqs: f and its base change are qcqs over affine
bases. The morphism g is affine, so g' is affine; inverse images of the three
quasi-compact opens are quasi-compact and cover X'. Construct the Mayer--Vietoris
triangles for K and K' using Tag 08BV.
2. Apply the triangulated functors Lg* Rf* and Rf'* respectively. Identify every
open term with the direct image along W → S or W' → S', using the composition
isomorphisms which are mates of the canonical derived pullback comparisons.
The pullback of W.ι is canonically the inverse-image open. Exact restriction
along an open immersion computes its derived pullback; use its canonical derived
comparison, rather than an arbitrary witness of existence of an isomorphism.
Transport both triangles, including their connecting arrows, along these
identifications. Additive functors identify the two middle terms with biproducts.
3. Transpose φ to K → Rg'*K'. Functoriality of the Mayer--Vietoris triangle and
its compatibility with direct image give a morphism of the two relative
triangles; transposing back preserves all three commuting squares, including the
connecting square because the derived adjunction commutes with shift. On an open
W, the mates calculation of Tag 08HY identifies the component with the base-change
map for the outer square followed by the restriction of φ. Expand the counit of
the composite adjunction into its two counits; their triangle identities give
vertical pasting. The two composition comparisons for g' and W.ι, with the
pullback equality between their composites, give precisely the displayed local
map. Naturality identifies the middle component with biprod.map of the U and V
components. The first component is the displayed global map.
The empty-open and zero-complex cases are the same construction with zero terms;
no nonempty or nonzero hypothesis is needed. -/
theorem relativeMV_canonicalTriangles
    [∀ Z : Scheme.{um},
      HasDerivedCategory.{wm} (SheafOfModules.{um} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{um}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X)
    (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
 :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun W ↦
      Arrow.mk (schemeDerivedBaseChangeMap (W.ι ≫ f)
      (pullback.fst g' W.ι ≫ f') g (pullback.snd g' W.ι)
      (by rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc])
      ((derivedPullback W.ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map
        (((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.snd g' W.ι) W.ι).hom.app K ≫
        eqToHom (congrArg (fun k => (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := W.ι)).symm) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.fst g' W.ι) g').inv.app K ≫
        (derivedPullback (pullback.fst g' W.ι)).map φ))
    let aX := Arrow.mk (schemeDerivedBaseChangeMap f f' g g' hpull.w K ≫
      (schemeDerivedDirectImage f').map φ)
    ∃ (d₁ : aX.left ⟶ (a U).left ⊞ (a V).left)
      (d₂ : (a U).left ⊞ (a V).left ⟶ (a (U ⊓ V)).left)
      (d₃ : (a (U ⊓ V)).left ⟶ aX.left⟦(1 : ℤ)⟧)
      (d₁' : aX.right ⟶ (a U).right ⊞ (a V).right)
      (d₂' : (a U).right ⊞ (a V).right ⟶ (a (U ⊓ V)).right)
      (d₃' : (a (U ⊓ V)).right ⟶ aX.right⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ t : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        t.hom₁ = aX.hom ∧
        t.hom₂ = biprod.map (a U).hom (a V).hom ∧
        t.hom₃ = (a (U ⊓ V)).hom := by
  classical
  let a := relativeMVLocalArrow f f' g g' hpull K K' φ
  let aX := relativeMVGlobalArrow f f' g g' hpull K K' φ
  have h := relativeMV_boundary_completion f f' g g' hpull K K' φ
    U V hcover
  let δ := Classical.choose h
  have h' := Classical.choose_spec h
  let δ' := Classical.choose h'
  have ht := Classical.choose_spec h'
  have hs := relativeMV_restriction_squares f f' g g' hpull K K' φ U V
  let t := Triangle.homMk
    (Triangle.mk (relativeMVSourceFirst f g U V K) (relativeMVSourceSecond f g U V K) δ)
    (Triangle.mk (relativeMVTargetFirst g' f' U V K')
      (relativeMVTargetSecond g' f' U V K') δ')
    aX.hom (biprod.map (a U).hom (a V).hom) (a (U ⊓ V)).hom hs.1 hs.2 ht.2.2
  exact ⟨relativeMVSourceFirst f g U V K, relativeMVSourceSecond f g U V K, δ,
    relativeMVTargetFirst g' f' U V K', relativeMVTargetSecond g' f' U V K', δ',
    ht.1, ht.2.1, t, rfl, rfl, rfl⟩

end AlgebraicGeometry
