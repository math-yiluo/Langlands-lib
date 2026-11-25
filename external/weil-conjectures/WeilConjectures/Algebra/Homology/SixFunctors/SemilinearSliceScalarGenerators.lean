/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic
import WeilConjectures.Algebra.Homology.Slice.SliceScalarTowerConstruction
import WeilConjectures.Algebra.Homology.Slice.SliceSystemExtensionConstruction
import WeilConjectures.Algebra.Homology.Slice.SliceScalarLevelComparison

/-! # Assembly of the scalar comparison on strict systems and complexes

Source: Stacks Project, Modules on Sites, Tags 0E8I, 03DI, 03CY and 03EK.
(blueprint: lem-sf-semilinear-slice-scalar-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r
open CategoryTheory Opposite
attribute [local implicit_reducible] CategoryTheory.sheafCompose
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C)

private theorem extension_unit (A : Sheaf J CommRingCat.{max c v r})
    (G : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
    (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x =
      ringedSliceExtensionSection.{c, v, r} A U G W x := by
  exact (localizedSystemAdjunction_existsUnique.{c, v, r} A U).exists.choose_spec G (op W) x

private theorem extension_ext (A : Sheaf J CommRingCat.{max c v r})
    (G : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U))
    (K : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J A))
    (f g : (localizedSystemExtension.{c, v, r} A U).obj G ⟶ K)
    (h : ∀ (W : Over U) (x : G.val.obj (op W)), f.val.app (op W.left)
      (ringedSliceExtensionSection.{c, v, r} A U G W x) =
      g.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} A U G W x)) : f = g := by
  apply ((localizedSystemAdjunction.{c, v, r} A U).homEquiv G K).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change f.val.app (op W.unop.left)
    (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app W x) =
      g.val.app (op W.unop.left)
        (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app W x)
  rw [extension_unit.{c, v, r} U A G W.unop x]
  exact h W.unop x

private theorem extension_map (A : Sheaf J CommRingCat.{max c v r})
    {G G' : ringedSiteModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A).over U)}
    (f : G ⟶ G') (W : Over U) (x : G.val.obj (op W)) :
    ((localizedSystemExtension.{c, v, r} A U).map f).val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} A U G W x) =
      ringedSliceExtensionSection.{c, v, r} A U G' W (f.val.app (op W) x) := by
  have h := congrArg (fun f ↦ f.val.app (op W) x)
    ((localizedSystemAdjunction.{c, v, r} A U).unit.naturality f)
  change ((localizedSystemAdjunction.{c, v, r} A U).unit.app G').val.app (op W)
      (f.val.app (op W) x) =
    ((localizedSystemExtension.{c, v, r} A U).map f).val.app (op W.left)
      (((localizedSystemAdjunction.{c, v, r} A U).unit.app G).val.app (op W) x) at h
  rw [extension_unit.{c, v, r} U A, extension_unit.{c, v, r} U A] at h
  exact h.symm

variable
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The normalized scalar comparison exists on strict semilinear systems and on
arbitrary unbounded complexes, with no flatness, surjectivity or completeness assumption.
Source: Stacks 0E8I, with Tags 03DI, 03CY, 03EK and Sites 00WK
(blueprint: lem-sf-semilinear-slice-scalar-generators).

Proof:
1. Extension over B_n and extension over O after scalar restriction have the same
abelian direct-sum presheaf and the same O-action. Uniqueness of the action on its
associated sheaf gives the unique summand-preserving scalarIdentification. The same
calculation for q_{m,n} extends transitions by [x]_f ↦ [t_{m,n}(x)]_f; identity and
composition follow on every summand. This constructs extension.F and its maps.
2. By the underlying-set sheafification comparison and local-section theorem (00WK),
every section of a sheafification is locally represented by a presheaf section. The
extension presheaf sections are finite sums of original summands. Tensor sections are
locally finite sums of pure tensors; refine the cover for their finitely many factors.
Thus equality can be checked on [x]_f tensor b, even after successive sheafifications.
3. Apply exists_ringedSliceTensorGenerators with H = B_n as an O-module and compose
with the summand-preserving scalar identification. This gives component with the stated
forward formula, inverse formula and uniqueness. No flatness is used.
4. The formula sends c([x]_f tensor b) to [x tensor cb]_f, which equals
c[x tensor b]_f because restriction preserves multiplication. The local generator test
proves B_n-linearity; injectivity then proves linearity of the inverse.
5. The two transition composites send a generator to [x tensor q_{m,n}(b)]_f;
restriction and q commute by naturality of the ring-sheaf transition. This proves all
transition squares; composing with inverses gives the inverse system morphism.
6. A module map v acts on the first tensor factor, so both naturality composites send
[x]_f tensor b to [v(x) tensor b]_f. The local generator test proves naturality in G.
7. The scalar units insert one; q preserves one, so they define strict O-tower maps.
Both augmentation composites send [x]_f to [x tensor 1]_f. Sheafification uniqueness
gives the asserted square of sheaf maps; compose with the inverse for the inverse square.
8. Apply comparison degreewise to a cochain complex. Naturality with each differential
gives the chain equation; additivity gives complexes. The inverse chain equation follows
by cancellation. The transition, generator and augmentation equations hold in every
degree, and naturality with chain maps follows degreewise. There is no sum over degrees
or totalization, so the result holds for unbounded complexes. -/
theorem exists_semilinearSliceScalarGenerators (O : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj O ⟶ B) :
    Nonempty (SemilinearSliceScalarGenerators.{c, v, r} B U O α) := by
  obtain ⟨AX⟩ := exists_sliceScalarTowerPresentation.{c, v, r} O B α
  obtain ⟨AV⟩ := exists_sliceScalarTowerPresentation.{max c v, v, r} (O.over U)
    (sliceScalarRings.{c, v, r} B U) (sliceScalarAlgebra.{c, v, r} B U O α)
  obtain ⟨E⟩ := exists_sliceSystemExtensionPresentation.{c, v, r} B U
  obtain ⟨p⟩ := exists_sliceScalarLevelComparison.{c, v, r} B U O α AX AV E
  let a : localizedSystemExtension.{c, v, r} O U ⋙ AX.F ⟶ AV.F ⋙ E.F :=
    { app := fun G ↦
        { app := sliceScalarComponentHom.{c, v, r} B U O α AX AV E p.component G
          comm := p.transition G }
      naturality := by
        intro G G' g
        apply strictRingSystem_hom_ext B
        intro n
        exact p.naturality g n }
  have ha : ∀ G, IsIso (a.app G) := by
    intro G
    apply (strictRingSystem_isIso_iff B (a.app G)).2
    intro n
    change IsIso (sliceScalarComponentHom.{c, v, r} B U O α AX AV E p.component G n)
    unfold sliceScalarComponentHom
    infer_instance
  let e := NatIso.ofComponents (fun G ↦ asIso (a.app G)) (fun f ↦ a.naturality f)
  have hAX := AX.additive
  have hAV := AV.additive
  have hE := E.additive
  refine ⟨{
    AX := AX
    AV := AV
    extension := E
    comparison := e
    component := p.component
    component_eq := fun _ _ ↦ rfl
    generator := p.generator
    unique := p.unique
    inverse_generator := ?_
    scalarIdentification := p.scalarIdentification
    scalarIdentification_generator := p.scalarIdentification_generator
    scalarIdentification_unique := p.scalarIdentification_unique
    augmentation := ?_
    chain := NatIso.mapHomologicalComplex e (.up ℤ)
    chain_degree := fun _ _ ↦ rfl
    chain_inverse_degree := fun _ _ ↦ rfl }⟩
  · intro G n W x b
    have h := congrArg ((p.component G n).inv.val.app (op W.left))
      (p.generator G n W x b)
    have hi := congrArg (fun f ↦ f.val.app (op W.left)
      (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} O U G W x) b))
      (p.component G n).hom_inv_id
    exact h.symm.trans hi
  · intro G n
    let F := changeOfRings.{v, max c v, max c v r}
      ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G
    apply extension_ext.{c, v, r} U O
    intro W x
    change (p.component G n).hom.val.app (op W.left)
      ((eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n)).val.app
        (op W.left) ((AX.unit ((localizedSystemExtension.{c, v, r} O U).obj G) n).val.app
          (op W.left) (ringedSliceExtensionSection.{c, v, r} O U G W x))) =
      (p.scalarIdentification n _).hom.val.app (op W.left)
        (((localizedSystemExtension.{c, v, r} O U).map
          (AV.unit G n ≫
            (restrictScalars ((sheafCompose (J.over U)
              (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
              ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).map
                (eqToHom (AV.obj_eq G n)))).val.app (op W.left)
          (ringedSliceExtensionSection.{c, v, r} O U G W x))
    rw [AX.unit_pure, p.generator, extension_map.{c, v, r}]
    change ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W
      (sliceScalarPure.{max c v, v, r}
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x 1) =
      (p.scalarIdentification n F).hom.val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} O U
          ((restrictScalars ((sheafCompose (J.over U)
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
              ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).obj F) W
          ((eqToHom (AV.obj_eq G n)).val.app (op W)
            ((AV.unit G n).val.app (op W) x)))
    rw [AV.unit_pure, p.scalarIdentification_generator]

end SheafOfModules
