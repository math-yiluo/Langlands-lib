/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproductComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafificationAffineRestriction
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Coproduct presentation of the ordinary external direct image

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, degree-zero formula.
(blueprint: lem-sc-picard-external-coefficients-pushforward-coproduct).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary direct image of external coefficients is a coproduct of G.
No positive-degree acyclicity of either coefficient is needed.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the degree-zero
case of the displayed derived-direct-image formula.
(blueprint: lem-sc-picard-external-coefficients-pushforward-coproduct).

Proof: Choose a k-basis of Gamma(X,F), indexed by a small type I. Each basis
section defines a map G to pr2_* E: over V send t to the external product of the
basis section with t. The adjunction-unit formulas commute with restrictions and
are O_Y(V)-linear, so these are morphisms of module sheaves. On every affine V,
the finite affine cover of X and affine-diagonal intersections identify sections
of pr2_* E with Gamma(X,F) tensor_k G(V). This is the affine-right external
section comparison; its pure-tensor formula identifies the displayed maps with
basis inclusions. Basis expansion gives the algebraic direct sum of copies of
G(V). The sheaf coproduct is obtained by sheafifying the presheaf coproduct.
Its comparison to pr2_* E is an isomorphism on the affine basis, hence on stalks
and therefore as a sheaf. Transfer the coproduct cofan along this isomorphism.
This uses sheafification, not an assertion about arbitrary sections of an infinite
sheaf coproduct. Zero Gamma(X,F) gives an empty basis and the zero coproduct;
empty schemes and zero G satisfy the same construction. -/
theorem picardExternalCupCoefficients_pushforward_coproduct
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    : ∃ (I : Type w)
      (ι : ∀ _ : I, G ⟶ (RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).obj (externalCupCoefficients f g F G)),
      Nonempty (IsColimit (Cofan.mk _ ι)) := by
  classical
  let I := Module.Basis.ofVectorSpaceIndex k (scalarObj f F (Opposite.op ⊤))
  let b := Module.Basis.ofVectorSpace k (scalarObj f F (Opposite.op ⊤))
  let D := (RingedSpace.moduleDirectImage
    (pullback.snd f g).toLRSHom.toShHom).obj (externalCupCoefficients f g F G)
  let P := ∐ fun _ : I ↦ G.val
  let S := PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)
  obtain ⟨e⟩ := exists_external_coproduct_comparison k X Y f g F G I b
  let PP := (Functor.const (Discrete PUnit.{1})).obj P
  let QQ := (Functor.const (Discrete PUnit.{1})).obj D
  let ee : PP ⋙ PresheafOfModules.pushforward₀
      (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj ≅
      QQ ⋙ SheafOfModules.forget Y.ringCatSheaf ⋙ PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj :=
    NatIso.ofComponents (fun _ ↦ e) (by
      intros
      change _ ≫ e.hom = e.hom ≫
        (PresheafOfModules.pushforward₀
          (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
          Y.ringCatSheaf.obj).map (𝟙 D.val)
      erw [CategoryTheory.Functor.map_id]
      simp only [PP, Functor.const_obj_map, Functor.comp_map]
      erw [CategoryTheory.Functor.map_id]
      exact (CategoryTheory.Category.id_comp e.hom).trans
        (CategoryTheory.Category.comp_id e.hom).symm)
  obtain ⟨es⟩ := module_sheafification_iso_of_affine_restriction Y PP QQ ee
  let ed : S.obj P ≅ D := es.app ⟨PUnit.unit⟩
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let eg : S.obj G.val ≅ G := asIso (a.counit.app G)
  let c : Cofan (fun _ : I ↦ S.obj G.val) :=
    Cofan.mk (S.obj P) (fun i ↦ S.map (Sigma.ι (fun _ : I ↦ G.val) i))
  have hc : IsColimit c :=
    Cofan.isColimitMapCoconeEquiv S (fun _ : I ↦ G.val)
      (Cofan.mk P (Sigma.ι (fun _ : I ↦ G.val)))
      (isColimitOfPreserves S (coproductIsCoproduct (fun _ : I ↦ G.val)))
  let ei : Discrete.functor (fun _ : I ↦ G) ≅
      Discrete.functor (fun _ : I ↦ S.obj G.val) :=
    Discrete.natIso (fun _ ↦ eg.symm)
  let hcc := (IsColimit.precomposeHomEquiv ei c).symm hc
  let cc : Cofan (fun _ : I ↦ G) := (Cocone.precompose ei.hom).obj c
  refine ⟨I, fun i ↦ cc.inj i ≫ ed.hom, ⟨?_⟩⟩
  exact hcc.ofIsoColimit (Cofan.ext ed (fun _ ↦ rfl))

end AlgebraicGeometry.Scheme.Modules
