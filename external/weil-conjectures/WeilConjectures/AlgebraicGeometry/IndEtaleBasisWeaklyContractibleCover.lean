/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Weakly contractible covers in the affine ind-etale basis

Source: Stacks Project, proetale.tex, Tag 0990, affine `S_app` clause;
sites.tex, Tags 090L and 090K (2)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- Transport a section lift through the equivalence given by restriction to the basis. -/
private theorem surjective_evaluation_of_full_site (S : Scheme.{u}) (V : S.AffineProEt)
    (hV : (ProEt.topology S).IsWeaklyContractible.{u + 1} ((toProEt S).obj V))
    (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q) [Epi φ] :
    Function.Surjective (φ.hom.app (op V)) := by
  -- Restriction is an equivalence, so its inverse preserves epimorphisms.
  let R := (toProEt S).sheafPushforwardContinuous (Type (u + 1))
    (topology S) (ProEt.topology S)
  let E := R.asEquivalence
  let φ' := E.inverse.map φ
  have : Epi φ' := inferInstance
  have hφ' := hV φ' ((Sheaf.isLocallySurjective_iff_epi φ').2 inferInstance)
  let ev := sheafToPresheaf (topology S) (Type (u + 1)) ⋙
    (CategoryTheory.evaluation _ _).obj (op V)
  let eP := ev.mapIso (E.counitIso.app P)
  let eQ := ev.mapIso (E.counitIso.app Q)
  intro s
  obtain ⟨q, hq⟩ := hφ' (eQ.inv s)
  refine ⟨eP.hom q, ?_⟩
  have hn := congrArg (fun f ↦ f.hom.app (op V)) (E.counitIso.hom.naturality φ)
  have hn' := congrArg (fun f ↦ f q) hn
  change eQ.hom (φ'.hom.app _ q) = φ.hom.app (op V) (eP.hom q) at hn'
  symm at hn'
  exact hn'.trans ((congrArg (fun x ↦ eQ.hom x) hq).trans
    (ConcreteCategory.congr_hom eQ.inv_hom_id s))

/-- Every object of the affine ind-etale basis of an affine scheme admits a covering
by objects that are weakly contractible in this same basis site.
Source: Stacks Project, Tag 0990, affine `S_app` clause, and Tags 090L, 090K (2)
(auxiliary; not a blueprint node).

Proof:
1. Apply `exists_isWContractibleRing` to the global sections of `U.left`, obtaining
   a faithfully flat ind-etale algebra `D` in the same universe. Compose its spectrum
   map with `U.left.isoSpec.inv` and `U.hom`. Ind-etale composition puts this object
   in the affine basis; faithful flatness gives a surjective singleton pro-etale cover.
2. `ProEt.isWeaklyContractible_of_iso` gives weak contractibility on the full small
   pro-etale site of `S`, since the underlying scheme is literally `Spec D`.
3. Restriction to the affine basis is a sheaf equivalence. Lift a basis-site epimorphism
   by the inverse equivalence; it remains an epimorphism. Lift the section using full-site
   weak contractibility, then apply the evaluated counit isomorphism. Counit naturality
   and its inverse identity show that the resulting section maps to the original one.
   No nonempty or nontrivial hypothesis is used, so the same proof covers empty `U`.
-/
theorem exists_weaklyContractible_cover (S : Scheme.{u}) [IsAffine S]
    (U : S.AffineProEt) :
    ∃ (I : Type (u + 1)) (V : I → S.AffineProEt) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ precoverage (S := S) U ∧
      ∀ (i : I) (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
        Epi φ → Function.Surjective (φ.hom.app (op (V i))) := by
  classical
  obtain ⟨D, hD, hAlg, hind, hff, hw⟩ := exists_isWContractibleRing Γ(U.left, ⊤)
  -- The affine comparison isomorphism avoids replacing U by a chosen representative.
  let p : Spec (CommRingCat.of D) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) D)) ≫ U.left.isoSpec.inv
  have hp : proAffineEtale p := by
    apply proAffineEtale.comp_mem
    · exact proAffineEtale_Spec_iff.mpr
        ((RingHom.IndEtale.algebraMap_iff _ _).mpr hind)
    · exact proAffineEtale.of_isAffine _
  let V : S.AffineProEt := mk (p ≫ U.hom) (proAffineEtale.comp_mem _ _ hp U.prop)
  let f : V ⟶ U := MorphismProperty.Over.homMk p
  have : WeaklyEtale p := proAffineEtale_le_weaklyEtale _ hp
  have : Surjective p := by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) D))) :=
      ((flat_and_surjective_SpecMap_iff _).mpr
        (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
    dsimp [p]
    infer_instance
  refine ⟨PUnit.{u + 2}, fun _ ↦ V, fun _ ↦ f, ?_, ?_⟩
  · rw [Presieve.ofArrows_pUnit]
    change (Presieve.singleton f).map
      (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) ∈ Scheme.proetalePrecoverage U.left
    rw [Presieve.map_singleton]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
      (f := p) inferInstance
  · intro i P Q φ hφ
    let := hφ
    apply surjective_evaluation_of_full_site S V
    exact ProEt.isWeaklyContractible_of_iso (R := CommRingCat.of D) (Iso.refl _)

end AlgebraicGeometry.Scheme.AffineProEt
