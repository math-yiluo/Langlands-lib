/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparison
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexModel

/-! # Complex presentations of condensed coefficient extension

This is the coefficient algebra step of derived Hom descent. It makes no
constructibility assumption on either the source or the target of a morphism.
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

/-- Source: archived master `ModuleObject/Colimit/TwoColimit.lean`, the Hom paragraph
of the module docstring; the coefficient complex construction in step 3 of
`prop-weil-pbc-qbar-condensed-two-colimit`.
(auxiliary; not a blueprint node)

Proof: represent the bounded-below object `L` by a complex `C` zero below an integer
`a`, using the standard derived t-structure. At index `i`, extend `C` termwise from
`F` to `H.obj i`, then restrict the resulting complex to `E`. A transition map is
induced by the coefficient inclusion, tensor the identity of `C`; its `E`-linearity
follows from the equality of the two coefficient inclusions. Tensor functoriality
proves identities, composition, and the cocone equations. The vertex is the same
construction with the finite-subfield-valued condensed algebraic closure.

The finite coefficient rings have this closure as their colimit, also after the
final functor `H` and after pullback to the scheme. Balanced tensor preserves this
colimit: write it as the coequalizer of the two action maps, use preservation by
ordinary tensor, and commute colimits. Forgetting the `E` action creates colimits,
so this gives the module colimit in every degree. Colimits of complexes are
computed degreewise, giving `IsColimit c`. All terms below `a` are zero because
extension and restriction are additive.

Exactness of these coefficient extensions identifies the total derived functors
with the termwise functors. Together with the representative isomorphism for `L`
this gives `eΩ` and every `ei`. For the displayed equation, first check the
underived extension/restriction adjunction: both sides take a section `m` to
`1 ⊗ m` followed by the same coefficient inclusion and tensor multiplication.
This is an equality of natural transformations of complexes, not a choice of
bijections. Localize it and use the defining factorization equations of
`leftDerivedFunctorCompIso` and `leftDerivedFunctorNatIso`; the resulting
comparisons are precisely `derivedExtendScalarsCompIso`. Naturality
then gives the equation for every derived `K` and every `g`.

Edge cases: the zero complex and the empty scheme give zero cocones; no
nonzero-source or bounded-above hypothesis is used. -/
theorem exists_condensed_coefficient_complex_presentation
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : FiniteIntermediateField ℓ)
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)))
    (hL : DerivedCategory.TStructure.t.plus L)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ FiniteIntermediateField ℓ) [H.Final]
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    ∃ N : I ⥤ CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ,
      ∃ c : Cocone N, Nonempty (IsColimit c) ∧
      (∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)) ∧
      ∃ eΩ : DerivedCategory.Q.obj c.pt ≅
          (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
            ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj L),
        ∃ ei : ∀ i : I, DerivedCategory.Q.obj (N.obj i) ≅
            (finiteCoefficientDerivedRestriction X ℓ (he i)).obj
              ((derivedExtendScalarsSubfield X ℓ (hf i)).obj L),
          ∀ (i : I) (K : DerivedCategory
              (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
            (g : K ⟶ DerivedCategory.Q.obj (N.obj i)),
            finiteCoefficientDerivedAlgClHomEquiv X ℓ E K _
              ((derivedExtendScalarsCompIso X ℓ (he i)).inv.app K ≫
                (derivedExtendScalarsToPadicAlgCl X ℓ (H.obj i)).map
                    ((finiteCoefficientDerivedHomEquiv X ℓ (he i) K _).symm
                        (g ≫ (ei i).hom)) ≫
                  (derivedExtendScalarsCompIso X ℓ (hf i)).hom.app L) =
              g ≫ DerivedCategory.Q.map (c.ι.app i) ≫ eΩ.hom := by
  -- Keep the existential eliminators explicit: nested `obtain` unfolds the large target.
  refine hL.elim fun a ha ↦ ?_
  have : L.IsGE a := ha
  refine (DerivedCategory.exists_iso_Q_obj_of_isGE L a).elim fun C hC ↦ ?_
  refine hC.elim fun hC heC ↦ ?_
  refine heC.elim fun e ↦ ?_
  refine (exists_condensed_coefficient_complex_model X ℓ E F C H he hf).elim fun N hN ↦ ?_
  refine hN.elim fun c hc ↦ ?_
  have hN := hc.2.1
  have hrest := hc.2.2
  have hc := hc.1
  refine hrest.elim fun eΩ hrest ↦ ?_
  refine hrest.elim fun ei hcomp ↦ ?_
  have hbound : ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r) := by
    intro i r hr
    rw [hN i]
    exact (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hf i))) ⋙
      Mod.comap (padicSubfieldRingObjMap X ℓ (he i)))).map_isZero
        (C.isZero_of_isStrictlyGE a r hr)
  let eΩ' := eΩ ≪≫ (finiteCoefficientDerivedFromAlgCl X ℓ E).mapIso
    ((derivedExtendScalarsToPadicAlgCl X ℓ F).mapIso e.symm)
  let ei' := fun i ↦ ei i ≪≫ (finiteCoefficientDerivedRestriction X ℓ (he i)).mapIso
    ((derivedExtendScalarsSubfield X ℓ (hf i)).mapIso e.symm)
  refine ⟨N, c, hc, ⟨a, hbound⟩, eΩ', ei', ?_⟩
  intro i K g
  -- Establish source and target naturality before instantiating the derived module categories.
  have transport {A B D T : Type _} [Category A] [Category B] [Category D] [Category T]
      {P : A ⥤ D} {UP : D ⥤ A} (ap : P ⊣ UP)
      {R : D ⥤ T} {S : A ⥤ T} {US : T ⥤ A} (aq : S ⊣ US)
      {V : B ⥤ D} {W : B ⥤ T} (α : P ⋙ R ≅ S) (β : V ⋙ R ≅ W)
      {L₀ L₁ : B} (f : L₀ ⟶ L₁) {K₀ K₁ : A}
      (k : K₁ ⟶ K₀) (g : K₀ ⟶ UP.obj (V.obj L₀)) :
      aq.homEquiv K₁ _
        (α.inv.app K₁ ≫ R.map ((ap.homEquiv K₁ _).symm
          ((k ≫ g) ≫ UP.map (V.map f))) ≫
          β.hom.app L₁) =
      k ≫ aq.homEquiv K₀ _ (α.inv.app K₀ ≫ R.map ((ap.homEquiv K₀ _).symm g) ≫
        β.hom.app L₀) ≫ US.map (W.map f) := by
    rw [ap.homEquiv_naturality_right_symm, ap.homEquiv_naturality_left_symm]
    simp only [R.map_comp, Category.assoc]
    have hb := β.hom.naturality f
    change R.map (V.map f) ≫ β.hom.app L₁ = β.hom.app L₀ ≫ W.map f at hb
    rw [hb]
    have ha := α.inv.naturality k
    change S.map k ≫ α.inv.app K₀ = α.inv.app K₁ ≫ R.map (P.map k) at ha
    rw [← reassoc_of% ha, aq.homEquiv_naturality_left]
    simpa only [Category.assoc] using congrArg (fun q ↦ k ≫ q)
      (aq.homEquiv_naturality_right
        (α.inv.app K₀ ≫ R.map ((ap.homEquiv K₀ _).symm g) ≫ β.hom.app L₀) (W.map f))
  have ht := transport (finiteCoefficientDerivedAdjunction X ℓ (he i))
    (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
    (derivedExtendScalarsCompIso X ℓ (he i))
    (derivedExtendScalarsCompIso X ℓ (hf i)) e.inv g (ei i).hom
  have hcompat := hcomp i
  simp only [finiteCoefficientDerivedHomEquiv, finiteCoefficientDerivedAlgClHomEquiv] at hcompat
  simp only [Category.assoc] at ht
  simp only [ei', eΩ', Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    finiteCoefficientDerivedHomEquiv, finiteCoefficientDerivedAlgClHomEquiv]
  refine ht.trans ?_
  simpa only [Category.assoc] using congrArg
    (fun f ↦ g ≫ f ≫ (finiteCoefficientDerivedFromAlgCl X ℓ E).map
      ((derivedExtendScalarsToPadicAlgCl X ℓ F).map e.inv)) hcompat

end AlgebraicGeometry.ProEtale
