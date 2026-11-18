import Langlands.GroupScheme.OuterIsomorphismGeometry
import Langlands.GroupScheme.SchemeActionParameterSection
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeBaseChange

/-! # Local quotient parameters are determined by normalized orbit families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- The class map with an extra scheme parameter has exactly the original
orbit kernel, retaining the extra parameter. -/
theorem parameterMap_eq_iff (U : Over S) {T : Over S}
    (p p' : T ⟶ I.parameter ⨯ U) :
    p ≫ prod.map O.classMap (𝟙 U) = p' ≫ prod.map O.classMap (𝟙 U) ↔
      p ≫ prod.snd = p' ≫ prod.snd ∧
        ∃ d : T ⟶ A.X,
          lift d (p ≫ prod.fst) ≫ I.actionHom a = p' ≫ prod.fst := by
  constructor
  · intro h
    have hc := congrArg (fun f => f ≫ prod.fst) h
    have ht := congrArg (fun f => f ≫ prod.snd) h
    simp only [Category.assoc, prod.map_fst] at hc
    simp only [Category.assoc, prod.map_snd, Category.comp_id] at ht
    exact ⟨ht, (O.orbit T (p ≫ prod.fst) (p' ≫ prod.fst) hc).exists⟩
  · rintro ⟨ht, d, hd⟩
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst]
      simpa only [Category.assoc] using
        ((O.invariant T d (p ≫ prod.fst)).symm.trans
          (congrArg (fun f => f ≫ O.classMap) hd))
    · simpa only [Category.assoc, prod.map_snd, Category.comp_id] using ht

/-- Any complete local normalized family identifies its parameter with the
product of the outer parameter and the local base. -/
theorem exists_parameterSectionIso
    [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom]
    {U M : Over S} (π : M ⟶ U) (s : M ⟶ I.parameter)
    (h : ∀ (T : Over S), Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ M) =>
        prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a) (z.2 ≫ π)))
    (hclassMap : LocallyOfFinitePresentation O.classMap.left := O.locallyOfFinitePresentation) :
    ∃ e : M ≅ O.parameter ⨯ U, e.hom ≫ prod.snd = π := by
  let b : SchemeAction A I.parameter := I.modObj a
  let q := b.parameterSectionClassMap π s h
  let c : I.parameter ⨯ U ⟶ O.parameter ⨯ U := prod.map O.classMap (𝟙 U)
  have hpb := (IsPullback.of_prod_fst_with_id O.classMap U).map (Over.forget S)
  let : Flat c.left := MorphismProperty.of_isPullback (P := @Flat) hpb O.flat
  let : Surjective c.left := MorphismProperty.of_isPullback (P := @Surjective) hpb O.surjective
  let : LocallyOfFinitePresentation c.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb hclassMap
  let : Flat q.left := b.parameterSectionClassMap_flat π s h
  let : Surjective q.left := b.parameterSectionClassMap_surjective π s h
  let : LocallyOfFinitePresentation q.left :=
    b.parameterSectionClassMap_locallyOfFinitePresentation π s h
  obtain ⟨e, he⟩ := exists_iso_of_locallySurjective_of_same_kernel
    (F := (schemeSheaf S).obj (O.parameter ⨯ U)) ((schemeYoneda S).map c) q
    (isLocallySurjective_schemeYoneda_map c) (isLocallySurjective_schemeYoneda_map q)
    (fun T p p' => by
      change (ULift.up (p ≫ c) : ULift.{u + 1} _) = ULift.up (p' ≫ c) ↔ p ≫ q = p' ≫ q
      rw [ULift.up_inj]
      exact (O.parameterMap_eq_iff U p p').trans
        (b.parameterSectionClassMap_eq_iff π s h p p').symm)
  let d : M ≅ O.parameter ⨯ U := (ULiftYoneda.fullyFaithful (Over S)).preimageIso e
  have hd : (schemeYoneda S).map d.hom = e.hom :=
    (ULiftYoneda.fullyFaithful (Over S)).map_preimage _
  have hqd : q ≫ d.hom = c := by
    apply (schemeYoneda S).map_injective
    rw [Functor.map_comp, hd, he]
  let : Sheaf.IsLocallySurjective ((schemeSheaf S).map q) :=
    isLocallySurjective_schemeYoneda_map q
  let : Epi q := (schemeSheaf S).epi_of_epi_map inferInstance
  refine ⟨d, (cancel_epi q).mp ?_⟩
  rw [← Category.assoc, hqd]
  exact (prod.map_snd _ _).trans (b.parameterSectionClassMap_comp π s h).symm

/-- The same local parameter comparison is an actual isomorphism over the
local base, with the outer parameter pulled back along its structure map. -/
theorem exists_localParameterIso
    [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom]
    {U M : Over S} (π : M ⟶ U) (s : M ⟶ I.parameter)
    (h : ∀ (T : Over S), Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ M) =>
        prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a) (z.2 ≫ π)))
    (hclassMap : LocallyOfFinitePresentation O.classMap.left := O.locallyOfFinitePresentation) :
    Nonempty ((Over.pullback U.hom).obj O.parameter ≅ Over.mk π.left) := by
  obtain ⟨e, he⟩ := O.exists_parameterSectionIso π s h hclassMap
  let hpb := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst : O.parameter ⨯ U ⟶ O.parameter) prod.snd)
    (prodIsProd O.parameter U)
  let d : M.left ≅ pullback O.parameter.hom U.hom :=
    (Over.forget S).mapIso e ≪≫ hpb.isoPullback
  refine ⟨(Over.isoMk d ?_).symm⟩
  change d.hom ≫ pullback.snd O.parameter.hom U.hom = π.left
  dsimp only [d, Iso.trans_hom]
  rw [Category.assoc, hpb.isoPullback_hom_snd]
  exact congrArg (fun f => f.left) he

/-- Select the actual local parameter comparison determined by a complete
normalized orbit family. -/
def localParameterIso
    [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom]
    {U M : Over S} (π : M ⟶ U) (s : M ⟶ I.parameter)
    (h : ∀ (T : Over S), Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ M) =>
        prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a) (z.2 ≫ π))) :
    (Over.pullback U.hom).obj O.parameter ≅ Over.mk π.left :=
  Classical.choice (O.exists_localParameterIso π s h)

end Langlands.GroupScheme.OuterIsomorphismScheme
