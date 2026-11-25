/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoOrdinaryComparison

/-! # Transport of base-derived tensor models along quasi-isomorphisms

Source: Stacks Project, More on Algebra, Tags 06Y6 and 08IB.
(blueprint: lem-pc-base-derived-tensor-model-quasiiso-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory
open scoped ChangeOfRings
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Transport the tensor-algebra cohomology and its localized counit comparison.

Proof: restriction of scalars preserves homology, so the restricted quasi-isomorphism
is invertible in D(R). The universal left-derived property identifies the derived
functors of the two models by a unique natural isomorphism compatible with their
counits. Apply cohomology to the restricted map and this isomorphism, and conjugate
by the two cohomologyIso maps. This is a B-linear isomorphism. Naturality for the
endomorphism a times the identity, together with cohomologyIso_smul, says that it
commutes with multiplication by a tensor 1. B-linearity says the same for 1 tensor b.
Tensor induction then makes it A-tensor-R-B-linear; its inverse is linear too.
Call the resulting isomorphism e. Naturality of the universal counits and the
homology comparison isomorphisms gives the ordinary comparison square using
comparison_eq. The ordinaryIso generator equations identify their conjugated
termwise maps: both send b tensor q to (1 tensor b) tensor s(q).
The ordinaryToLocalized generator equations similarly give a commuting chain-map
square: both routes send t tensor q to the image of t tensor s(q). Apply homology
and compose with the ordinary comparison square. Finally transpose along the
extension/restriction adjunction. Naturality of its unit and localized_eq identify
the two transposes, hence give the asserted localized square. This does not claim
that ordinary extension of the quasi-isomorphism is invertible.
Source: Stacks Project, Tags 06Y6 and 08IB, and perfect.tex, equation-bc before Tag 0DJ8.
(blueprint: lem-pc-base-derived-tensor-model-quasiiso-comparison). -/
theorem exists_baseDerivedTensorModel_quasiIso_comparison
    {P G : CochainComplex (ModuleCat.{u} A) ℤ} (s : P ⟶ G) (hs : QuasiIso s)
    (MP : BaseDerivedTensorCohomologyModel R A B P D)
    (MG : BaseDerivedTensorCohomologyModel R A B G D) (i : ℤ) :
    ∃ e : MP.cohomology i ≅ MG.cohomology i,
      MP.localizedComparison i ≫ HomologicalComplex.homologyMap
        (((extendScalars ((algebraMap (A ⊗[R] B) D).comp
          (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).map s) i =
      (extendScalars (algebraMap (A ⊗[R] B) D)).map e.hom ≫
        MG.localizedComparison i := by
  obtain ⟨e, he⟩ := exists_baseDerivedTensorModel_quasiIso_ordinary_comparison
    R A B D s hs MP MG i
  let F := extendScalars (algebraMap A (A ⊗[R] B))
  let H := extendScalars ((algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)))
  let U := restrictScalars (algebraMap (A ⊗[R] B) D)
  let t := (H.mapHomologicalComplex (.up ℤ)).map s
  have hchain : (F.mapHomologicalComplex (.up ℤ)).map s ≫ MG.ordinaryToLocalized =
      MP.ordinaryToLocalized ≫ (U.mapHomologicalComplex (.up ℤ)).map t := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ExtendScalars.hom_ext
    intro q
    change MG.ordinaryToLocalized.f j
        (F.map (s.f j) ((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] q)) =
      U.map (H.map (s.f j)) (MP.ordinaryToLocalized.f j
        ((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] q))
    rw [ExtendScalars.map_tmul, MG.ordinaryToLocalized_tmul,
      MP.ordinaryToLocalized_tmul]
    change (algebraMap (A ⊗[R] B) D 1 ⊗ₜ[A,
        (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] (s.f j) q) =
      H.map (s.f j) (algebraMap (A ⊗[R] B) D 1 ⊗ₜ[A,
        (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] q)
    exact (ExtendScalars.map_tmul _ _ _ _).symm
  have hhom := congrArg (fun a => HomologicalComplex.homologyMap a i) hchain
  simp only [HomologicalComplex.homologyMap_comp] at hhom
  let JP := ((H.mapHomologicalComplex (.up ℤ)).obj P).sc i |>.mapHomologyIso U
  let JG := ((H.mapHomologicalComplex (.up ℤ)).obj G).sc i |>.mapHomologyIso U
  have hJ : HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (.up ℤ)).map t) i ≫ JG.hom =
      JP.hom ≫ U.map (HomologicalComplex.homologyMap t i) := by
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map t) U
  let adj := extendRestrictScalarsAdj (algebraMap (A ⊗[R] B) D)
  refine ⟨e, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, MP.localized_eq, MG.localized_eq]
  change (MP.comparison i ≫ HomologicalComplex.homologyMap MP.ordinaryToLocalized i ≫
      JP.hom) ≫ U.map (HomologicalComplex.homologyMap t i) =
    e.hom ≫ MG.comparison i ≫ HomologicalComplex.homologyMap MG.ordinaryToLocalized i ≫
      JG.hom
  rw [Category.assoc, Category.assoc, ← hJ]
  calc
    _ = (MP.comparison i ≫ HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map s) i) ≫
        HomologicalComplex.homologyMap MG.ordinaryToLocalized i ≫ JG.hom := by
      simpa only [Category.assoc] using
        congrArg (fun a => MP.comparison i ≫ a ≫ JG.hom) hhom.symm
    _ = _ := by rw [he, Category.assoc]

end ModuleCat
