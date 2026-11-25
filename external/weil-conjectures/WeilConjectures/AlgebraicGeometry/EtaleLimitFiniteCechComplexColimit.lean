/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteCechStageData
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteCechColimit

set_option linter.unusedVariables false

/-! # Finite Čech complexes on inverse limits of schemes

Source: Stacks Project, Tags 09YP, 09YN and 09YQ.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-complex-colimit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks


/-- A finite qcqs étale covering has a Čech complex computed by stage Čech complexes.
Source: Stacks Project, proof of Tag 09YP, the displayed equality of Čech complexes;
Tag 09YN supplies degree-zero continuity, and 09YQ supplies the scheme-site realization.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-complex-colimit).

Proof: Descend the qcqs étale object U and the finitely many qcqs covering objects
and arrows to a common stage. These étale morphisms have finite presentation because
source and base are qcqs. Descend the jointly surjective finite family, increasing the
stage if necessary. On the directed tail, pull back the descended covering to obtain
Uj, Vj and fj. Base change preserves étaleness and the covering property. Iterated
fibre products of these objects give the stage nerves; their pullbacks to the limit
are the nerve of the given covering, by uniqueness of fibre products. On each nerve
object apply degree-zero section continuity for the compatible coefficient system.
Its maps are the adjunction units followed by the coefficient transitions, so they
commute with every face projection. Taking the finite product over tuples of cover
indices therefore defines the stage complex diagram A and a cocone into the limit
Čech complex. Naturality commutes with the alternating differentials. Filtered
colimits of abelian groups commute with these finite products, so the cocone is
colimiting in every degree and hence in complexes. The stage complexes are identified
by the fibre-product comparisons, giving eA; their colimit is identified with the
original nerve complex, giving eK. No injectivity or positive-degree cohomological
continuity is used. The empty covering only covers an empty object and gives zero
complexes; a singleton index and the zero coefficient system satisfy the same construction.
The displayed existential is a theorem about complexes; it is not used to define
any coefficient sheaf or other object of the library. -/
theorem etale_limit_finite_cech_complex_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U) :
    ∃ (i₀ : I) (A : {j : I // i₀ ≤ j} ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (Uj : ∀ j : {j : I // i₀ ≤ j}, (D.obj (op j.val)).Etale)
      (Vj : ∀ j : {j : I // i₀ ≤ j}, K → (D.obj (op j.val)).Etale)
      (fj : ∀ (j : {j : I // i₀ ≤ j}) (k : K), Vj j k ⟶ Uj j)
      (eA : ∀ j : {j : I // i₀ ≤ j}, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj)),
      (∀ j : {j : I // i₀ ≤ j},
        Sieve.ofArrows (Vj j) (fj j) ∈ (D.obj (op j.val)).smallEtaleTopology (Uj j)) ∧
      Nonempty (IsColimit cA) := by
  obtain ⟨i₀, U₀, V₀, f₀, eU, eV, A, eA, cA, eK, eNj, eNlim, γ, δ, hdata⟩ :=
    exists_etale_limit_finite_cech_stage_data D c hc F φ hidentity
      hcomposition G eG hG L hL U K V f hV hf
  let B := fun j : {j : I // i₀ ≤ j} ↦
    MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
  have hcol := finite_cech_stage_data_is_colimit D c hc F φ hidentity
    hcomposition G eG hG L hL U K V f hV hf i₀ U₀ V₀ f₀ eU eV
    A eA cA eK eNj eNlim γ δ hdata
  exact ⟨i₀, A, (fun j ↦ (B j).obj U₀), (fun j k ↦ (B j).obj (V₀ k)),
    (fun j k ↦ (B j).map (f₀ k)), eA, cA, eK, hdata.2.2.2.1, hcol⟩

end AlgebraicGeometry.Etale
