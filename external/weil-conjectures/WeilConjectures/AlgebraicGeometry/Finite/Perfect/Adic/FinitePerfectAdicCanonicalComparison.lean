/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientDiagram
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicFlatTensorComparison
import Mathlib.RingTheory.Finiteness.Projective

/-! # The canonical quotient diagram as an explicit coefficient complex

Source: Stacks Project, Tag 09C6, the finite-projective quotient comparison;
Modules on Sites, Tags 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

local instance finitePerfectAdicCanonicalComparisonCategory
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    Category.{t + 2} (DerivedCategory (CompletedAdicModules X d)) := inferInstance

private theorem tensorModule_retract
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : ModuleCat.{t} A) [Module.Projective A M] [Module.Finite A M] :
    Nonempty (FinitePerfectAdicCoefficientRetract X d
      ((finitePerfectAdicTensorFunctor X d).obj ((finitePerfectAdicOrdinary X d).obj M))
      (finitePerfectAdicTensorCone X d ((finitePerfectAdicOrdinary X d).obj M))) := by
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let H := finitePerfectAdicOrdinary X d
  let O := finitePerfectAdicTensorFunctor X d
  let F : CompletedAdicModules X d ⥤ CompletedAdicModules X d :=
    Functor.const (Discrete (Fin r)) ⋙ lim
  let f' : ModuleCat.of A (Fin r → A) ⟶ M := ModuleCat.ofHom f
  let g' : M ⟶ ModuleCat.of A (Fin r → A) := ModuleCat.ofHom g
  have hgf : g' ≫ f' = 𝟙 M := by
    apply ModuleCat.hom_ext
    exact hfg
  obtain ⟨e, e₀, he⟩ := finitePerfectAdicFreeTensorCone_comparison X d r
  let i := (O.map (H.map g')) ≫ e.hom
  let p := e.inv ≫ (O.map (H.map f'))
  let i₀ := H.map g' ≫ e₀.hom
  let p₀ := e₀.inv ≫ H.map f'
  have hip : i ≫ p = 𝟙 _ := by
    simp only [i, p, Category.assoc, Iso.hom_inv_id_assoc, ← O.map_comp,
      ← H.map_comp, hgf, H.map_id, O.map_id]
  have hip₀ : i₀ ≫ p₀ = 𝟙 _ := by
    simp only [i₀, p₀, Category.assoc, Iso.hom_inv_id_assoc, ← H.map_comp,
      hgf, H.map_id]
  have hi (n : ℕᵒᵖ) : i₀ ≫ F.map ((finitePerfectAdicCoefficientCone X d).π.app n) =
      (finitePerfectAdicTensorCone X d (H.obj M)).π.app n ≫ i.app n := by
    dsimp only [i₀, i, NatTrans.comp_app]
    rw [Category.assoc, he, ← Category.assoc]
    change (H.map g' ≫ finitePerfectAdicTensorProjection X d _ n.unop) ≫ _ = _
    rw [finitePerfectAdicTensorProjection_naturality, Category.assoc]
    rfl
  have hp (n : ℕᵒᵖ) : p₀ ≫
      (finitePerfectAdicTensorCone X d (H.obj M)).π.app n =
      F.map ((finitePerfectAdicCoefficientCone X d).π.app n) ≫ p.app n := by
    have he' : e₀.inv ≫ (finitePerfectAdicTensorCone X d
        (H.obj (ModuleCat.of A (Fin r → A)))).π.app n =
        F.map ((finitePerfectAdicCoefficientCone X d).π.app n) ≫ e.inv.app n := by
      apply (cancel_epi e₀.hom).1
      simp only [Iso.hom_inv_id_assoc]
      rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    dsimp only [p₀, p, NatTrans.comp_app]
    rw [Category.assoc]
    have hn := finitePerfectAdicTensorProjection_naturality X d (H.map f') n.unop
    change H.map f' ≫ (finitePerfectAdicTensorCone X d (H.obj M)).π.app n =
      (finitePerfectAdicTensorCone X d _).π.app n ≫ (O.map (H.map f')).app n at hn
    rw [hn, ← Category.assoc, he', Category.assoc]
  exact ⟨{ rank := r
           inclusion := i
           projection := p
           splitting := hip
           coneInclusion := i₀
           coneProjection := p₀
           coneSplitting := hip₀
           inclusion_naturality := hi
           projection_naturality := hp }⟩

/-- The canonical algebraic quotient diagram is computed by the corresponding explicit
coefficient complex and its compatible finite-free summands.

Source: Stacks Project, Tag 09C6, the displayed finite-projective quotient calculation;
Modules on Sites, Tags 093J--093M; More on Algebra, Tag 09AW.
(blueprint: lem-weil-pbc-finite-perfect-adic-canonical-comparison).

Proof: form the ordinary completed constant complex and tensor it termwise with the
actual coefficient diagram. Map the coefficient cone under tensor and extend it
along the inverse right unitor; tensor-projection naturality proves that its maps
commute with every differential. Split each finite-projective term P^j from A^r
using Module.Finite.exists_comp_eq_id_of_projective. The finite-free tensor-cone
comparison identifies the image of A^r with the finite power of the coefficient
diagram and its unit cone. Compose the images of the splitting maps with that
diagram isomorphism and its inverse, and do the same at the cone point. Functoriality
proves the two splittings. Naturality of the tensor projections and the finite-free
cone comparison prove the inclusion equation; the inverse comparison proves the
projection equation. Finally each projective term is flat, so the bounded-flat
tensor comparison supplies the derived diagram and cone-point isomorphisms. This
last comparison is a separate named obligation; the explicit construction and all
finite-projective retract equations are proved here. Zero terms, rank zero, and
the zero coefficient ring are included. No limit or Roos assertion is used -/
theorem finitePerfectAdicCanonical_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction d.ideal n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) :
    ∃ (T : ℕᵒᵖ ⥤ CochainComplex (CompletedAdicModules X d) ℤ) (c : Cone T),
      (∀ j : ℤ, Nonempty (FinitePerfectAdicCoefficientRetract X d
        (T ⋙ HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j)
        ((HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j).mapCone c))) ∧
      Nonempty (T ⋙ DerivedCategory.Q ≅
        finitePerfectAdicQuotientDiagram d.ideal L adj (DerivedCategory.Q.obj P) ⋙
          finitePerfectAdicDerivedConstant X A ⋙
            completedAdicDerivedChange X (completedAdicScalar X d)) ∧
      Nonempty (DerivedCategory.Q.obj c.pt ≅
        (completedAdicDerivedChange X (completedAdicScalar X d)).obj
          ((finitePerfectAdicDerivedConstant X A).obj (DerivedCategory.Q.obj P))) := by
  classical
  have hflat (i : ℤ) : Module.Flat A (P.X i) := by
    have := (hP i).1
    infer_instance
  obtain ⟨e, e₀⟩ := finitePerfectAdicFlatTensor_comparison X d L adj P a b ha hb hflat
  refine ⟨finitePerfectAdicTensorComplexDiagram X d P,
    finitePerfectAdicTensorComplexCone X d P, ?_, e, e₀⟩
  intro j
  have := (hP j).1
  have := (hP j).2
  exact tensorModule_retract X d (P.X j)

end AlgebraicGeometry.Scheme
