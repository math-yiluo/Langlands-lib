import Langlands.GroupScheme.Reductive.TorusGenerationStatement
import Langlands.GroupScheme.ImageGenerationStatement
import Langlands.GroupScheme.ImageGenerationProducts
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.Torus.GeometricallyIntegral
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Torus.Geometry

/-! # Torus domination from finite torus generation and pointed-image generation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an infinite field `k`, every connected reductive group scheme `G` admits a torus `P`,
a natural number `n` and a morphism of `k`-schemes from the `n`-fold fibre power of `P.X` to
`G.X`, not necessarily a homomorphism, whose image is Zariski dense in `G`. -/
def ReductiveTorusPowerDominationStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ) (g : finitePower P.X n ⟶ G.X),
      IsTorus P ∧ Dense (Set.range g.left)

/-- An ordered product in a monoid in which every factor but the `j`-th is `1`. -/
theorem prod_ofFn_eq_of_eq_one {M : Type*} [Monoid M] {m : ℕ} (g : Fin m → M) (j : Fin m)
    (h : ∀ i, i ≠ j → g i = 1) : (List.ofFn g).prod = g j := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases j using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      exact List.forall_mem_ofFn_iff.2 fun i => h _ (Fin.succ_ne_zero i)
    | succ j =>
      rw [h 0 (Fin.succ_ne_zero j).symm, one_mul]
      exact ih (fun i => g i.succ) j fun i hi => h _ fun e => hi (Fin.succ_injective _ e)

/-- Precomposition with a morphism of the test object commutes with ordered products of points
of a monoid object. -/
theorem comp_list_prod {B : Scheme.{u}} {T W M : Over B} [MonObj M] (a : T ⟶ W)
    (l : List (W ⟶ M)) : a ≫ l.prod = (l.map (a ≫ ·)).prod := by
  induction l with
  | nil => exact MonObj.comp_one a
  | cons x l ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

/-- Finite generation of a connected reductive group by closed tori, together with
pointed-image generation, gives a dense ordered product map from a finite power of a torus. -/
theorem reductiveTorusPowerDomination_of_generation
    (hGen : ReductiveFiniteTorusGenerationStatement.{u})
    (hPIG : PointedImageGenerationStatement.{u}) :
    ReductiveTorusPowerDominationStatement.{u} := by
  intro k _ _ G hG
  obtain ⟨m, T, e, hT, he, hgen⟩ := hGen k G hG
  have := hG.isAffineHom
  let T' : ULift.{u} (Fin m) → GroupScheme (Spec (CommRingCat.of k)) := fun j => T j.down
  let P : GroupScheme (Spec (CommRingCat.of k)) := pi T'
  have hP : IsTorus P := IsTorus.pi T' fun j => hT j.down
  let π' : ∀ j : Fin m, P.X ⟶ (T j).X := fun j => (Pi.π T' ⟨j⟩).hom.hom
  let f : P.X ⟶ G.X := (List.ofFn fun j : Fin m => π' j ≫ (e j).hom.hom).prod
  have hAff : IsAffineHom P.X.hom := by
    have : MorphismProperty.IsStableUnderComposition
        (@IsAffineHom : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have : MorphismProperty.ContainsIdentities (@IsAffineHom : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have : MorphismProperty.RespectsIso (@IsAffineHom : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine prop_pi_hom (@IsAffineHom : MorphismProperty Scheme.{u}) T' fun j => ?_
    have : IsClosedImmersion (e j.down).hom.hom.left := he j.down
    change IsAffineHom (T j.down).X.hom
    rw [← Over.w (e j.down).hom.hom]
    infer_instance
  have hLFT : LocallyOfFiniteType P.X.hom := by
    have := hP.smooth
    infer_instance
  have hv₀ : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ f = 1 := by
    rw [comp_list_prod, List.map_ofFn]
    refine List.prod_eq_one (List.forall_mem_ofFn_iff.2 fun j => ?_)
    simp only [Function.comp_apply, π', MonObj.one_comp]
  obtain ⟨D, -, -, -, n, -, hdom⟩ :=
    hPIG k G hG.smooth hG.isAffineHom P.X hAff hLFT hP.geometricallyIntegral 1 f hv₀
  let s : ∀ j : Fin m, (T j).X ⟶ P.X := fun j =>
    (piPointsEquiv T' (T j).X).symm
      (Pi.mulSingle (M := fun i : ULift.{u} (Fin m) => (T j).X ⟶ (T' i).X) ⟨j⟩ (𝟙 (T j).X))
  have hs : ∀ j, s j ≫ f = (e j).hom.hom := by
    intro j
    rw [comp_list_prod, List.map_ofFn, prod_ofFn_eq_of_eq_one _ j]
    · simp only [Function.comp_apply, π', s, ← Category.assoc, piPointsEquiv_symm_π,
        Pi.mulSingle_eq_same, Category.id_comp]
    · intro i hi
      have hne : (⟨i⟩ : ULift.{u} (Fin m)) ≠ ⟨j⟩ := fun e => hi (congrArg ULift.down e)
      simp only [Function.comp_apply, π', s, ← Category.assoc, piPointsEquiv_symm_π,
        Pi.mulSingle_eq_of_ne hne, MonObj.one_comp]
  have hfac : ∀ j, FactorsThrough (e j).hom.hom D.inclusion := fun j =>
    ⟨s j ≫ D.factor, by rw [Category.assoc, D.factor_comp, hs j]⟩
  have htop := hgen D.group D.inclusion D.closed hfac
  obtain ⟨r, hr⟩ : ∃ r : G.X ⟶ D.group.X, r ≫ D.inclusion.hom.hom = 𝟙 G.X :=
    SubgroupFunctor.mem_range.1 (by rw [htop]; exact Subgroup.mem_top _)
  have hsurj : Function.Surjective D.inclusion.hom.hom.left := fun x =>
    ⟨r.left x, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hr]; rfl⟩
  refine ⟨P, n, orderedPowerMap f n, hP, ?_⟩
  have hd := hsurj.denseRange.comp hdom.denseRange D.inclusion.hom.hom.left.continuous
  rw [← D.powerMap_comp, Over.comp_left]
  have hfun : ⇑((D.powerMap n).left ≫ D.inclusion.hom.hom.left) =
      ⇑D.inclusion.hom.hom.left ∘ ⇑(D.powerMap n).left :=
    funext fun x => Scheme.Hom.comp_apply _ _ x
  rw [hfun]
  exact hd

end Langlands.GroupScheme
