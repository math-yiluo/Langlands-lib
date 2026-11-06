import Langlands.Geometry.Building.ChamberOrderedInjective
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Descent of unique ordered subgroup factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {G : GroupScheme B} {n : ℕ}
    {H : Fin n → GroupScheme B}

/-- The set of points admitting an ordered factorization through the supplied
subgroup functors. This set is not assumed closed under multiplication. -/
def orderedSubgroupProduct (F : Fin n → SubgroupFunctor G) (U : Over B) :
    Set (U ⟶ G.X) :=
  {g | ∃ x : ∀ r, (F r).carrier U,
    (List.ofFn fun r => (x r : U ⟶ G.X)).prod = g}

/-- Injectivity on all tests makes the represented ordered multiplication
monic. The individual representing maps remain the supplied ones. -/
theorem mono_orderedMultiplication_of_subgroupPoints_injective
    (j : ∀ r, H r ⟶ G) (F : Fin n → SubgroupFunctor G)
    (hH : ∀ r, (F r).IsRepresentedBy (j r))
    (hinj : ∀ T : Over B,
      Function.Injective (fun x : ∀ r, (F r).carrier T =>
        (List.ofFn fun r => (x r : T ⟶ G.X)).prod)) :
    Mono (orderedMultiplication j) := by
  constructor
  intro T x y hxy
  apply (finiteProductPointsEquiv H T).injective
  have htuple :
      (fun r => (hH r).pointsEquiv T (finiteProductPointsEquiv H T x r)) =
        (fun r => (hH r).pointsEquiv T (finiteProductPointsEquiv H T y r)) := by
    apply hinj T
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      comp_orderedMultiplication, orderedPoints] using hxy
  funext r
  exact ((hH r).pointsEquiv T).injective (congrFun htuple r)

private theorem exists_lift_of_comp_eq
    {X Y U V : Over B} (f : X ⟶ Y) [Mono f]
    (q : V ⟶ U) [EffectiveEpi q.left]
    (x : U ⟶ Y) (y : V ⟶ X) (hy : y ≫ f = q ≫ x) :
    ∃ z : U ⟶ X, z ≫ f = x := by
  have hy₀ : y.left ≫ f.left = q.left ≫ x.left :=
    congrArg (fun a => a.left) hy
  let d : U.left ⟶ X.left :=
    EffectiveEpi.desc q.left y.left (fun a a' he => by
      apply (cancel_mono f.left).mp
      simpa only [Category.assoc, hy₀] using
        congrArg (fun z => z ≫ x.left) he)
  have hd : q.left ≫ d = y.left := EffectiveEpi.fac _ _ _
  let z : U ⟶ X := Over.homMk d (by
    apply (cancel_epi q.left).mp
    simp only [← Category.assoc, hd, Over.w y, Over.w q])
  refine ⟨z, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi q.left).mp
  change q.left ≫ (d ≫ f.left) = q.left ≫ x.left
  rw [← Category.assoc, hd, hy₀]

private theorem comp_orderedSubgroupPoints
    (F : Fin n → SubgroupFunctor G) {U V : Over B} (q : V ⟶ U)
    (x : ∀ r, (F r).carrier U) :
    q ≫ (List.ofFn fun r => (x r : U ⟶ G.X)).prod =
      (List.ofFn fun r => q ≫ (x r : U ⟶ G.X)).prod := by
  have key (l : List (U ⟶ G.X)) :
      q ≫ l.prod = (l.map (fun z => q ≫ z)).prod := by
    induction l with
    | nil => simp
    | cons z l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]
  simpa only [List.map_ofFn, Function.comp_def] using
    key (List.ofFn fun r => (x r : U ⟶ G.X))

/-- A factorization after an effective epimorphism descends whenever the
actual represented ordered product is injective on every test. No
surjectivity of multiplication, or descent data on the factors, is supplied. -/
theorem orderedSubgroupFactors_descend
    (j : ∀ r, H r ⟶ G) (F : Fin n → SubgroupFunctor G)
    (hH : ∀ r, (F r).IsRepresentedBy (j r))
    (hinj : ∀ T : Over B,
      Function.Injective (fun x : ∀ r, (F r).carrier T =>
        (List.ofFn fun r => (x r : T ⟶ G.X)).prod))
    {U V : Over B} (q : V ⟶ U) [EffectiveEpi q.left]
    (g : U ⟶ G.X) (y : ∀ r, (F r).carrier V)
    (hy : (List.ofFn fun r => (y r : V ⟶ G.X)).prod = q ≫ g) :
    ∃ x : ∀ r, (F r).carrier U,
      (∀ r, q ≫ (x r : U ⟶ G.X) = (y r : V ⟶ G.X)) ∧
        (List.ofFn fun r => (x r : U ⟶ G.X)).prod = g := by
  let : Mono (orderedMultiplication j) :=
    mono_orderedMultiplication_of_subgroupPoints_injective j F hH hinj
  let y' : V ⟶ (∏ᶜ H).X :=
    (finiteProductPointsEquiv H V).symm
      (fun r => ((hH r).pointsEquiv V).symm (y r))
  have hy' : y' ≫ orderedMultiplication j = q ≫ g := by
    simpa only [y', finiteProductPointsEquiv_symm_orderedMultiplication,
      orderedPoints, SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp] using hy
  obtain ⟨z, hz⟩ := exists_lift_of_comp_eq (orderedMultiplication j) q g y' hy'
  let x : ∀ r, (F r).carrier U :=
    fun r => (hH r).pointsEquiv U (finiteProductPointsEquiv H U z r)
  have hx : (List.ofFn fun r => (x r : U ⟶ G.X)).prod = g := by
    simpa only [x, SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      comp_orderedMultiplication, orderedPoints] using hz
  refine ⟨x, ?_, hx⟩
  let x' : ∀ r, (F r).carrier V :=
    fun r => ⟨q ≫ (x r : U ⟶ G.X), (F r).comp_mem q (x r).property⟩
  have hxy : x' = y := hinj V (by
    change (List.ofFn fun r => q ≫ (x r : U ⟶ G.X)).prod = _
    rw [← comp_orderedSubgroupPoints F q x, hx]
    exact hy.symm)
  intro r
  exact congrArg Subtype.val (congrFun hxy r)

/-- Membership in the actual ordered product set is preserved and reflected
by an effective epimorphism, provided ordered multiplication is injective on
all tests and each supplied subgroup is represented. -/
theorem mem_orderedSubgroupProduct_comp_iff
    (j : ∀ r, H r ⟶ G) (F : Fin n → SubgroupFunctor G)
    (hH : ∀ r, (F r).IsRepresentedBy (j r))
    (hinj : ∀ T : Over B,
      Function.Injective (fun x : ∀ r, (F r).carrier T =>
        (List.ofFn fun r => (x r : T ⟶ G.X)).prod))
    {U V : Over B} (q : V ⟶ U) [EffectiveEpi q.left] (g : U ⟶ G.X) :
    q ≫ g ∈ orderedSubgroupProduct F V ↔ g ∈ orderedSubgroupProduct F U := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, _, hx⟩ := orderedSubgroupFactors_descend j F hH hinj q g y hy
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun r => ⟨q ≫ (x r : U ⟶ G.X), (F r).comp_mem q (x r).property⟩, ?_⟩
    rw [← comp_orderedSubgroupPoints F q x, hx]

end Langlands.GroupScheme.RelativeRoot
