import Langlands.Cohomology.HyperextExtBaseChange

/-!
# Extension of scalars on `Ext` groups: direct summands of finite sums

The dimension-shifting theorems of `Langlands.Cohomology.HyperextExtBaseChange` apply to
resolutions by objects of a class `Q` of projective objects `P` with `F P` projective and
`S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective. This module shows that these three conditions pass
from `Q` to the direct summands of finite direct sums of objects of `Q`, so that the theorems apply
to resolutions by such summands. For representations of a monoid `G`, this applies to the
summands of finite sums of representations free of finite rank over `R[G]`.

* `IsSummandOfFiniteSum Q X`: there are finitely many objects `P i` satisfying `Q` and morphisms
  `a i : X ⟶ P i`, `b i : P i ⟶ X` with `∑ i, a i ≫ b i = 𝟙 X`;
  `IsSummandOfFiniteSum.of_prop`, `isSummandOfFiniteSum_of_isZero`, `IsSummandOfFiniteSum.mono`,
  `IsSummandOfFiniteSum.of_retract`, `IsSummandOfFiniteSum.biproduct` and
  `IsSummandOfFiniteSum.hasResolutionBy`.
* `projective_of_sum_comp_eq_id`, `IsSummandOfFiniteSum.projective`,
  `IsSummandOfFiniteSum.projective_map`: projectivity.
* `sum_mk₀_comp_mk₀_comp_eq_self`, `extBaseChangeMap_injective_of_sum_comp_eq_id`,
  `extBaseChangeMap_surjective_of_sum_comp_eq_id`, `IsSummandOfFiniteSum.extBaseChangeMap_bijective`:
  the comparison map `S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)` of a summand `X`, in every degree.
* `extBaseChangeMap_injective_of_hasResolutionBy_summand`,
  `extBaseChangeMap_bijective_of_hasResolutionBy_summand` and
  `extBaseChangeEquivOfHasResolutionBySummand`: dimension shifting with resolutions by summands.
* `repExtBaseChangeMap_injective_of_hasResolutionBy_summand`,
  `repExtBaseChangeMap_bijective_of_hasResolutionBy_summand` and
  `repExtBaseChangeEquivOfHasResolutionBySummand`: the case of representations, with resolutions
  by summands of finite sums of representations free of finite rank over `R[G]`.

The existence of the resolutions remains a hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

universe w uR uS uG uC vC uD vD t t'

namespace HyperextScalarExtension

section Summand

variable {C : Type uC} [Category.{vC} C] [Preadditive C]

/-- `IsSummandOfFiniteSum Q X`: `X` is a direct summand of a finite direct sum of objects
satisfying `Q`. That is, there are a finite type `ι`, objects `P i` satisfying `Q` and morphisms
`a i : X ⟶ P i`, `b i : P i ⟶ X` with `∑ i, a i ≫ b i = 𝟙 X`. In a category with finite
biproducts this says that `X` is a retract of the biproduct `⨁ P`. -/
def IsSummandOfFiniteSum (Q : C → Prop) (X : C) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (P : ι → C) (a : ∀ i, X ⟶ P i) (b : ∀ i, P i ⟶ X),
    (∀ i, Q (P i)) ∧ ∑ i, a i ≫ b i = 𝟙 X

variable {Q Q' : C → Prop}

/-- An object satisfying `Q` is a summand of a finite sum of objects satisfying `Q`. -/
theorem IsSummandOfFiniteSum.of_prop {X : C} (hX : Q X) : IsSummandOfFiniteSum Q X :=
  ⟨Unit, inferInstance, fun _ => X, fun _ => 𝟙 X, fun _ => 𝟙 X, fun _ => hX, by simp⟩

/-- A zero object is the summand of the empty sum. -/
theorem isSummandOfFiniteSum_of_isZero {X : C} (hX : IsZero X) : IsSummandOfFiniteSum Q X :=
  ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim,
    hX.eq_of_src _ _⟩

/-- Summands of finite sums of objects satisfying `Q` are summands of finite sums of objects
satisfying any weaker `Q'`. -/
theorem IsSummandOfFiniteSum.mono (h : ∀ P, Q P → Q' P) {X : C}
    (hX : IsSummandOfFiniteSum Q X) : IsSummandOfFiniteSum Q' X := by
  obtain ⟨ι, _, P, a, b, hP, hab⟩ := hX
  exact ⟨ι, inferInstance, P, a, b, fun i => h _ (hP i), hab⟩

/-- A retract of a summand of a finite sum of objects satisfying `Q` is again such a summand. -/
theorem IsSummandOfFiniteSum.of_retract {X Y : C} (r : Retract X Y)
    (hY : IsSummandOfFiniteSum Q Y) : IsSummandOfFiniteSum Q X := by
  obtain ⟨ι, _, P, a, b, hP, hab⟩ := hY
  refine ⟨ι, inferInstance, P, fun i => r.i ≫ a i, fun i => b i ≫ r.r, hP, ?_⟩
  calc ∑ i, (r.i ≫ a i) ≫ b i ≫ r.r = r.i ≫ (∑ i, a i ≫ b i) ≫ r.r := by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 𝟙 X := by rw [hab, Category.id_comp, r.retract]

/-- A finite biproduct of summands of finite sums of objects satisfying `Q` is again such a
summand. -/
theorem IsSummandOfFiniteSum.biproduct {J : Type} [Fintype J] (X : J → C) [HasBiproduct X]
    (hX : ∀ j, IsSummandOfFiniteSum Q (X j)) : IsSummandOfFiniteSum Q (⨁ X) := by
  choose ι hι P a b hP hab using hX
  let _ : ∀ j, Fintype (ι j) := hι
  refine ⟨Σ j, ι j, inferInstance, fun k => P k.1 k.2,
    fun k => biproduct.π X k.1 ≫ a k.1 k.2, fun k => b k.1 k.2 ≫ biproduct.ι X k.1,
    fun k => hP k.1 k.2, ?_⟩
  rw [Fintype.sum_sigma]
  calc ∑ j, ∑ i, (biproduct.π X j ≫ a j i) ≫ b j i ≫ biproduct.ι X j
      = ∑ j, biproduct.π X j ≫ (∑ i, a j i ≫ b j i) ≫ biproduct.ι X j := by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 𝟙 (⨁ X) := by simp only [hab, Category.id_comp, biproduct.total]

/-- A summand of a finite sum of projective objects is projective. -/
theorem projective_of_sum_comp_eq_id {X : C} {ι : Type*} [Fintype ι] {P : ι → C}
    (a : ∀ i, X ⟶ P i) (b : ∀ i, P i ⟶ X) (hab : ∑ i, a i ≫ b i = 𝟙 X)
    (hP : ∀ i, Projective (P i)) : Projective X where
  factors {E Z} f e _ := by
    choose l hl using fun i => (hP i).factors (b i ≫ f) e
    refine ⟨∑ i, a i ≫ l i, ?_⟩
    calc (∑ i, a i ≫ l i) ≫ e = (∑ i, a i ≫ b i) ≫ f := by
          simp only [Preadditive.sum_comp, Category.assoc, hl]
      _ = f := by rw [hab, Category.id_comp]

/-- If all objects satisfying `Q` are projective, so are the summands of their finite sums. -/
theorem IsSummandOfFiniteSum.projective (hproj : ∀ P, Q P → Projective P) {X : C}
    (hX : IsSummandOfFiniteSum Q X) : Projective X := by
  obtain ⟨ι, _, P, a, b, hP, hab⟩ := hX
  exact projective_of_sum_comp_eq_id a b hab fun i => hproj _ (hP i)

/-- Let `F` be an additive functor. If `F P` is projective for all objects `P` satisfying `Q`,
then `F X` is projective for every summand `X` of a finite sum of such objects. -/
theorem IsSummandOfFiniteSum.projective_map {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (hFproj : ∀ P, Q P → Projective (F.obj P)) {X : C}
    (hX : IsSummandOfFiniteSum Q X) : Projective (F.obj X) := by
  obtain ⟨ι, _, P, a, b, hP, hab⟩ := hX
  refine projective_of_sum_comp_eq_id (fun i => F.map (a i)) (fun i => F.map (b i)) ?_
    fun i => hFproj _ (hP i)
  rw [← CategoryTheory.Functor.map_id, ← hab, F.map_sum]
  simp only [CategoryTheory.Functor.map_comp]

end Summand

section SummandResolution

variable {C : Type uC} [Category.{vC} C] [Abelian C] {Q : C → Prop}

/-- A summand of a finite sum of objects satisfying `Q` has resolutions of every length by such
summands. -/
theorem IsSummandOfFiniteSum.hasResolutionBy {X : C} (hX : IsSummandOfFiniteSum Q X) (n : ℕ) :
    HasResolutionBy (IsSummandOfFiniteSum Q) n X :=
  HasResolutionBy.of_prop (isZero_zero _) (isSummandOfFiniteSum_of_isZero (isZero_zero _)) n hX

end SummandResolution

section Ext

open Abelian

/-- If `∑ i, a i ≫ b i = 𝟙 X`, then `∑ i, a i ∘ (b i ∘ e) = e` for every `e : Ext^n(X, Y)`. -/
theorem sum_mk₀_comp_mk₀_comp_eq_self {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{t} C]
    {X Y : C} {ι : Type*} [Fintype ι] {P : ι → C} (a : ∀ i, X ⟶ P i) (b : ∀ i, P i ⟶ X)
    (hab : ∑ i, a i ≫ b i = 𝟙 X) {n : ℕ} (e : Ext.{t} X Y n) :
    ∑ i, (Ext.mk₀ (a i)).comp ((Ext.mk₀ (b i)).comp e (zero_add n)) (zero_add n) = e := by
  simp only [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  rw [← Ext.sum_comp, ← Ext.mk₀_sum, hab, Ext.mk₀_id_comp]

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{t} C] [HasExt.{t'} D] (hF : IsSemilinear R S F) (Y : C)

/-- Let `∑ i, a i ≫ b i = 𝟙 X` with `a i : X ⟶ P i`, `b i : P i ⟶ X`. If the comparison maps
`S ⊗[R] Ext^n(P i, Y) → Ext^n(F (P i), F Y)` are injective, so is
`S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`. -/
theorem extBaseChangeMap_injective_of_sum_comp_eq_id {X : C} {ι : Type*} [Fintype ι]
    {P : ι → C} (a : ∀ i, X ⟶ P i) (b : ∀ i, P i ⟶ X) (hab : ∑ i, a i ≫ b i = 𝟙 X) (n : ℕ)
    (h : ∀ i, Function.Injective (extBaseChangeMap F hF (P i) Y n)) :
    Function.Injective (extBaseChangeMap F hF X Y n) := by
  have hsum : ∀ z : S ⊗[R] Ext.{t} X Y n,
      ∑ i, ((Ext.mk₀ (a i)).precompOfLinear R Y (zero_add n)).baseChange S
        (((Ext.mk₀ (b i)).precompOfLinear R Y (zero_add n)).baseChange S z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s e =>
      simp only [LinearMap.baseChange_tmul]
      rw [← TensorProduct.tmul_sum]
      exact congrArg (s ⊗ₜ[R] ·) (sum_mk₀_comp_mk₀_comp_eq_self a b hab e)
    | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have hi : ∀ i, ((Ext.mk₀ (b i)).precompOfLinear R Y (zero_add n)).baseChange S z = 0 :=
    fun i => h i (by
      rw [extBaseChangeMap_baseChange_precompOfLinear_mk₀, hz, map_zero, Ext.comp_zero])
  rw [← hsum z]
  simp only [hi, map_zero, Finset.sum_const_zero]

/-- Let `∑ i, a i ≫ b i = 𝟙 X` with `a i : X ⟶ P i`, `b i : P i ⟶ X`. If the comparison maps
`S ⊗[R] Ext^n(P i, Y) → Ext^n(F (P i), F Y)` are surjective, so is
`S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`. -/
theorem extBaseChangeMap_surjective_of_sum_comp_eq_id {X : C} {ι : Type*} [Fintype ι]
    {P : ι → C} (a : ∀ i, X ⟶ P i) (b : ∀ i, P i ⟶ X) (hab : ∑ i, a i ≫ b i = 𝟙 X) (n : ℕ)
    (h : ∀ i, Function.Surjective (extBaseChangeMap F hF (P i) Y n)) :
    Function.Surjective (extBaseChangeMap F hF X Y n) := by
  intro y
  have hFab : ∑ i, F.map (a i) ≫ F.map (b i) = 𝟙 (F.obj X) := by
    rw [← CategoryTheory.Functor.map_id, ← hab, F.map_sum]
    simp only [CategoryTheory.Functor.map_comp]
  choose t ht using fun i => h i ((Ext.mk₀ (F.map (b i))).comp y (zero_add n))
  refine ⟨∑ i, ((Ext.mk₀ (a i)).precompOfLinear R Y (zero_add n)).baseChange S (t i), ?_⟩
  rw [map_sum]
  simp only [extBaseChangeMap_baseChange_precompOfLinear_mk₀, ht]
  exact sum_mk₀_comp_mk₀_comp_eq_self (fun i => F.map (a i)) (fun i => F.map (b i)) hFab y

/-- If the comparison map `S ⊗[R] Ext^n(P, Y) → Ext^n(F P, F Y)` is bijective for all objects `P`
satisfying `Q`, it is bijective for every summand `X` of a finite sum of such objects. -/
theorem IsSummandOfFiniteSum.extBaseChangeMap_bijective {Q : C → Prop} (n : ℕ)
    (hQ : ∀ P, Q P → Function.Bijective (extBaseChangeMap F hF P Y n)) {X : C}
    (hX : IsSummandOfFiniteSum Q X) : Function.Bijective (extBaseChangeMap F hF X Y n) := by
  obtain ⟨ι, _, P, a, b, hP, hab⟩ := hX
  exact ⟨extBaseChangeMap_injective_of_sum_comp_eq_id F hF Y a b hab n fun i => (hQ _ (hP i)).1,
    extBaseChangeMap_surjective_of_sum_comp_eq_id F hF Y a b hab n fun i => (hQ _ (hP i)).2⟩

variable {Q : C → Prop} (hproj : ∀ P, Q P → Projective P)
  (hFproj : ∀ P, Q P → Projective (F.obj P))
  (hQ : ∀ P, Q P → Function.Bijective (extBaseChangeMap F hF P Y 0))

include hproj hFproj hQ in
/-- **Injectivity by dimension shifting, with summands.** Let `S` be flat over `R`, and let `Q`
be a class of projective objects `P` with `F P` projective and
`S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective. If `X` has a resolution `P_n → ⋯ → P_0 → X → 0`
by summands of finite sums of objects in `Q`, then `S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)` is
injective. -/
theorem extBaseChangeMap_injective_of_hasResolutionBy_summand [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy (IsSummandOfFiniteSum Q) n X) :
    Function.Injective (extBaseChangeMap F hF X Y n) :=
  extBaseChangeMap_injective_of_hasResolutionBy F hF Y
    (fun _ hP => hP.projective hproj) (fun _ hP => hP.projective_map F hFproj)
    (fun _ hP => hP.extBaseChangeMap_bijective F hF Y 0 hQ) n hX

include hproj hFproj hQ in
/-- **Bijectivity by dimension shifting, with summands.** Let `S` be flat over `R`, and let `Q`
be a class of projective objects `P` with `F P` projective and
`S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective. If `X` has a resolution
`P_{n+1} → ⋯ → P_0 → X → 0` by summands of finite sums of objects in `Q`, then
`S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)` is bijective. -/
theorem extBaseChangeMap_bijective_of_hasResolutionBy_summand [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy (IsSummandOfFiniteSum Q) (n + 1) X) :
    Function.Bijective (extBaseChangeMap F hF X Y n) :=
  extBaseChangeMap_bijective_of_hasResolutionBy F hF Y
    (fun _ hP => hP.projective hproj) (fun _ hP => hP.projective_map F hFproj)
    (fun _ hP => hP.extBaseChangeMap_bijective F hF Y 0 hQ) n hX

/-- Under the hypotheses of `extBaseChangeMap_bijective_of_hasResolutionBy_summand`, the
`S`-linear equivalence `S ⊗[R] Ext^n(X, Y) ≃ Ext^n(F X, F Y)` given by `extBaseChangeMap`. -/
def extBaseChangeEquivOfHasResolutionBySummand [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy (IsSummandOfFiniteSum Q) (n + 1) X) :
    S ⊗[R] Ext.{t} X Y n ≃ₗ[S] Ext.{t'} (F.obj X) (F.obj Y) n :=
  extBaseChangeEquivOfHasResolutionBy F hF Y
    (fun _ hP => hP.projective hproj) (fun _ hP => hP.projective_map F hFproj)
    (fun _ hP => hP.extBaseChangeMap_bijective F hF Y 0 hQ) n hX

@[simp]
theorem extBaseChangeEquivOfHasResolutionBySummand_apply [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy (IsSummandOfFiniteSum Q) (n + 1) X) (z : S ⊗[R] Ext.{t} X Y n) :
    extBaseChangeEquivOfHasResolutionBySummand F hF Y hproj hFproj hQ n hX z =
      extBaseChangeMap F hF X Y n z :=
  rfl

end Ext

section Rep

open Abelian

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {G : Type uG} [Monoid G] [Module.Flat R S] [HasExt.{t} (Rep.{max uS w} R G)]
  [HasExt.{t'} (Rep.{max uS w} S G)] (Y : Rep.{max uS w} R G)

/-- **`Ext` of representations and extension of scalars, injectivity, with summands.** Let `S` be
flat over `R`. If `X` has a resolution `P_n → ⋯ → P_0 → X → 0` by direct summands of finite
direct sums of representations that are free of finite rank over `R[G]`, then
`S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is injective. -/
theorem repExtBaseChangeMap_injective_of_hasResolutionBy_summand (n : ℕ)
    {X : Rep.{max uS w} R G} (hX : HasResolutionBy (IsSummandOfFiniteSum HasFiniteBasis) n X) :
    Function.Injective (extBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) X Y n) :=
  extBaseChangeMap_injective_of_hasResolutionBy_summand (repExtendScalars.{max uS w} R S G)
    (repExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasFiniteBasis)
    (fun _ hP => hP.projective) (fun _ hP => hP.projective_repExtendScalars S)
    (fun P hP => (extBaseChangeMap_zero_bijective_iff (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y).2
      (repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y)) n hX

/-- **`Ext` of representations and extension of scalars, with summands.** Let `S` be flat over
`R`. If `X` has a resolution `P_{n+1} → ⋯ → P_0 → X → 0` by direct summands of finite direct sums
of representations that are free of finite rank over `R[G]`, then
`S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is bijective. -/
theorem repExtBaseChangeMap_bijective_of_hasResolutionBy_summand (n : ℕ)
    {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum HasFiniteBasis) (n + 1) X) :
    Function.Bijective (extBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) X Y n) :=
  extBaseChangeMap_bijective_of_hasResolutionBy_summand (repExtendScalars.{max uS w} R S G)
    (repExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasFiniteBasis)
    (fun _ hP => hP.projective) (fun _ hP => hP.projective_repExtendScalars S)
    (fun P hP => (extBaseChangeMap_zero_bijective_iff (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y).2
      (repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y)) n hX

/-- Under the hypotheses of `repExtBaseChangeMap_bijective_of_hasResolutionBy_summand`, the
`S`-linear equivalence `S ⊗[R] Ext^n_G(X, Y) ≃ Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` given by
`extBaseChangeMap`. -/
def repExtBaseChangeEquivOfHasResolutionBySummand (n : ℕ) {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum HasFiniteBasis) (n + 1) X) :
    S ⊗[R] Ext.{t} X Y n ≃ₗ[S] Ext.{t'} ((repExtendScalars.{max uS w} R S G).obj X)
      ((repExtendScalars.{max uS w} R S G).obj Y) n :=
  extBaseChangeEquivOfHasResolutionBySummand (repExtendScalars.{max uS w} R S G)
    (repExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasFiniteBasis)
    (fun _ hP => hP.projective) (fun _ hP => hP.projective_repExtendScalars S)
    (fun P hP => (extBaseChangeMap_zero_bijective_iff (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y).2
      (repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y)) n hX

@[simp]
theorem repExtBaseChangeEquivOfHasResolutionBySummand_apply (n : ℕ) {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum HasFiniteBasis) (n + 1) X)
    (z : S ⊗[R] Ext.{t} X Y n) :
    repExtBaseChangeEquivOfHasResolutionBySummand S Y n hX z =
      extBaseChangeMap (repExtendScalars.{max uS w} R S G)
        (repExtendScalars_isSemilinear.{max uS w} R S G) X Y n z :=
  rfl

end Rep

end HyperextScalarExtension

end Langlands.Cohomology
