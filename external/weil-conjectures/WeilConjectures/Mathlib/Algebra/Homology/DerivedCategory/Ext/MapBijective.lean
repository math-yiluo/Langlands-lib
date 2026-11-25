/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.FiveLemma

/-!
# The edge maps on `Ext` of an adjunction with an exact left adjoint

Let `L ⊣ R` be an adjunction between abelian categories whose left adjoint `L : C ⥤ D` is
exact. For `A : C` and `G : D`, pushing an `Ext`-class forward along `L` and composing with the
counit `L R G ⟶ G` gives a map

```
  Ext A (R G) n ──L──▶ Ext (L A) (L R G) n ──counit──▶ Ext (L A) G n
```

For `L = f^*` and `R = f_*` on étale sheaves and `A` the constant sheaf `ℤ`, this is the edge
map `H^n(Y, f_* G) ⟶ H^n(X, G)` of the Leray spectral sequence. We show the low-degree part of
the five-term exact sequence that it fits in: the map is injective in degree `1`, and in degree
`2` as soon as `R¹R G = 0`, phrased as `R` preserving the cokernel of a monomorphism from `G`
into an injective object.

## Main definitions

- `CategoryTheory.Adjunction.mapExtCounit`: the map `Ext A (R G) n ⟶ Ext (L A) G n`.

## Main statements

- `CategoryTheory.Adjunction.mapExtCounit_one_injective`: it is injective in degree `1`.
- `CategoryTheory.Adjunction.mapExtCounit_two_injective`: it is injective in degree `2` if
  `R` maps `I ⟶ cokernel ι` to an epimorphism for a monomorphism `ι : G ⟶ I` into an injective
  object `I`.
- `CategoryTheory.Adjunction.mapExtCounit_bijective`: it is bijective in every degree if `R` is
  exact as well, so that `Ext A (R G) n ≃ Ext (L A) G n`.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Adjunction

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {R : D ⥤ C} (adj : L ⊣ R)

/-- The map `Ext A (R G) n ⟶ Ext (L A) G n` of an adjunction `L ⊣ R` with exact left adjoint:
push forward along `L`, then compose with the counit `L R G ⟶ G`. -/
noncomputable def mapExtCounit (A : C) (G : D) (n : ℕ) :
    Ext A (R.obj G) n →+ Ext (L.obj A) G n :=
  ((Ext.mk₀ (adj.counit.app G)).postcomp _ (add_zero n)).comp (L.mapExtAddHom A (R.obj G) n)

lemma mapExtCounit_apply (A : C) (G : D) (n : ℕ) (x : Ext A (R.obj G) n) :
    adj.mapExtCounit A G n x =
      (x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app G)) (add_zero n) :=
  rfl

/-- The map `CategoryTheory.Adjunction.mapExtCounit` is natural in `G`. -/
lemma mapExtCounit_comp_mk₀ (A : C) {G G' : D} (g : G ⟶ G') {n : ℕ} (x : Ext A (R.obj G) n) :
    adj.mapExtCounit A G' n (x.comp (Ext.mk₀ (R.map g)) (add_zero n)) =
      (adj.mapExtCounit A G n x).comp (Ext.mk₀ g) (add_zero n) := by
  simp only [mapExtCounit_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀]
  congr 2
  exact adj.counit_naturality g

/-- For a short exact sequence `S` in `C` and a morphism `φ : L S ⟶ T` to a short exact
sequence `T` in `D`, pushing the connecting map of `S` forward along `L` and composing with
`φ.τ₁` is the connecting map of `T` precomposed with `φ.τ₃`. -/
lemma mapExactFunctor_comp_extClass_comp_mk₀ {A : C} {S : ShortComplex C} (hS : S.ShortExact)
    {T : ShortComplex D} (hT : T.ShortExact) (φ : S.map L ⟶ T) {n : ℕ} (y : Ext A S.X₃ n) :
    ((y.comp hS.extClass rfl).mapExactFunctor L).comp (Ext.mk₀ φ.τ₁) (add_zero _) =
      ((y.mapExactFunctor L).comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  refine (Ext.comp_assoc _ _ _ rfl (add_zero 1) (by omega)).trans ?_
  exact (congrArg (fun z ↦ (y.mapExactFunctor L).comp z (rfl : n + 1 = n + 1))
    ((hS.map_of_exact L).extClass_naturality hT φ)).trans
      (Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) rfl).symm

variable [EnoughInjectives D]

attribute [local instance] Ext.subsingleton_of_injective

/-- **Injectivity of the edge map in degree `1`.** For an adjunction `L ⊣ R` with exact left
adjoint, the map `Ext¹(A, R G) ⟶ Ext¹(L A, G)` is injective. This is the first map of the
five-term exact sequence of the Grothendieck spectral sequence. -/
theorem mapExtCounit_one_injective (A : C) (G : D) :
    Function.Injective (adj.mapExtCounit A G 1) := by
  have := adj.isRightAdjoint
  have : L.PreservesMonomorphisms := inferInstance
  have hR := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let I : InjectivePresentation G := Classical.arbitrary _
  have := I.injective
  let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have hTR : (T.map R).Exact := hT.exact.map_of_mono_of_preservesKernel R inferInstance
    inferInstance
  let S := ShortComplex.mk (R.map I.f) (cokernel.π (R.map I.f)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let c : S.X₃ ⟶ R.obj T.X₃ := cokernel.desc _ (R.map T.g)
    (by rw [← R.map_comp, show I.f ≫ T.g = 0 from T.zero, R.map_zero])
  have hc : Mono c := hTR.mono_cokernelDesc
  have hgc : S.g ≫ c = R.map T.g := cokernel.π_desc _ _ _
  let φ : S.map L ⟶ T :=
    { τ₁ := adj.counit.app G
      τ₂ := adj.counit.app I.J
      τ₃ := L.map c ≫ adj.counit.app T.X₃
      comm₁₂ := (adj.counit.naturality I.f).symm
      comm₂₃ := by
        change adj.counit.app I.J ≫ T.g = L.map S.g ≫ L.map c ≫ _
        rw [← L.map_comp_assoc, hgc]
        exact (adj.counit.naturality T.g).symm }
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ A hS x
    (Ext.eq_zero_of_injective (I := R.obj I.J) _) (zero_add 1)
  change ((y.comp hS.extClass rfl).mapExactFunctor L).comp (Ext.mk₀ φ.τ₁) (add_zero _) = 0
    at hx
  rw [mapExactFunctor_comp_extClass_comp_mk₀ hS hT φ y] at hx
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ (L.obj A) hT _ rfl hx
  obtain ⟨y₀, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  obtain ⟨z₀, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀] at hz
  replace hz : z₀ ≫ T.g = L.map y₀ ≫ φ.τ₃ :=
    (Ext.mk₀_bijective _ _).1 (hz.trans (Ext.mk₀_comp_mk₀ _ _))
  have hw : adj.homEquiv _ _ z₀ ≫ S.g = y₀ := by
    rw [← cancel_mono c, Category.assoc, hgc, ← adj.homEquiv_naturality_right, hz]
    rw [Adjunction.homEquiv_unit]
    change adj.unit.app A ≫ R.map (L.map y₀ ≫ L.map c ≫ adj.counit.app T.X₃) = y₀ ≫ c
    simp
  rw [← hw, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- **Injectivity of the edge map in degree `2`.** For an adjunction `L ⊣ R` with exact left
adjoint, the map `Ext²(A, R G) ⟶ Ext²(L A, G)` is injective as soon as `R¹R G = 0`, in the form:
there is a monomorphism `ι : G ⟶ I` into an injective object such that `R` maps the cokernel
map of `ι` to an epimorphism. -/
theorem mapExtCounit_two_injective (A : C) {G I : D} (ι : G ⟶ I) [Mono ι] [Injective I]
    (hι : Epi (R.map (cokernel.π ι))) :
    Function.Injective (adj.mapExtCounit A G 2) := by
  have := adj.isRightAdjoint
  have : L.PreservesMonomorphisms := inferInstance
  have hR := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let T := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  have hS : (T.map R).ShortExact :=
    { exact := hT.exact.map_of_mono_of_preservesKernel R inferInstance inferInstance
      mono_f := inferInstanceAs (Mono (R.map ι))
      epi_g := hι }
  let φ : (T.map R).map L ⟶ T :=
    { τ₁ := adj.counit.app G
      τ₂ := adj.counit.app I
      τ₃ := adj.counit.app T.X₃
      comm₁₂ := (adj.counit.naturality ι).symm
      comm₂₃ := (adj.counit.naturality T.g).symm }
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ A hS x
    (Ext.eq_zero_of_injective (I := R.obj I) (n := 1) _) rfl
  change ((y.comp hS.extClass rfl).mapExactFunctor L).comp (Ext.mk₀ φ.τ₁) (add_zero _) = 0
    at hx
  rw [mapExactFunctor_comp_extClass_comp_mk₀ hS hT φ y] at hx
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ (L.obj A) hT _ rfl hx
  have hy : adj.mapExtCounit A T.X₃ 1 y = 0 := by
    change (y.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app T.X₃)) (add_zero 1) =
      (0 : Ext (L.obj A) T.X₃ 1)
    rw [← hz, Subsingleton.elim z 0, Ext.zero_comp]
  rw [(adj.mapExtCounit_one_injective A T.X₃) (hy.trans (map_zero _).symm)]
  exact Abelian.Ext.zero_comp (X := A) (n := 1) hS.extClass 2 rfl

omit [EnoughInjectives D] in
/-- In degree `0`, the map `CategoryTheory.Adjunction.mapExtCounit` is the adjunction
bijection `(A ⟶ R G) ≃ (L A ⟶ G)`. -/
lemma mapExtCounit_mk₀ (A : C) (G : D) (f : A ⟶ R.obj G) :
    adj.mapExtCounit A G 0 (Ext.mk₀ f) = Ext.mk₀ ((adj.homEquiv _ _).symm f) := by
  rw [mapExtCounit_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, adj.homEquiv_counit]

/-- **The `Ext`-adjunction.** For an adjunction `L ⊣ R` between abelian categories with both
`L` and `R` exact, the map `Ext A (R G) n ⟶ Ext (L A) G n` is bijective in every degree: `R`
preserves injective objects and short exact sequences, so both sides are computed by the
adjunction bijection on an injective resolution of `G`. -/
theorem mapExtCounit_bijective [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (A : C) (G : D) (n : ℕ) :
    Function.Bijective (adj.mapExtCounit A G n) := by
  have := adj.isRightAdjoint
  have : L.PreservesMonomorphisms := inferInstance
  have hR := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing G with
  | zero =>
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
      obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
      rw [mapExtCounit_mk₀, mapExtCounit_mk₀] at hxy
      rw [(adj.homEquiv _ _).symm.injective ((Ext.mk₀_bijective _ _).1 hxy)]
    · obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
      exact ⟨Ext.mk₀ (adj.homEquiv _ _ z), by rw [mapExtCounit_mk₀, Equiv.symm_apply_apply]⟩
  | succ n hn =>
    let I : InjectivePresentation G := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS : (T.map R).ShortExact := hT.map_of_exact R
    let φ : (T.map R).map L ⟶ T :=
      { τ₁ := adj.counit.app G
        τ₂ := adj.counit.app I.J
        τ₃ := adj.counit.app T.X₃
        comm₁₂ := (adj.counit.naturality I.f).symm
        comm₂₃ := (adj.counit.naturality T.g).symm }
    have : Injective (R.obj I.J) := Functor.injective_obj R I.J
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ (R.map T.g)).postcomp A (add_zero n)) (hS.extClass.postcomp A rfl)
      ((Ext.mk₀ T.g).postcomp (L.obj A) (add_zero n)) (hT.extClass.postcomp (L.obj A) rfl)
      (adj.mapExtCounit A I.J n) (adj.mapExtCounit A T.X₃ n) (adj.mapExtCounit A G (n + 1))
      (AddMonoidHom.ext fun x ↦ (adj.mapExtCounit_comp_mk₀ A T.g x).symm)
      (AddMonoidHom.ext fun y ↦ (mapExactFunctor_comp_extClass_comp_mk₀ hS hT φ y).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj A) hT n (n + 1) rfl))
      (hn I.J).2 (hn T.X₃)
      (fun x ↦ Ext.covariant_sequence_exact₁ _ hS x
        (Ext.eq_zero_of_injective (I := R.obj I.J) _) rfl)
      (fun y ↦ Ext.covariant_sequence_exact₁ _ hT y
        (Ext.eq_zero_of_injective (I := I.J) _) rfl)

/-- **The `Ext`-adjunction.** For an adjunction `L ⊣ R` between abelian categories with both
`L` and `R` exact, `Ext A (R G) n ≃ Ext (L A) G n`, by
`CategoryTheory.Adjunction.mapExtCounit_bijective`. -/
noncomputable def extAddEquiv [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (A : C) (G : D) (n : ℕ) :
    Ext A (R.obj G) n ≃+ Ext (L.obj A) G n :=
  AddEquiv.ofBijective (adj.mapExtCounit A G n) (adj.mapExtCounit_bijective A G n)

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {A : C} {A' : D} (u : A' ⟶ G.obj A)

/-- The map `Ext A B n ⟶ Ext A' (G B) n` for an exact functor `G` and `u : A' ⟶ G A`: push
forward along `G`, then precompose with `u`. -/
noncomputable def mapExtPrecomp (B : C) (n : ℕ) : Ext A B n →+ Ext A' (G.obj B) n :=
  ((Ext.mk₀ u).precomp _ (zero_add n)).comp (G.mapExtAddHom A B n)

lemma mapExtPrecomp_apply (B : C) (n : ℕ) (x : Ext A B n) :
    G.mapExtPrecomp u B n x = (Ext.mk₀ u).comp (x.mapExactFunctor G) (zero_add n) :=
  rfl

/-- The map `CategoryTheory.Functor.mapExtPrecomp` is natural in `B`. -/
lemma mapExtPrecomp_comp_mk₀ {B B' : C} (g : B ⟶ B') {n : ℕ} (x : Ext A B n) :
    G.mapExtPrecomp u B' n (x.comp (Ext.mk₀ g) (add_zero n)) =
      (G.mapExtPrecomp u B n x).comp (Ext.mk₀ (G.map g)) (add_zero n) := by
  simp only [mapExtPrecomp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero]

/-- The map `CategoryTheory.Functor.mapExtPrecomp` commutes with connecting maps. -/
lemma mapExtPrecomp_comp_extClass {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (y : Ext A S.X₃ n) :
    G.mapExtPrecomp u S.X₁ (n + 1) (y.comp hS.extClass rfl) =
      (G.mapExtPrecomp u S.X₃ n y).comp (hS.map_of_exact G).extClass rfl := by
  simp only [mapExtPrecomp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- In degree `0`, the map `CategoryTheory.Functor.mapExtPrecomp` is `φ ↦ u ≫ G φ`. -/
lemma mapExtPrecomp_mk₀ (B : C) (φ : A ⟶ B) :
    G.mapExtPrecomp u B 0 (Ext.mk₀ φ) = Ext.mk₀ (u ≫ G.map φ) := by
  rw [mapExtPrecomp_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- **Dimension shifting.** Let `G` be an exact functor which preserves injective objects and let
`u : A' ⟶ G A` be such that `φ ↦ u ≫ G φ` is a bijection `(A ⟶ B) ≃ (A' ⟶ G B)` for every `B`.
Then pushing forward along `G` and precomposing with `u` is a bijection
`Ext A B n ≃ Ext A' (G B) n` in every degree. -/
theorem mapExtPrecomp_bijective [EnoughInjectives C]
    (hG : ∀ I : C, Injective I → Injective (G.obj I))
    (hu : ∀ B : C, Function.Bijective (fun φ : A ⟶ B ↦ u ≫ G.map φ)) (B : C) (n : ℕ) :
    Function.Bijective (G.mapExtPrecomp u B n) := by
  induction n generalizing B with
  | zero =>
    refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
      obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
      rw [mapExtPrecomp_mk₀, mapExtPrecomp_mk₀] at hxy
      rw [(hu B).1 ((Ext.mk₀_bijective _ _).1 hxy)]
    · obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
      obtain ⟨φ, rfl⟩ := (hu B).2 z
      exact ⟨Ext.mk₀ φ, mapExtPrecomp_mk₀ G u B φ⟩
  | succ n hn =>
    let I : InjectivePresentation B := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS : (T.map G).ShortExact := hT.map_of_exact G
    have : Injective (G.obj I.J) := hG I.J I.injective
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ T.g).postcomp A (add_zero n)) (hT.extClass.postcomp A rfl)
      ((Ext.mk₀ (G.map T.g)).postcomp A' (add_zero n)) (hS.extClass.postcomp A' rfl)
      (G.mapExtPrecomp u I.J n) (G.mapExtPrecomp u T.X₃ n) (G.mapExtPrecomp u B (n + 1))
      (AddMonoidHom.ext fun x ↦ (G.mapExtPrecomp_comp_mk₀ u T.g x).symm)
      (AddMonoidHom.ext fun y ↦ (G.mapExtPrecomp_comp_extClass u hT y).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hT n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A' hS n (n + 1) rfl))
      (hn I.J).2 (hn T.X₃)
      (fun x ↦ Ext.covariant_sequence_exact₁ _ hT x
        (Ext.eq_zero_of_injective (I := I.J) _) rfl)
      (fun y ↦ Ext.covariant_sequence_exact₁ _ hS y
        (Ext.eq_zero_of_injective (I := G.obj I.J) _) rfl)

end CategoryTheory.Functor
