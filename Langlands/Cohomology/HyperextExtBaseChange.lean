import Langlands.Cohomology.HyperextHomLocalization
import Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Extension of scalars on `Ext` groups by dimension shifting

Let `F : C ⥤ D` be an exact functor from an `R`-linear to an `S`-linear abelian category that is
semilinear along `algebraMap R S`. The Library's `extBaseChangeMap F hF X Y n` compares
`S ⊗[R] Ext^n(X, Y)` with `Ext^n(F X, F Y)`, and is in general not bijective. This module proves,
for `S` flat over `R`, that it is injective when `X` has a resolution
`P_n → ⋯ → P_0 → X → 0` of length `n`, and bijective when `X` has a resolution of length
`n + 1`, by objects `P` in a class `Q` of projective objects with `F P` projective and
`S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective. For extension of scalars of representations, the
representations that are free of finite rank over the monoid algebra `R[G]` form such a class.

* `HasResolutionBy Q n X`: `X` has a resolution of length `n` by objects satisfying `Q`, defined
  recursively through the first syzygy; `HasResolutionBy.of_succ`, `HasResolutionBy.of_le`,
  `HasResolutionBy.mono` and `HasResolutionBy.of_prop`.
* `exact_precompOfLinear_mk₀_g_f`, `exact_precompOfLinear_mk₀_f_extClass`,
  `precompOfLinear_extClass_surjective`: pieces of the contravariant long exact `Ext` sequence of
  a short exact sequence, as exact sequences of `R`-linear maps.
* `extBaseChangeMap_baseChange_precompOfLinear` and its cases `_mk₀`, `_extClass`: naturality of
  `extBaseChangeMap` in the first variable.
* `extBaseChangeMap_zero_bijective_iff`: in degree `0`, `extBaseChangeMap` is bijective if and only
  if the Library's `homBaseChangeMap` is.
* `extBaseChangeMap_injective_of_hasResolutionBy`, `extBaseChangeMap_bijective_of_hasResolutionBy`
  and the linear equivalence `extBaseChangeEquivOfHasResolutionBy`: the dimension-shifting
  theorems.
* `HasFiniteBasis P`: `P` is free of finite rank over `R[G]`; `HasFiniteBasis.projective`,
  `HasFiniteBasis.projective_repExtendScalars`, `HasFiniteBasis.hasResolutionBy` and
  `repHomBaseChangeMap_bijective_of_hasFiniteBasis`.
* `repExtBaseChangeMap_injective_of_hasResolutionBy`,
  `repExtBaseChangeMap_bijective_of_hasResolutionBy` and the linear equivalence
  `repExtBaseChangeEquivOfHasResolutionBy`: the case of extension of scalars of representations.

The existence of resolutions by finite free representations remains a hypothesis; this module
does not verify it for any representation, and smooth representations are not treated.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

universe w uR uS uG uC vC uD vD t t'

namespace HyperextScalarExtension

section Resolution

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]

/-- `HasResolutionBy Q n X`: there is an exact sequence `P_n → ⋯ → P_1 → P_0 → X → 0` whose
terms `P_i` satisfy `Q`. It is defined by recursion on `n` through the first syzygy: for
`n = 0` there is an epimorphism `P_0 → X` with `Q P_0`, and for `n + 1` there is a short exact
sequence `0 → K → P_0 → X → 0` with `Q P_0` and `HasResolutionBy Q n K`. -/
def HasResolutionBy (Q : C → Prop) : ℕ → C → Prop
  | 0, X => ∃ (P : C) (p : P ⟶ X), Q P ∧ Epi p
  | n + 1, X => ∃ (K P : C) (i : K ⟶ P) (p : P ⟶ X) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ Q P ∧ HasResolutionBy Q n K

variable {Q Q' : C → Prop}

/-- A resolution of length `n + 1` gives a resolution of length `n`. -/
theorem HasResolutionBy.of_succ : ∀ {n : ℕ} {X : C},
    HasResolutionBy Q (n + 1) X → HasResolutionBy Q n X
  | 0, _, ⟨_, P, _, p, _, hT, hP, _⟩ => ⟨P, p, hP, hT.epi_g⟩
  | _ + 1, _, ⟨K, P, i, p, w, hT, hP, hK⟩ => ⟨K, P, i, p, w, hT, hP, hK.of_succ⟩

/-- A resolution of length `n` gives a resolution of every length `m ≤ n`. -/
theorem HasResolutionBy.of_le {m n : ℕ} (h : m ≤ n) {X : C} (hX : HasResolutionBy Q n X) :
    HasResolutionBy Q m X := by
  revert hX
  induction h with
  | refl => exact id
  | step _ ih => exact fun hX => ih hX.of_succ

/-- Resolutions by objects satisfying `Q` are resolutions by objects satisfying any weaker
`Q'`. -/
theorem HasResolutionBy.mono (h : ∀ P, Q P → Q' P) : ∀ {n : ℕ} {X : C},
    HasResolutionBy Q n X → HasResolutionBy Q' n X
  | 0, _, ⟨P, p, hP, hp⟩ => ⟨P, p, h P hP, hp⟩
  | _ + 1, _, ⟨K, P, i, p, w, hT, hP, hK⟩ => ⟨K, P, i, p, w, hT, h P hP, hK.mono h⟩

end Resolution

section ResolutionZero

variable {C : Type uC} [Category.{vC} C] [Abelian C] {Q : C → Prop}

/-- If a zero object `Z` satisfies `Q`, every object `P` satisfying `Q` has resolutions of every
length by objects satisfying `Q`, built from the short exact sequences `0 → Z → P → P → 0` and
`0 → Z → Z → Z → 0`. -/
theorem HasResolutionBy.of_prop {Z : C} (hZ : IsZero Z) (hQZ : Q Z) :
    ∀ (n : ℕ) {P : C}, Q P → HasResolutionBy Q n P
  | 0, P, hP => ⟨P, 𝟙 P, hP, inferInstance⟩
  | n + 1, P, hP =>
    have : Mono (0 : Z ⟶ P) := ⟨fun g h _ => hZ.eq_of_tgt g h⟩
    ⟨Z, P, 0, 𝟙 P, zero_comp,
      { exact := ShortComplex.exact_of_f_is_kernel _
          (KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance hZ) },
      hP, HasResolutionBy.of_prop hZ hQZ n hQZ⟩

end ResolutionZero

section Sequences

open Abelian

variable (R : Type uR) [CommRing R]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasExt.{t} C]
variable {T : ShortComplex C} (hT : T.ShortExact) (Y : C)

include hT in
/-- The `R`-linear sequence `Ext^n(X₃, Y) → Ext^n(X₂, Y) → Ext^n(X₁, Y)` of a short exact
sequence `0 → X₁ → X₂ → X₃ → 0` is exact. -/
theorem exact_precompOfLinear_mk₀_g_f (n : ℕ) :
    Function.Exact ((Ext.mk₀ T.g).precompOfLinear R Y (zero_add n))
      ((Ext.mk₀ T.f).precompOfLinear R Y (zero_add n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.contravariant_sequence_exact₂' hT Y n)

/-- The `R`-linear sequence `Ext^n(X₂, Y) → Ext^n(X₁, Y) → Ext^{n+1}(X₃, Y)` of a short exact
sequence `0 → X₁ → X₂ → X₃ → 0` is exact; the second map is precomposition with the extension
class of the sequence. -/
theorem exact_precompOfLinear_mk₀_f_extClass (n : ℕ) :
    Function.Exact ((Ext.mk₀ T.f).precompOfLinear R Y (zero_add n))
      (hT.extClass.precompOfLinear R Y (add_comm 1 n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.contravariant_sequence_exact₁' hT Y n (n + 1) (add_comm 1 n))

/-- If the middle term of a short exact sequence `0 → X₁ → X₂ → X₃ → 0` is projective, the
connecting map `Ext^n(X₁, Y) → Ext^{n+1}(X₃, Y)` is surjective. -/
theorem precompOfLinear_extClass_surjective [Projective T.X₂] (n : ℕ) :
    Function.Surjective (hT.extClass.precompOfLinear R Y (add_comm 1 n)) := by
  have := Ext.subsingleton_of_projective T.X₂ Y n
  intro x
  exact Ext.contravariant_sequence_exact₃ hT Y x (Subsingleton.elim _ _) (add_comm 1 n)

end Sequences

section Ext

open Abelian

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{t} C] [HasExt.{t'} D] (hF : IsSemilinear R S F)

/-- **Naturality of `extBaseChangeMap` in the first variable.** For `α : Ext^a(X₁, X₂)`,
`extBaseChangeMap` intertwines the base change of precomposition with `α` and precomposition
with `F(α)`. -/
theorem extBaseChangeMap_baseChange_precompOfLinear {X₁ X₂ : C} (Y : C) {a n m : ℕ}
    (α : Ext.{t} X₁ X₂ a) (h : a + n = m) (z : S ⊗[R] Ext.{t} X₂ Y n) :
    extBaseChangeMap F hF X₁ Y m ((α.precompOfLinear R Y h).baseChange S z) =
      (α.mapExactFunctor.{t, t'} F).comp (extBaseChangeMap F hF X₂ Y n z) h := by
  induction z using TensorProduct.inductionOn with
  | tmul s e =>
    rw [LinearMap.baseChange_tmul, extBaseChangeMap_tmul, extBaseChangeMap_tmul, Ext.comp_smul]
    change s • (α.comp e h).mapExactFunctor F = _
    rw [Ext.mapExactFunctor_comp]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Ext.comp_add]

/-- `extBaseChangeMap_baseChange_precompOfLinear` for precomposition with a morphism. -/
theorem extBaseChangeMap_baseChange_precompOfLinear_mk₀ {X₁ X₂ : C} (Y : C)
    (g : X₁ ⟶ X₂) (n : ℕ) (z : S ⊗[R] Ext.{t} X₂ Y n) :
    extBaseChangeMap F hF X₁ Y n (((Ext.mk₀ g).precompOfLinear R Y (zero_add n)).baseChange S z) =
      (Ext.mk₀ (F.map g)).comp (extBaseChangeMap F hF X₂ Y n z) (zero_add n) := by
  rw [extBaseChangeMap_baseChange_precompOfLinear, Ext.mapExactFunctor_mk₀]

/-- `extBaseChangeMap_baseChange_precompOfLinear` for the connecting map of a short exact
sequence: `extBaseChangeMap` intertwines the connecting maps of `0 → X₁ → X₂ → X₃ → 0` and of
its image under `F`. -/
theorem extBaseChangeMap_baseChange_precompOfLinear_extClass {T : ShortComplex C}
    (hT : T.ShortExact) (Y : C) (n : ℕ) (z : S ⊗[R] Ext.{t} T.X₁ Y n) :
    extBaseChangeMap F hF T.X₃ Y (n + 1)
        ((hT.extClass.precompOfLinear R Y (add_comm 1 n)).baseChange S z) =
      (hT.map_of_exact F).extClass.comp (extBaseChangeMap F hF T.X₁ Y n z) (add_comm 1 n) := by
  rw [extBaseChangeMap_baseChange_precompOfLinear, Ext.mapExactFunctor_extClass]

/-- In degree `0`, `extBaseChangeMap` is bijective if and only if the comparison map
`homBaseChangeMap : S ⊗[R] Hom(X, Y) → Hom(F X, F Y)` is bijective. -/
theorem extBaseChangeMap_zero_bijective_iff (X Y : C) :
    Function.Bijective (extBaseChangeMap F hF X Y 0) ↔
      Function.Bijective (homBaseChangeMap F hF X Y) := by
  let eR := ((Ext.linearEquiv₀ (R := R) (X := X) (Y := Y)).symm).baseChange R S
  let eS := (Ext.linearEquiv₀ (R := S) (X := F.obj X) (Y := F.obj Y)).symm
  have key : (extBaseChangeMap F hF X Y 0) ∘ eR = eS ∘ (homBaseChangeMap F hF X Y) := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul s f =>
      change s • (Ext.mk₀ f).mapExactFunctor F = Ext.mk₀ (s • F.map f)
      rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_smul]
    | add a b ha hb =>
      simp only [Function.comp_apply, map_add] at ha hb ⊢
      rw [ha, hb]
  exact (EquivLike.bijective_comp eR _).symm.trans
    (by rw [key]; exact EquivLike.comp_bijective _ eS)

variable {Q : C → Prop} (Y : C)

/-- **Degree `0`, injectivity.** Let `S` be flat over `R`. If `X` is a quotient of an object `P`
satisfying `Q`, and the comparison map of `P` in degree `0` is injective for all such `P`, then
`S ⊗[R] Hom(X, Y) → Hom(F X, F Y)` is injective. -/
theorem extBaseChangeMap_zero_injective_of_hasResolutionBy [Module.Flat R S]
    (hQ' : ∀ P, Q P → Function.Injective (extBaseChangeMap F hF P Y 0)) {X : C}
    (hX : HasResolutionBy Q 0 X) :
    Function.Injective (extBaseChangeMap F hF X Y 0) := by
  obtain ⟨P, p, hP, hp⟩ := hX
  have h1 : Function.Injective
      (((Ext.mk₀ p).precompOfLinear R Y (zero_add 0)).baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (Ext.precomp_mk₀_injective_of_epi Y p)
  have h2 : (fun z => (Ext.mk₀ (F.map p)).comp (extBaseChangeMap F hF X Y 0 z) (zero_add 0)) =
      extBaseChangeMap F hF P Y 0 ∘ ((Ext.mk₀ p).precompOfLinear R Y (zero_add 0)).baseChange S :=
    funext fun z => (extBaseChangeMap_baseChange_precompOfLinear_mk₀ F hF Y p 0 z).symm
  have h3 : Function.Injective
      (fun z => (Ext.mk₀ (F.map p)).comp (extBaseChangeMap F hF X Y 0 z) (zero_add 0)) :=
    h2 ▸ (hQ' P hP).comp h1
  exact Function.Injective.of_comp (f := fun e => (Ext.mk₀ (F.map p)).comp e (zero_add 0)) h3

variable (hproj : ∀ P, Q P → Projective P) (hFproj : ∀ P, Q P → Projective (F.obj P))
  (hQ : ∀ P, Q P → Function.Bijective (extBaseChangeMap F hF P Y 0))

include hFproj hQ in
/-- For `P` satisfying `Q`, the comparison map `S ⊗[R] Ext^n(P, Y) → Ext^n(F P, F Y)` is
surjective in every degree: in degree `0` by hypothesis, and in positive degrees because
`F P` is projective. -/
theorem extBaseChangeMap_surjective_of_prop {P : C} (hP : Q P) :
    ∀ n : ℕ, Function.Surjective (extBaseChangeMap F hF P Y n)
  | 0 => (hQ P hP).2
  | n + 1 => by
    have := hFproj P hP
    have := Ext.subsingleton_of_projective (F.obj P) (F.obj Y) n
    exact fun y => ⟨0, Subsingleton.elim _ _⟩

include hproj hFproj hQ in
/-- **Injectivity by dimension shifting.** Let `S` be flat over `R`, and let `Q` be a class of
projective objects `P` with `F P` projective and `S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective.
If `X` has a resolution `P_n → ⋯ → P_0 → X → 0` by objects in `Q`, then
`S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)` is injective. -/
theorem extBaseChangeMap_injective_of_hasResolutionBy [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy Q n X) : Function.Injective (extBaseChangeMap F hF X Y n) := by
  induction n generalizing X with
  | zero =>
    exact extBaseChangeMap_zero_injective_of_hasResolutionBy F hF Y
      (fun P hP => (hQ P hP).1) hX
  | succ n ih =>
    obtain ⟨K, P, i, p, w, hT, hP, hK⟩ := hX
    have : Projective (ShortComplex.mk i p w).X₂ := hproj P hP
    exact LinearMap.injective_of_surjective_of_injective_of_right_exact
      (((Ext.mk₀ i).precompOfLinear R Y (zero_add n)).baseChange S)
      ((hT.extClass.precompOfLinear R Y (add_comm 1 n)).baseChange S)
      ((Ext.mk₀ (F.map i)).precompOfLinear S (F.obj Y) (zero_add n))
      ((hT.map_of_exact F).extClass.precompOfLinear S (F.obj Y) (add_comm 1 n))
      (extBaseChangeMap F hF P Y n) (extBaseChangeMap F hF K Y n)
      (extBaseChangeMap F hF X Y (n + 1))
      (LinearMap.ext fun z => (extBaseChangeMap_baseChange_precompOfLinear_mk₀ F hF Y i n z).symm)
      (LinearMap.ext fun z =>
        (extBaseChangeMap_baseChange_precompOfLinear_extClass F hF hT Y n z).symm)
      (by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact _root_.lTensor_exact S (exact_precompOfLinear_mk₀_f_extClass R hT Y n)
          (precompOfLinear_extClass_surjective R hT Y n))
      (exact_precompOfLinear_mk₀_f_extClass S (hT.map_of_exact F) (F.obj Y) n)
      (extBaseChangeMap_surjective_of_prop F hF Y hFproj hQ hP n) (ih hK)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective S (precompOfLinear_extClass_surjective R hT Y n))

include hproj hFproj hQ in
/-- **Bijectivity by dimension shifting.** Let `S` be flat over `R`, and let `Q` be a class of
projective objects `P` with `F P` projective and `S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective.
If `X` has a resolution `P_{n+1} → ⋯ → P_0 → X → 0` by objects in `Q`, then
`S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)` is bijective. -/
theorem extBaseChangeMap_bijective_of_hasResolutionBy [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy Q (n + 1) X) : Function.Bijective (extBaseChangeMap F hF X Y n) := by
  induction n generalizing X with
  | zero =>
    obtain ⟨K, P, i, p, w, hT, hP, hK⟩ := hX
    have : Epi p := hT.epi_g
    have : Epi (F.map p) := (hT.map_of_exact F).epi_g
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (((Ext.mk₀ p).precompOfLinear R Y (zero_add 0)).baseChange S)
      (((Ext.mk₀ i).precompOfLinear R Y (zero_add 0)).baseChange S)
      ((Ext.mk₀ (F.map p)).precompOfLinear S (F.obj Y) (zero_add 0))
      ((Ext.mk₀ (F.map i)).precompOfLinear S (F.obj Y) (zero_add 0))
      (extBaseChangeMap F hF X Y 0) (extBaseChangeMap F hF P Y 0)
      (extBaseChangeMap F hF K Y 0)
      (LinearMap.ext fun z => (extBaseChangeMap_baseChange_precompOfLinear_mk₀ F hF Y p 0 z).symm)
      (LinearMap.ext fun z => (extBaseChangeMap_baseChange_precompOfLinear_mk₀ F hF Y i 0 z).symm)
      (by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact S (exact_precompOfLinear_mk₀_g_f R hT Y 0))
      (exact_precompOfLinear_mk₀_g_f S (hT.map_of_exact F) (F.obj Y) 0) (hQ P hP)
      (extBaseChangeMap_zero_injective_of_hasResolutionBy F hF Y (fun P hP => (hQ P hP).1) hK)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap _
          (Ext.precomp_mk₀_injective_of_epi Y p))
      (Ext.precomp_mk₀_injective_of_epi (F.obj Y) (F.map p))
  | succ n ih =>
    obtain ⟨K, P, i, p, w, hT, hP, hK⟩ := hX
    have : Projective (ShortComplex.mk i p w).X₂ := hproj P hP
    have : Projective ((ShortComplex.mk i p w).map F).X₂ := hFproj P hP
    exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
      (((Ext.mk₀ i).precompOfLinear R Y (zero_add n)).baseChange S)
      ((hT.extClass.precompOfLinear R Y (add_comm 1 n)).baseChange S)
      ((Ext.mk₀ (F.map i)).precompOfLinear S (F.obj Y) (zero_add n))
      ((hT.map_of_exact F).extClass.precompOfLinear S (F.obj Y) (add_comm 1 n))
      (extBaseChangeMap F hF P Y n) (extBaseChangeMap F hF K Y n)
      (extBaseChangeMap F hF X Y (n + 1))
      (LinearMap.ext fun z => (extBaseChangeMap_baseChange_precompOfLinear_mk₀ F hF Y i n z).symm)
      (LinearMap.ext fun z =>
        (extBaseChangeMap_baseChange_precompOfLinear_extClass F hF hT Y n z).symm)
      (by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact _root_.lTensor_exact S (exact_precompOfLinear_mk₀_f_extClass R hT Y n)
          (precompOfLinear_extClass_surjective R hT Y n))
      (exact_precompOfLinear_mk₀_f_extClass S (hT.map_of_exact F) (F.obj Y) n)
      (extBaseChangeMap_surjective_of_prop F hF Y hFproj hQ hP n) (ih hK)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective S (precompOfLinear_extClass_surjective R hT Y n))
      (precompOfLinear_extClass_surjective S (hT.map_of_exact F) (F.obj Y) n)

/-- **Extension of scalars on `Ext` by dimension shifting.** Let `S` be flat over `R`, and let
`Q` be a class of projective objects `P` with `F P` projective and
`S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` bijective. If `X` has a resolution
`P_{n+1} → ⋯ → P_0 → X → 0` by objects in `Q`, then `extBaseChangeMap` is an `S`-linear
equivalence `S ⊗[R] Ext^n(X, Y) ≃ Ext^n(F X, F Y)`. -/
def extBaseChangeEquivOfHasResolutionBy [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy Q (n + 1) X) :
    S ⊗[R] Ext.{t} X Y n ≃ₗ[S] Ext.{t'} (F.obj X) (F.obj Y) n :=
  LinearEquiv.ofBijective (extBaseChangeMap F hF X Y n)
    (extBaseChangeMap_bijective_of_hasResolutionBy F hF Y hproj hFproj hQ n hX)

@[simp]
theorem extBaseChangeEquivOfHasResolutionBy_apply [Module.Flat R S] (n : ℕ) {X : C}
    (hX : HasResolutionBy Q (n + 1) X) (z : S ⊗[R] Ext.{t} X Y n) :
    extBaseChangeEquivOfHasResolutionBy F hF Y hproj hFproj hQ n hX z =
      extBaseChangeMap F hF X Y n z :=
  rfl

end Ext

section Rep

open Abelian

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]

/-- `P` is free of finite rank as a module over the monoid algebra `R[G]`: for some `n` there is
a basis of `P` over `R[G]` indexed by `Fin n`. -/
def HasFiniteBasis (P : Rep.{w} R G) : Prop :=
  ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (MonoidAlgebra R G) P.ρ.asModule)

/-- A representation that is free of finite rank over `R[G]` is a projective object of
`Rep R G`. -/
theorem HasFiniteBasis.projective {P : Rep.{w} R G} (hP : HasFiniteBasis P) : Projective P := by
  obtain ⟨n, ⟨b⟩⟩ := hP
  exact projective_of_free_asModule P (Module.Free.of_basis b)

/-- A zero representation is free of rank `0` over `R[G]`. -/
theorem hasFiniteBasis_of_isZero {Z : Rep.{w} R G} (hZ : IsZero Z) : HasFiniteBasis Z := by
  have : Subsingleton Z.ρ.asModule := (Rep.isZero_iff R G Z).1 hZ
  exact ⟨0, ⟨Module.Basis.empty _⟩⟩

/-- A representation that is free of finite rank over `R[G]` has resolutions of every length by
such representations. -/
theorem HasFiniteBasis.hasResolutionBy {P : Rep.{w} R G} (hP : HasFiniteBasis P) (n : ℕ) :
    HasResolutionBy HasFiniteBasis n P :=
  HasResolutionBy.of_prop (isZero_zero _) (hasFiniteBasis_of_isZero (isZero_zero _)) n hP

/-- Evaluation at the vectors of a basis of `P` over `R[G]` is a bijection from `Hom_G(P, Y)` to
the families of vectors of `Y`. -/
theorem repHom_eval_basis_bijective {P : Rep.{w} R G} {ι : Type*}
    (b : Module.Basis ι (MonoidAlgebra R G) P.ρ.asModule) (Y : Rep.{w} R G) :
    Function.Bijective (fun (f : P ⟶ Y) (i : ι) => f.hom (P.ρ.asModuleEquiv (b i))) := by
  refine ⟨fun f f' h => ?_, fun y => ?_⟩
  · have h' : Representation.IntertwiningMap.equivLinearMapAsModule P.ρ Y.ρ f.hom =
        Representation.IntertwiningMap.equivLinearMapAsModule P.ρ Y.ρ f'.hom :=
      b.ext fun i => congrFun h i
    exact Rep.hom_ext
      ((Representation.IntertwiningMap.equivLinearMapAsModule P.ρ Y.ρ).injective h')
  · let L : P.ρ.asModule →ₗ[MonoidAlgebra R G] Y.ρ.asModule :=
      b.constr ℕ (fun i => Y.ρ.asModuleEquiv.symm (y i))
    refine ⟨Rep.ofHom ((Representation.IntertwiningMap.equivLinearMapAsModule P.ρ Y.ρ).symm L),
      funext fun i => ?_⟩
    exact b.constr_basis ℕ (fun i => Y.ρ.asModuleEquiv.symm (y i)) i

variable (R) (S : Type uS) [CommRing S] [Algebra R S] (G)

/-- Restriction of scalars of representations preserves epimorphisms. -/
instance repRestrictScalars_preservesEpimorphisms :
    (repRestrictScalars.{w} R S G).PreservesEpimorphisms where
  preserves {W W'} f _ := by
    have hf := (Rep.epi_iff_surjective f).1 inferInstance
    refine (Rep.epi_iff_surjective _).2 fun x => ?_
    obtain ⟨y, hy⟩ := hf (RestrictScalars.addEquiv R S W'.V x)
    refine ⟨(RestrictScalars.addEquiv R S W.V).symm y, ?_⟩
    change (RestrictScalars.addEquiv R S W'.V).symm
      (f.hom (RestrictScalars.addEquiv R S W.V ((RestrictScalars.addEquiv R S W.V).symm y))) = x
    rw [AddEquiv.apply_symm_apply, hy]
    exact (RestrictScalars.addEquiv R S W'.V).symm_apply_apply x

variable {R G}

/-- Extension of scalars sends a representation that is free of finite rank over `R[G]` to a
projective object of `Rep S G`. -/
theorem HasFiniteBasis.projective_repExtendScalars {P : Rep.{max uS w} R G}
    (hP : HasFiniteBasis P) : Projective ((repExtendScalars.{max uS w} R S G).obj P) :=
  (repExtendScalarsAdjunction.{w} R S G).map_projective P hP.projective

/-- **Hom groups out of finite free representations and extension of scalars.** If `P` is free
of finite rank over `R[G]`, then `S ⊗[R] Hom_G(P, Y) → Hom_G(S ⊗[R] P, S ⊗[R] Y)` is bijective,
for every `R`-algebra `S` and every representation `Y`. -/
theorem repHomBaseChangeMap_bijective_of_hasFiniteBasis {P : Rep.{max uS w} R G}
    (hP : HasFiniteBasis P) (Y : Rep.{max uS w} R G) :
    Function.Bijective (homBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y) := by
  obtain ⟨n, ⟨b⟩⟩ := hP
  let x : Fin n → P := fun i => P.ρ.asModuleEquiv (b i)
  let eR : (P ⟶ Y) ≃ₗ[R] (Fin n → Y) := LinearEquiv.ofBijective
    { toFun := fun f i => f.hom (x i)
      map_add' := fun f f' => rfl
      map_smul' := fun r f => rfl }
    (repHom_eval_basis_bijective b Y)
  let ψ : S ⊗[R] (P ⟶ Y) ≃ₗ[S] (Fin n → S ⊗[R] Y) :=
    (eR.baseChange R S _ _).trans (TensorProduct.piRight R S S (fun _ : Fin n => Y))
  let E : ((repExtendScalars.{max uS w} R S G).obj P ⟶
      (repExtendScalars.{max uS w} R S G).obj Y) → (Fin n → S ⊗[R] Y) :=
    fun g i => g.hom ((1 : S) ⊗ₜ[R] x i)
  have hE : Function.Injective E := by
    intro g g' h
    let adj := repExtendScalarsAdjunction.{w} R S G
    refine (adj.homEquiv P _).injective ((repHom_eval_basis_bijective b _).1 (funext fun i => ?_))
    exact congrArg (RestrictScalars.addEquiv R S _).symm (congrFun h i)
  have key : ∀ t, E (homBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y t) = ψ t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s f =>
      funext i
      change s • ((1 : S) ⊗ₜ[R] f.hom (x i)) = s ⊗ₜ[R] f.hom (x i)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add a c ha hc =>
      rw [map_add, map_add, ← ha, ← hc]
      rfl
  have hEφ : Function.Bijective (E ∘ homBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y) := by
    rw [show E ∘ _ = ψ from funext key]
    exact ψ.bijective
  refine ⟨hEφ.1.of_comp, fun g => ?_⟩
  obtain ⟨t, ht⟩ := hEφ.2 (E g)
  exact ⟨t, hE ht⟩

section Ext

variable [Module.Flat R S] [HasExt.{t} (Rep.{max uS w} R G)]
  [HasExt.{t'} (Rep.{max uS w} S G)] (Y : Rep.{max uS w} R G)

/-- **`Ext` of representations and extension of scalars, injectivity.** Let `S` be flat over `R`.
If `X` has a resolution `P_n → ⋯ → P_0 → X → 0` by representations that are free of finite rank
over `R[G]`, then `S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is injective. -/
theorem repExtBaseChangeMap_injective_of_hasResolutionBy (n : ℕ) {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy HasFiniteBasis n X) :
    Function.Injective (extBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) X Y n) :=
  extBaseChangeMap_injective_of_hasResolutionBy (repExtendScalars.{max uS w} R S G)
    (repExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasFiniteBasis)
    (fun _ hP => hP.projective) (fun _ hP => hP.projective_repExtendScalars S)
    (fun P hP => (extBaseChangeMap_zero_bijective_iff (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y).2
      (repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y)) n hX

/-- **`Ext` of representations and extension of scalars.** Let `S` be flat over `R`. If `X` has a
resolution `P_{n+1} → ⋯ → P_0 → X → 0` by representations that are free of finite rank over
`R[G]`, then `S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is bijective. -/
theorem repExtBaseChangeMap_bijective_of_hasResolutionBy (n : ℕ) {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy HasFiniteBasis (n + 1) X) :
    Function.Bijective (extBaseChangeMap (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) X Y n) :=
  extBaseChangeMap_bijective_of_hasResolutionBy (repExtendScalars.{max uS w} R S G)
    (repExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasFiniteBasis)
    (fun _ hP => hP.projective) (fun _ hP => hP.projective_repExtendScalars S)
    (fun P hP => (extBaseChangeMap_zero_bijective_iff (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y).2
      (repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y)) n hX

/-- Under the hypotheses of `repExtBaseChangeMap_bijective_of_hasResolutionBy`, the `S`-linear
equivalence `S ⊗[R] Ext^n_G(X, Y) ≃ Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` given by
`extBaseChangeMap`. -/
def repExtBaseChangeEquivOfHasResolutionBy (n : ℕ) {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy HasFiniteBasis (n + 1) X) :
    S ⊗[R] Ext.{t} X Y n ≃ₗ[S] Ext.{t'} ((repExtendScalars.{max uS w} R S G).obj X)
      ((repExtendScalars.{max uS w} R S G).obj Y) n :=
  extBaseChangeEquivOfHasResolutionBy (repExtendScalars.{max uS w} R S G)
    (repExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasFiniteBasis)
    (fun _ hP => hP.projective) (fun _ hP => hP.projective_repExtendScalars S)
    (fun P hP => (extBaseChangeMap_zero_bijective_iff (repExtendScalars.{max uS w} R S G)
      (repExtendScalars_isSemilinear.{max uS w} R S G) P Y).2
      (repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y)) n hX

@[simp]
theorem repExtBaseChangeEquivOfHasResolutionBy_apply (n : ℕ) {X : Rep.{max uS w} R G}
    (hX : HasResolutionBy HasFiniteBasis (n + 1) X) (z : S ⊗[R] Ext.{t} X Y n) :
    repExtBaseChangeEquivOfHasResolutionBy S Y n hX z =
      extBaseChangeMap (repExtendScalars.{max uS w} R S G)
        (repExtendScalars_isSemilinear.{max uS w} R S G) X Y n z :=
  rfl

end Ext

end Rep

end HyperextScalarExtension

end Langlands.Cohomology
