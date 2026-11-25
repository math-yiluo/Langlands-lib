/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.Triangulated.ExtensionProductEssentiallySmall

/-!
# Essential smallness of bounded complexes with cohomology in a small class

Let `C` be an abelian category and `P` a property of objects of `C`, closed under isomorphisms.
A bounded object `K` of the derived category `D(C)` with cohomology in degrees `[a, a + d]`, all
of whose cohomology objects satisfy `P`, is obtained from the shifted objects `M[-n]` with `P M`
(`DerivedCategory.singleObjects P`) by `d` successive extensions
(`DerivedCategory.iteratedExtensions_of_isGE_of_isLE`), using the truncation triangles
`τ_{<b} K ⟶ K ⟶ τ_{≥b} K ⟶ (τ_{<b} K)⟦1⟧` of the canonical t-structure and the long exact
cohomology sequence. Consequently, if `P` is essentially small, then so are the bounded complexes
with cohomology in `P` (`DerivedCategory.essentiallySmall_bounded_inf`). This is the argument of
blueprint `lemma-hypotheses-brown-representability--5`.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] (P : ObjectProperty C)

/-- The objects of `D(C)` isomorphic to a shifted object `M[-n]` with `P M`. -/
def singleObjects : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∃ (n : ℤ) (M : C), P M ∧ Nonempty (K ≅ (singleFunctor C n).obj M)

/-- The objects of `D(C)` obtained from `singleObjects P` by `d` successive extensions. -/
def iteratedExtensions : ℕ → ObjectProperty (DerivedCategory C)
  | 0 => singleObjects P
  | d + 1 => (iteratedExtensions d).extensionProduct (singleObjects P)

/-- The shifted objects of an essentially small property of objects are essentially small. -/
instance essentiallySmall_singleObjects [ObjectProperty.EssentiallySmall.{w'} P] :
    ObjectProperty.EssentiallySmall.{w'} (singleObjects P) := by
  obtain ⟨P₀, _, hP₀⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P
  refine ⟨ObjectProperty.ofObj (fun x : ℤ × Subtype P₀ ↦ (singleFunctor C x.1).obj x.2.1),
    inferInstance, ?_⟩
  rintro K ⟨n, M, hM, ⟨e⟩⟩
  obtain ⟨M₀, hM₀, ⟨e'⟩⟩ := hP₀ M hM
  exact ⟨_, ObjectProperty.ofObj_apply _ (n, ⟨M₀, hM₀⟩), ⟨e ≪≫ (singleFunctor C n).mapIso e'⟩⟩

/-- The iterated extensions of shifted objects of an essentially small property of objects are
essentially small. -/
lemma essentiallySmall_iteratedExtensions [LocallySmall.{w'} (DerivedCategory C)]
    [ObjectProperty.EssentiallySmall.{w'} P] (d : ℕ) :
    ObjectProperty.EssentiallySmall.{w'} (iteratedExtensions P d) := by
  induction d with
  | zero => exact essentiallySmall_singleObjects P
  | succ d ih => exact ObjectProperty.essentiallySmall_extensionProduct _ _

/-- An object of `D(C)` with cohomology in degrees `[a, a + d]` satisfying `P` is a `d`-fold
iterated extension of shifted objects satisfying `P`: split off the top cohomology with the
truncation triangle `τ_{<b} K ⟶ K ⟶ τ_{≥b} K ⟶ (τ_{<b} K)⟦1⟧`, `b = a + d`. -/
theorem iteratedExtensions_of_isGE_of_isLE [P.IsClosedUnderIsomorphisms] (d : ℕ)
    (K : DerivedCategory C) (a : ℤ) [K.IsGE a] [K.IsLE (a + d)]
    (hK : ∀ i, a ≤ i → i ≤ a + d → P ((homologyFunctor C i).obj K)) :
    iteratedExtensions P d K := by
  induction d generalizing K with
  | zero =>
    have : K.IsLE a := TStructure.t.isLE_of_le K (a + (0 : ℕ)) a (by simp)
    obtain ⟨M, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
    exact ⟨a, M, P.prop_of_iso ((homologyFunctor C a).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C a).app M) (hK a le_rfl (by simp)), ⟨e⟩⟩
  | succ d ih =>
    let b : ℤ := a + (d + 1 : ℕ)
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    have : T.obj₁.IsLE (b - 1) := inferInstanceAs (TStructure.t.IsLE T.obj₁ (b - 1))
    have : T.obj₁.IsLE (a + d) := TStructure.t.isLE_of_le _ (b - 1) _ (by
      push_cast [b]
      lia)
    have : T.obj₁.IsGE a := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE T.obj₃ b)
    have : TStructure.t.IsLE K b := ‹K.IsLE (a + ((d + 1 : ℕ) : ℤ))›
    have : T.obj₃.IsLE b := inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    refine ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, ih T.obj₁ fun i hi₁ hi₂ ↦ ?_, ?_⟩
    · have := (homologyFunctor C 0).isIso_shift_map_mor₁_of_isZero T hT (i - 1) i (by lia)
        (T.obj₃.isZero_of_isGE b _ (by lia)) (T.obj₃.isZero_of_isGE b _ (by lia))
      exact P.prop_of_iso (asIso (((homologyFunctor C 0).shift i).map T.mor₁)).symm
        (hK i hi₁ (by
          push_cast at hi₂ ⊢
          lia))
    · obtain ⟨M, ⟨e⟩⟩ := T.obj₃.exists_iso_singleFunctor_obj_of_isGE_of_isLE b
      have := (homologyFunctor C 0).isIso_shift_map_mor₂_of_isZero T hT b (b + 1) rfl
        (T.obj₁.isZero_of_isLE (a + d) _ (by lia)) (T.obj₁.isZero_of_isLE (a + d) _ (by lia))
      exact ⟨b, M, P.prop_of_iso (asIso (((homologyFunctor C 0).shift b).map T.mor₂) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app M)
        (hK b (by lia) le_rfl), ⟨e⟩⟩

/-- A bounded object of `D(C)` all of whose cohomology objects satisfy `P` is an iterated
extension of shifted objects satisfying `P`. -/
theorem exists_iteratedExtensions_of_bounded [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory C) (hK : TStructure.t.bounded K)
    (hP : ∀ n, P ((homologyFunctor C n).obj K)) : ∃ d, iteratedExtensions P d K := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  have : K.IsLE (a + (b - a).toNat) := TStructure.t.isLE_of_le K b _ (by lia)
  exact ⟨_, iteratedExtensions_of_isGE_of_isLE P (b - a).toNat K a fun i _ _ ↦ hP i⟩

/-- The iterated extensions of shifted objects satisfying `P` lie in every triangulated
subcategory closed under isomorphisms which contains these shifted objects. -/
lemma iteratedExtensions_le {Q : ObjectProperty (DerivedCategory C)} [Q.IsTriangulatedClosed₂]
    [Q.IsClosedUnderIsomorphisms] (hQ : singleObjects P ≤ Q) (d : ℕ) :
    iteratedExtensions P d ≤ Q := by
  induction d with
  | zero => exact hQ
  | succ d ih =>
    rintro K ⟨Y, Z, f, g, h, hT, hY, hZ⟩
    exact Q.ext_of_isTriangulatedClosed₂ _ hT (ih Y hY) (hQ Z hZ)

/-- Blueprint `lemma-hypotheses-brown-representability--5` (formal part): if `P` is essentially
small and closed under isomorphisms, the bounded objects of `D(C)` all of whose cohomology objects
satisfy `P` are essentially small. -/
theorem essentiallySmall_bounded_inf [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w'} P] [LocallySmall.{w'} (DerivedCategory C)] :
    ObjectProperty.EssentiallySmall.{w'}
      (TStructure.t.bounded ⊓ fun K ↦ ∀ n, P ((homologyFunctor C n).obj K)) := by
  have := essentiallySmall_iteratedExtensions P
  refine ObjectProperty.EssentiallySmall.of_le (Q := ⨆ d, iteratedExtensions P d) ?_
  rintro K ⟨hK, hP⟩
  exact (ObjectProperty.prop_iSup_iff _ _).2 (exists_iteratedExtensions_of_bounded P K hK hP)

end DerivedCategory
