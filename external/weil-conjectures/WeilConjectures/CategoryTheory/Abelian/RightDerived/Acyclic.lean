/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend
public import WeilConjectures.Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Acyclic resolutions compute right derived functors

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
injective resolutions. An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`.

The key statement is that `F` sends exact bounded below cochain complexes of `F`-acyclic
objects to exact complexes. It follows by dimension shifting from the long exact sequence of
the right derived functors (`ShortComplex.ShortExact.exists_rightDerived_δ_exact`). Applied to
mapping cones, it shows that `F.mapHomologicalComplex` sends quasi-isomorphisms between
bounded below cochain complexes of `F`-acyclic objects to quasi-isomorphisms. As a
consequence, if `ι : single₀ X ⟶ I` is a resolution of `X` by `F`-acyclic objects, then
`R^q F X ≅ H^q(F I)`.

## Main definitions

* `CategoryTheory.Functor.rightAcyclic`: the property of being `F`-acyclic.
* `CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso`: the isomorphism
  `R^q F X ≅ H^q(F I)` induced by a quasi-isomorphism from a complex `I` of `F`-acyclic
  objects to an injective resolution of `X`.
* `CategoryTheory.Functor.rightDerivedObjIsoOfResolution`: the isomorphism
  `R^q F X ≅ H^q(F I)` for a resolution `ι : single₀ X ⟶ I` of `X` by `F`-acyclic objects.

## Main results

* `CategoryTheory.Functor.nonempty_rightDerivedObjIso_homology_of_acyclic`: a resolution
  `ι : single₀ X ⟶ I` of `X` by `F`-acyclic objects gives `R^q F X ≅ H^q(F I)`.

* `CategoryTheory.ShortComplex.ShortExact.rightAcyclic_X₃`: `F`-acyclic objects are closed under
  cokernels of monomorphisms.
* `CategoryTheory.ShortComplex.ShortExact.map_of_rightAcyclic`: `F` sends a short exact sequence
  `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A` `F`-acyclic to a short exact sequence.
* `HomologicalComplex.Acyclic.map_of_rightAcyclic`: `F` sends exact bounded below cochain
  complexes of `F`-acyclic objects to exact complexes.
* `CategoryTheory.Functor.quasiIso_map_of_rightAcyclic`: `F` preserves quasi-isomorphisms
  between bounded below `ℤ`-indexed cochain complexes of `F`-acyclic objects;
  `CategoryTheory.Functor.quasiIso_map_of_rightAcyclic_nat` is the `ℕ`-indexed version.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* C. A. Weibel, *An Introduction to Homological Algebra*, Exercise 2.4.3
-/

@[expose] public section

namespace CategoryTheory

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

/-- An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`. This is acyclicity of an
object with respect to `F`, not acyclicity of a complex in the sense of
`HomologicalComplex.Acyclic`. -/
def rightAcyclic : ObjectProperty C :=
  fun A ↦ ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)

instance : F.rightAcyclic.IsClosedUnderIsomorphisms where
  of_iso e hA q := (hA q).of_iso ((F.rightDerived (q + 1)).mapIso e.symm)

instance : F.rightAcyclic.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, fun _ ↦ Functor.map_isZero _ (isZero_zero C)⟩

variable {F}

/-- Injective objects are `F`-acyclic. (blueprint: `lemma-acyclic-resolutions`, item 1) -/
lemma rightAcyclic_of_injective (A : C) [Injective A] : F.rightAcyclic A :=
  fun q ↦ F.isZero_rightDerived_obj_injective_succ q A

/-- `F`-acyclic objects are closed under binary biproducts. -/
lemma rightAcyclic_biprod {A B : C} (hA : F.rightAcyclic A) (hB : F.rightAcyclic B) :
    F.rightAcyclic (A ⊞ B) := by
  intro q
  have := preservesBinaryBiproducts_of_preservesBiproducts (F.rightDerived (q + 1))
  exact ((biprod_isZero_iff _ _).2 ⟨hA q, hB q⟩).of_iso ((F.rightDerived (q + 1)).mapBiprod A B)

instance : F.rightAcyclic.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    refine F.rightAcyclic.prop_of_iso ?_
      (rightAcyclic_biprod (h.prop_diag_obj ⟨.left⟩) (h.prop_diag_obj ⟨.right⟩))
    exact biprod.isoProd _ _ ≪≫ HasLimit.isoOfNatIso (diagramIsoPair h.diag).symm ≪≫
      (limit.isLimit _).conePointUniqueUpToIso h.isLimit

end Functor

namespace ShortComplex.ShortExact

variable {F : C ⥤ D} [F.Additive] {S : ShortComplex C} (hS : S.ShortExact)

include hS

/-- `F`-acyclic objects are closed under cokernels of monomorphisms: if `0 ⟶ A ⟶ B ⟶ C ⟶ 0`
is short exact and `A` and `B` are `F`-acyclic, then so is `C`. -/
lemma rightAcyclic_X₃ (h₁ : F.rightAcyclic S.X₁) (h₂ : F.rightAcyclic S.X₂) :
    F.rightAcyclic S.X₃ := by
  intro q
  obtain ⟨δ, w₁, w₂, h, -⟩ := hS.exists_rightDerived_δ_exact F (q + 1)
  exact (h.isZero_X₂_iff).2 ⟨(h₂ q).eq_of_src _ _, (h₁ (q + 1)).eq_of_tgt _ _⟩

/-- A left exact functor `F` sends a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A`
`F`-acyclic to a short exact sequence `0 ⟶ F A ⟶ F B ⟶ F C ⟶ 0`: exactness on the right
follows from `R^1 F A = 0`. -/
lemma map_of_rightAcyclic [PreservesFiniteLimits F] (h₁ : F.rightAcyclic S.X₁) :
    (S.map F).ShortExact := by
  have := hS.mono_f
  have hf : IsLimit (KernelFork.ofι (F.map S.f) (S.map F).zero) :=
    isLimitForkMapOfIsLimit' F S.zero hS.exact.fIsKernel
  have : Mono (S.map F).f := mono_of_isLimit_fork hf
  obtain ⟨δ, w₁, -, h, -⟩ := hS.exists_rightDerived_δ_exact F 0
  have : Epi ((F.rightDerived 0).map S.g) := h.epi_f ((h₁ 0).eq_of_tgt _ _)
  have : Epi (S.map F).g := by
    change Epi (F.map S.g)
    rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf S.g]
    infer_instance
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hf) inferInstance
    inferInstance

end ShortComplex.ShortExact

end CategoryTheory

namespace HomologicalComplex

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

/-- A left exact additive functor `F : C ⥤ D` sends an exact cochain complex `K` which is
bounded below and whose terms are all `F`-acyclic to an exact complex `F(K)`:
```
  0 ──▶ Kᵃ ──d──▶ Kᵃ⁺¹ ──d──▶ Kᵃ⁺² ──▶ ⋯      exact
                      │ F
                      ▼
  0 ──▶ F Kᵃ ──F d──▶ F Kᵃ⁺¹ ──F d──▶ F Kᵃ⁺² ──▶ ⋯    exact
```
The proof is by dimension shifting: the short exact sequences `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0` of
cycles show inductively that all `Zⁿ` are `F`-acyclic, so `F` keeps them short exact. -/
theorem Acyclic.map_of_rightAcyclic {K : CochainComplex C ℤ} (hK : K.Acyclic) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] (a : ℤ) [K.IsStrictlyGE a]
    (hK' : ∀ n, F.rightAcyclic (K.X n)) :
    ((F.mapHomologicalComplex _).obj K).Acyclic := by
  have hS (n : ℤ) := (hK (n + 1)).shortExact_cyclesShortComplex (i := n) (by simp)
  -- all the cycles `Zⁿ` are `F`-acyclic
  have hZ (n : ℤ) : F.rightAcyclic (K.cycles n) := by
    obtain hn | hn := lt_or_ge n a
    · exact F.rightAcyclic.prop_of_isZero
        (IsZero.of_mono (K.iCycles n) (K.isZero_of_isStrictlyGE a n hn))
    · induction n, hn using Int.leInduction with
      | base =>
        have := (hK a).epi_toCycles (a - 1) (by simp)
        exact F.rightAcyclic.prop_of_isZero (IsZero.of_epi (K.toCycles (a - 1) a)
          (K.isZero_of_isStrictlyGE a (a - 1) (by lia)))
      | succ n _ ih => exact (hS n).rightAcyclic_X₃ ih (hK' n)
  intro m
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by lia⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; lia)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; lia))
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    ((hS n).map_of_rightAcyclic (hZ n)).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

end HomologicalComplex

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- A left exact additive functor `F : C ⥤ D` sends a quasi-isomorphism `φ : K ⟶ L` between
bounded below `ℤ`-indexed cochain complexes whose terms are all `F`-acyclic to a
quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`:
```
    F Kᵃ ──F d──▶ F Kᵃ⁺¹ ──F d──▶ ⋯
     │F φᵃ          │F φᵃ⁺¹
     ▼              ▼
    F Lᵃ ──F d──▶ F Lᵃ⁺¹ ──F d──▶ ⋯
```
The proof applies `HomologicalComplex.Acyclic.map_of_rightAcyclic` to the mapping cone.
(blueprint: `lemma-acyclic-resolutions--1`) -/
theorem quasiIso_map_of_rightAcyclic {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (a : ℤ) [K.IsStrictlyGE a] [L.IsStrictlyGE a] (hK : ∀ n, F.rightAcyclic (K.X n))
    (hL : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have := CochainComplex.isStrictlyGE_mappingCone φ a a (a - 1)
  have hφ := (CochainComplex.mappingCone.quasiIso_iff_acyclic φ).1 ‹_›
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  refine HomologicalComplex.Acyclic.of_iso ?_
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)
  refine hφ.map_of_rightAcyclic F (a - 1) fun n ↦ ?_
  exact F.rightAcyclic.prop_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
    (rightAcyclic_biprod (hK (n + 1)) (hL n))

/-- The `ℕ`-indexed version of `Functor.quasiIso_map_of_rightAcyclic`: `F` sends a
quasi-isomorphism `φ : K ⟶ L` between `ℕ`-indexed cochain complexes whose terms are all
`F`-acyclic to a quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`. The proof extends `φ` to `ℤ` along
`e = ComplexShape.embeddingUpNat` and uses that `F` commutes with extension:
```
  F(K.extend e) ──F(extendMap φ e)──▶ F(L.extend e)
        │ ≅ mapExtendIso                    │ ≅ mapExtendIso
        ▼                                   ▼
  (F K).extend e ──extendMap (F φ) e──▶ (F L).extend e
```
-/
theorem quasiIso_map_of_rightAcyclic_nat {K L : CochainComplex C ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, F.rightAcyclic (K.X n)) (hL : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  let e := ComplexShape.embeddingUpNat
  have : QuasiIso (HomologicalComplex.extendMap φ e) :=
    (HomologicalComplex.quasiIso_extendMap_iff φ e).2 ‹_›
  have := F.quasiIso_map_of_rightAcyclic (HomologicalComplex.extendMap φ e) 0
    (HomologicalComplex.prop_extend_X _ e hK) (HomologicalComplex.prop_extend_X _ e hL)
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ e]
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (K.mapExtendIso e F) (L.mapExtendIso e F) (by ext; simp))).1 this

end Functor

namespace InjectiveResolution

variable {X : C} {I : CochainComplex C ℕ} (J : InjectiveResolution X) (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] (φ : I ⟶ J.cocomplex) [QuasiIso φ]

/-- The isomorphism `R^q F X ≅ H^q(F I)` induced by a quasi-isomorphism `φ : I ⟶ J` from a
complex `I` of `F`-acyclic objects to an injective resolution `J` of `X`:
```
    R^q F X ──J.isoRightDerivedObj F q──▶ H^q(F J) ◀──H^q(F φ)── H^q(F I)
```
`H^q(F φ)` is an isomorphism by `Functor.quasiIso_map_of_rightAcyclic_nat`. This generalises
`InjectiveResolution.isoRightDerivedObj`. -/
@[simps!]
noncomputable def isoRightDerivedObjOfQuasiIso (hI : ∀ n, F.rightAcyclic (I.X n)) (q : ℕ) :
    (F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q :=
  have := F.quasiIso_map_of_rightAcyclic_nat φ hI fun _ ↦ Functor.rightAcyclic_of_injective _
  J.isoRightDerivedObj F q ≪≫
    (asIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) q)).symm

end InjectiveResolution

namespace Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {X : C} {I : CochainComplex C ℕ}
  (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]

/-- **Acyclic resolutions compute right derived functors.** If `ι : single₀ X ⟶ I` is a
resolution `X → I⁰ → I¹ → ⋯` of `X` by `F`-acyclic objects, then `R^q F X ≅ H^q(F I)`.
It is `InjectiveResolution.isoRightDerivedObjOfQuasiIso` applied to the lift
`φ : I ⟶ J` of the identity of `X` to an injective resolution `J` of `X`:
```
  single₀ X ──ι──▶ I
        ╲          │ φ = descOfQuasiIso (𝟙 X) J ι
      J.ι ╲        ▼
            ╲────▶ J
```
(blueprint: `lemma-acyclic-resolutions`, item 2) -/
noncomputable def rightDerivedObjIsoOfResolution (hI : ∀ n, F.rightAcyclic (I.X n)) (q : ℕ) :
    (F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q :=
  (injectiveResolution X).isoRightDerivedObjOfQuasiIso F
    (InjectiveResolution.descOfQuasiIso (𝟙 X) _ ι) hI q

include ι in
/-- **Acyclic resolutions compute right derived functors.** Let `F : C ⥤ D` be a left exact
additive functor. If `ι : single₀ X ⟶ I` is a resolution `X → I⁰ → I¹ → ⋯` of `X` by
`F`-acyclic objects, then `R^q F X ≅ H^q(F I)` for all `q`. The witness is the natural
isomorphism `Functor.rightDerivedObjIsoOfResolution`. (blueprint: `lemma-acyclic-resolutions`;
`lemma-acyclic-resolutions`, item 2) -/
theorem nonempty_rightDerivedObjIso_homology_of_acyclic (hI : ∀ n, F.rightAcyclic (I.X n))
    (q : ℕ) :
    Nonempty ((F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q) :=
  ⟨F.rightDerivedObjIsoOfResolution ι hI q⟩


end Functor

end CategoryTheory

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **A criterion for acyclicity.** Let `P` be a property of objects of `C` which holds for the
injective objects and passes to the cokernel of a monomorphism between objects of `P`, and such
that `F` sends every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A` in `P` to an
epimorphism `F B ⟶ F C`. Then every object of `P` is `F`-acyclic.

Embed `A` into an injective object `I`, with cokernel `Q` in `P`. In the long exact sequence
`R^q F I ⟶ R^q F Q ⟶ R^{q+1} F A ⟶ R^{q+1} F I = 0`, the first map is an epimorphism for
`q = 0`, and `R^q F Q = 0` for `q > 0` by induction. -/
theorem rightAcyclic_of_epi_map_g (P : ObjectProperty C) (hinj : ∀ (I : C) [Injective I], P I)
    (hX₃ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hepi : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → Epi (F.map S.g)) {A : C}
    (hA : P A) : F.rightAcyclic A := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  intro q
  induction q generalizing A with
  | zero =>
    let S := ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := hS.exists_rightDerived_δ_exact F 0
    have : Epi ((F.rightDerived 0).map S.g) := by
      rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf S.g]
      have := hepi S hS hA
      infer_instance
    exact h₂.isZero_X₂_iff.2 ⟨h₁.epi_f_iff.1 this,
      (F.isZero_rightDerived_obj_injective_succ 0 S.X₂).eq_of_tgt _ _⟩
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨δ, w₁, w₂, -, h₂⟩ := hS.exists_rightDerived_δ_exact F (q + 1)
    exact h₂.isZero_X₂_iff.2 ⟨(ih (hX₃ S hS hA (hinj _))).eq_of_src _ _,
      (F.isZero_rightDerived_obj_injective_succ (q + 1) S.X₂).eq_of_tgt _ _⟩

end CategoryTheory.Functor
