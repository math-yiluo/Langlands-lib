module

import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.SeparablyGenerated

public import StacksFrontier.FieldTheory.TranscendentalSeparable
public import StacksFrontier.FieldTheory.Separable.Basic
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Purely inseparable base change to a separable extension

Let `K/k` be a finitely generated field extension. Then there is a commutative square of field
extensions
```
K  →  K'
↑     ↑
k  →  k'
```
in which `k'/k` and `K'/K` are finite purely inseparable and `K'/k'` is separably generated.
Inside a perfect field extension `Ω/K` the square can moreover be chosen with `K'` the compositum
`k'K` and `K' = (k' ⊗[k] K)_red`, and with `K'/k'` separable in the sense of [stacks, 030O](2),
i.e. each of its finitely generated subextensions has a separating transcendence basis.

## Main definitions

* `Stacks04KMConclusion`: the existence of such a square with `K'/k'` separably generated.

## Main results

* `exists_purelyInseparable_separablyGenerated_of_fg`: a finitely generated field extension
  becomes separably generated after a finite purely inseparable base change.
* `exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType`: the square exists inside
  any perfect field extension `Ω/K`, with `K' = k'K` and `K' = (k' ⊗[k] K)_red`.

## Implementation notes

Separability of `K'/k'` in `exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType`
is `Algebra.IsSeparableExtension`, the notion of [stacks, 030O](2), and not Mathlib's
`Algebra.IsSeparable`: the latter forces algebraicity, while `K'/k'` is in general transcendental.

`K/k` finitely generated as a field extension is `Algebra.EssFiniteType k K`
(`IntermediateField.fg_top_iff`); `Algebra.FiniteType k K` would be the strictly stronger
"finitely generated as an algebra".

The identification `K' = (k' ⊗[k] K)_red` is stated for the canonical map
`Algebra.TensorProduct.productMap`, `x ⊗ y ↦ xy`, as surjectivity together with
`RingHom.ker = nilradical`.

## References

* [Stacks Project, Tag 04KM](https://stacks.math.columbia.edu/tag/04KM)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
-/

@[expose] public section

@[expose] public section

/-! ### Separability after a purely inseparable base change inside a perfect field -/

namespace Stacks.FieldTheory.SeparableBaseChange

open scoped TensorProduct

/-- If `F/k` is a finite purely inseparable extension of exponent `n` and `q` is the exponential
characteristic, then the `q ^ n`-th power of any element of `F ⊗[k] K` comes from `K`. -/
private lemma exists_pow_eq_one_tmul (k F K : Type*) [Field k] [Field F] [CommRing K]
    [Algebra k F] [Algebra k K] [Module.Finite k F] [IsPurelyInseparable k F]
    (q : ℕ) [ExpChar k q] [ExpChar (F ⊗[k] K) q] (x : F ⊗[k] K) :
    ∃ c : K, x ^ q ^ IsPurelyInseparable.exponent k F = (1 : F) ⊗ₜ[k] c := by
  refine TensorProduct.inductionOn x (fun a b => ?_) (fun x y hx hy => ?_)
  · obtain ⟨d, hd⟩ := IsPurelyInseparable.exponent_def' k q a
    exact ⟨d • b ^ q ^ IsPurelyInseparable.exponent k F, by
      rw [Algebra.TensorProduct.tmul_pow, ← hd, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]⟩
  · obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [add_pow_expChar_pow, hc, hd, TensorProduct.tmul_add]⟩

/-- For a finite purely inseparable `F/k` and fields `F, K` inside `E` over `k`, the canonical map
`F ⊗[k] K → E` has the nilradical as its kernel: it identifies `(F ⊗[k] K)_red` with the
compositum. -/
private lemma ker_productMap_eq_nilradical (k K E F : Type*) [Field k] [Field K] [Field E]
    [Field F] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [Algebra k F]
    [Algebra F E] [IsScalarTower k F E] [Module.Finite k F] [IsPurelyInseparable k F] :
    RingHom.ker (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F E)
        (IsScalarTower.toAlgHom k K E)) = nilradical (F ⊗[k] K) := by
  set f := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F E)
    (IsScalarTower.toAlgHom k K E) with hf
  obtain ⟨q, _⟩ := ExpChar.exists k
  have hcomp : (f : F ⊗[k] K → E) ∘ algebraMap k (F ⊗[k] K) = algebraMap k E :=
    funext f.commutes
  have : ExpChar (F ⊗[k] K) q :=
    expChar_of_injective_algebraMap (.of_comp (hcomp ▸ (algebraMap k E).injective)) q
  refine le_antisymm (fun x hx => ?_) fun x hx =>
    RingHom.mem_ker.2 ((mem_nilradical.mp hx).map f).eq_zero
  obtain ⟨c, hc⟩ := exists_pow_eq_one_tmul k F K q x
  have h3 : f ((1 : F) ⊗ₜ[k] c) = 0 := by
    rw [← hc, map_pow, RingHom.mem_ker.mp hx, zero_pow (pow_ne_zero _ (expChar_pos k q).ne')]
  have h4 : c = 0 := (algebraMap K E).injective (by simpa [hf] using h3)
  exact mem_nilradical.2 ⟨_, by rw [hc, h4, TensorProduct.tmul_zero]⟩

/-- Being separably generated in the sense of [stacks, 030O](1) depends only on the image of the
base field in the extension: an isomorphism of the base compatible with the two maps into `E`
transports it. -/
private lemma isSeparablyGenerated_of_ringEquiv {L L' E : Type*} [Field L] [Field L'] [Field E]
    [Algebra L E] [Algebra L' E] (i : L ≃+* L')
    (hi : (algebraMap L E : L → E) = (algebraMap L' E) ∘ i)
    [h : Algebra.IsSeparablyGenerated L E] : Algebra.IsSeparablyGenerated L' E := by
  obtain ⟨s, hs, hsep⟩ := h.isSeparable
  let _ : Algebra L' L := (i.symm : L' →+* L).toAlgebra
  have hmap : (algebraMap L' L : L' → L) = i.symm := rfl
  have : IsScalarTower L' L E := IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, hi]; simp
  let i' : L ≃ₐ[L'] L' := { i with commutes' := fun r => i.apply_symm_apply r }
  refine ⟨s, ((hs.1.restrictScalars
    (hmap ▸ i.symm.injective)).isTranscendenceBasis_iff_isAlgebraic).mpr ?_, ?_⟩
  · have h0 : Algebra.IsAlgebraic
        ↥((Algebra.adjoin L (Set.range ((↑) : s → E))).restrictScalars L') E :=
      hs.1.isTranscendenceBasis_iff_isAlgebraic.mp hs
    rwa [Algebra.restrictScalars_adjoin_of_algEquiv i' hi] at h0
  · have h0 : Algebra.IsSeparable ↥((IntermediateField.adjoin L s).restrictScalars L') E := hsep
    rwa [IntermediateField.restrictScalars_adjoin_of_algEquiv i' hi] at h0

/-- A separably generated extension is separable in the sense of [stacks, 030O](2). -/
private lemma isSeparableExtension_of_isSeparablyGenerated (F E : Type*) [Field F] [Field E]
    [Algebra F E] (h : Algebra.IsSeparablyGenerated F E) : Algebra.StacksIsSeparableExtension F E := by
  obtain ⟨s, hs, hsep⟩ := h.isSeparable
  refine ⟨fun L _ => ⟨?_⟩⟩
  obtain ⟨t, ht, htsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType
      (k := F) (L := ↥L) (K := E) hs hsep
  exact ⟨(t : Set ↥L), ht, htsep⟩

/-- If an algebraic subextension `F/k` of `E/k` generates `E` over `K` as a field, then the
canonical map `F ⊗[k] K → E`, `x ⊗ y ↦ xy`, is surjective: the compositum is a field, but already
the `k`-subalgebra generated by `K` and `F` is all of `E`. -/
private lemma surjective_productMap_of_adjoin_eq_top {k K E : Type*} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E] (F : IntermediateField k E)
    [Algebra.IsAlgebraic k ↥F] (h : IntermediateField.adjoin K (F : Set E) = ⊤) :
    Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom k ↥F E) (IsScalarTower.toAlgHom k K E)) := by
  have hF : (IsScalarTower.toAlgHom k ↥F E).range = Algebra.adjoin k (F : Set E) :=
    (IntermediateField.range_val F).trans (Algebra.adjoin_eq _).symm
  have hK : Algebra.adjoin K (F : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right K F, h,
      IntermediateField.top_toSubalgebra]
  rw [← AlgHom.range_eq_top, Algebra.TensorProduct.productMap_range, hF, sup_comm,
    ← Algebra.Subalgebra.restrictScalars_adjoin (R := k), hK, Subalgebra.restrictScalars_top]

/-- Cutting a square down to the compositum: for a tower `k → K → K₁ → Ω` and an intermediate
field `k₁` of `K₁/k`, the subextension `K' = K(k₁)` of `K₁/K` contains a copy `k'` of `k₁` and is
generated over `K` by it. -/
private lemma exists_algEquiv_and_adjoin_eq_top (k K Ω : Type*) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    (K₁ : IntermediateField K Ω) (k₁ : IntermediateField k ↥K₁) :
    ∃ (K' : IntermediateField K Ω) (_ : K' ≤ K₁) (k' : IntermediateField k ↥K')
      (e : ↥k₁ ≃ₐ[k] ↥k'), (∀ x : ↥k₁, ((e x : ↥K') : Ω) = ((x : ↥K₁) : Ω)) ∧
        IntermediateField.adjoin K (k' : Set ↥K') = ⊤ := by
  set T : Set Ω := (Subtype.val : ↥K₁ → Ω) '' (k₁ : Set ↥K₁) with hT
  have hmem : ∀ x : ↥k₁, ((x : ↥K₁) : Ω) ∈ IntermediateField.adjoin K T := fun x =>
    IntermediateField.subset_adjoin K T ⟨(x : ↥K₁), x.2, rfl⟩
  let g : ↥k₁ →ₐ[k] ↥(IntermediateField.adjoin K T) :=
    { toFun := fun x => ⟨((x : ↥K₁) : Ω), hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  refine ⟨IntermediateField.adjoin K T,
    IntermediateField.adjoin_le_iff.mpr (by rintro y ⟨z, -, rfl⟩; exact z.2),
    g.fieldRange, AlgEquiv.ofInjectiveField g, fun _ => rfl,
    IntermediateField.lift_injective _ ?_⟩
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  congr 1
  ext y
  simp only [hT, Set.mem_image, SetLike.mem_coe, AlgHom.mem_fieldRange]
  exact ⟨by rintro ⟨z, ⟨x, rfl⟩, rfl⟩; exact ⟨x, x.2, rfl⟩,
    by rintro ⟨z, hz, rfl⟩; exact ⟨g ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩⟩

/-- Let `K/k` be a finitely generated field extension and let `Ω/K` be a perfect field extension.
Then there are intermediate fields `K'` of `Ω/K` and `k'` of `K'/k` with `k'/k` and `K'/K` finite
purely inseparable and `K'/k'` separable in the sense of [stacks, 030O](2), such that `K'` is
generated over `K` by `k'` and the canonical map `k' ⊗[k] K → K'` is surjective with kernel the
nilradical. -/
public theorem solution (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [Algebra K Ω] [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (K' : IntermediateField K Ω) (k' : IntermediateField k ↥K'),
      Module.Finite K ↥K' ∧ IsPurelyInseparable K ↥K' ∧
      Module.Finite k ↥k' ∧ IsPurelyInseparable k ↥k' ∧
      Algebra.StacksIsSeparableExtension ↥k' ↥K' ∧
      IntermediateField.adjoin K (k' : Set ↥K') = ⊤ ∧
      Function.Surjective (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) ∧
      RingHom.ker (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) =
        nilradical (↥k' ⊗[k] K) := by
  obtain ⟨K₁, k₁, _, _, _, _, _⟩ :=
    exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType k K Ω
  obtain ⟨K', hle, k', e, hev, hcompos⟩ := exists_algEquiv_and_adjoin_eq_top k K Ω K₁ k₁
  let _ : Algebra ↥K' ↥K₁ := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K ↥K' ↥K₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra ↥k' ↥K₁ := ((algebraMap ↥K' ↥K₁).comp (algebraMap ↥k' ↥K')).toAlgebra
  have htower : IsScalarTower ↥k' ↥K' ↥K₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite K ↥K' :=
    .of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have : IsPurelyInseparable K ↥K' := .tower_bot K ↥K' ↥K₁
  have : Module.Finite k ↥k' := .equiv e.toLinearEquiv
  have : IsPurelyInseparable k ↥k' := e.isPurelyInseparable
  have : Algebra.IsAlgebraic k ↥k' := .of_finite k ↥k'
  have : Algebra.EssFiniteType k ↥K' := .comp k K ↥K'
  have : Algebra.EssFiniteType ↥k' ↥K' := .of_comp k ↥k' ↥K'
  obtain ⟨s, hs, hsep⟩ :=
    (isSeparablyGenerated_of_ringEquiv (E := ↥K₁) e.toRingEquiv
      (funext fun x => Subtype.ext (hev x).symm)).isSeparable
  obtain ⟨t, ht, htsep⟩ :=
    @exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType
      ↥k' ↥K₁ ↥K' _ _ _ _ _ _ htower _ s hs hsep
  exact ⟨K', k', ‹_›, ‹_›, ‹_›, ‹_›,
    isSeparableExtension_of_isSeparablyGenerated ↥k' ↥K' ⟨_, ht, htsep⟩, hcompos,
    surjective_productMap_of_adjoin_eq_top k' hcompos,
    ker_productMap_eq_nilradical k K ↥K' ↥k'⟩

end Stacks.FieldTheory.SeparableBaseChange

@[expose] public section

open scoped TensorProduct

/-- Let `K/k` be a finitely generated field extension and let `Ω/K` be a perfect field extension.
Then inside `Ω` there is a diagram
```
K  →  K'
↑     ↑
k  →  k'
```
with `k'/k` and `K'/K` finite purely inseparable and `K'/k'` separable in the sense of
[stacks, 030O](2), in which moreover `K'` is the compositum `k'K` and the canonical map
`k' ⊗[k] K → K'` is surjective with kernel the nilradical, i.e. `K' = (k' ⊗[k] K)_red`. -/
@[stacks 030R]
public theorem exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
    [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (K' : IntermediateField K Ω) (k' : IntermediateField k ↥K'),
      Module.Finite K ↥K' ∧ IsPurelyInseparable K ↥K' ∧
      Module.Finite k ↥k' ∧ IsPurelyInseparable k ↥k' ∧
      Algebra.StacksIsSeparableExtension ↥k' ↥K' ∧
      IntermediateField.adjoin K (k' : Set ↥K') = ⊤ ∧
      Function.Surjective (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) ∧
      RingHom.ker (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) =
        nilradical (↥k' ⊗[k] K) := by apply Stacks.FieldTheory.SeparableBaseChange.solution

end
