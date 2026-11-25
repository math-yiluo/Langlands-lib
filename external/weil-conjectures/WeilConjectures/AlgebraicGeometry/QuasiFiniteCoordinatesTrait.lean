/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.PowerSeries.Ideal
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteCoordinates
public import WeilConjectures.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization
public import WeilConjectures.RingTheory.DimensionAtPointComponents
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# Quasi-finite coordinates over a trait

Let `f : X ⟶ T` be flat and locally of finite presentation, and let `x` be a point of `X` with
local fibre dimension `q = dim_x X_{f(x)}`. If `η ⤳ f x` is a generalization of `f x`, then the
fibre `X_η` has dimension at least `q`, and so has the base change of `X` along any flat
field-valued point `Spec K ⟶ T` with image `η` (for instance the geometric generic point of a
trait). Together with the quasi-finite coordinates `exists_quasiFinite_affineSpace_chart`, this
gives the full statement of blueprint `lemma-quasi-finite-coordinates` for a flat scheme of
finite type over the trait `S = Spec k'⟦t⟧`: `q ≤ dim X_η̄`, and there are an open
neighbourhood `V` of `x` and quasi-finite coordinates `b : V ⟶ 𝔸^q_S`, so that `dim V_η̄ ≤ q`.

## Main results

- `AlgebraicGeometry.exists_specializes_topologicalKrullDimAt_asFiber_le`: a generalization of
  `f x` lifts to a generalization of `x` whose fibre has local dimension at least `dim_x X_{f x}`.
- `AlgebraicGeometry.topologicalKrullDimAt_asFiber_le_topologicalKrullDim_pullback`:
  `dim_x X_{f x} ≤ dim (X ×_T Spec K)` for a flat point `Spec K ⟶ T` generalizing `f x`.
- `AlgebraicGeometry.exists_quasiFinite_affineSpace_chart_trait`: the statement of the blueprint
  lemma over the trait `Spec k'⟦t⟧` and its geometric generic point.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

section Topology

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- In a quasi-sober space, the generic points of the irreducible components are the points
which are maximal for generalization. -/
theorem mem_genericPoints_iff_forall_specializes [QuasiSober A] {a : A} :
    a ∈ genericPoints A ↔ ∀ b : A, b ⤳ a → a ⤳ b := by
  constructor
  · intro ha b hb
    have hsub : closure ({a} : Set A) ⊆ closure {b} :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hb))
        isClosed_closure
    have := ha.2 isIrreducible_singleton.closure hsub
    exact specializes_iff_mem_closure.mpr (this (subset_closure rfl))
  · intro h
    refine ⟨isIrreducible_singleton.closure, fun Z hZ hsub ↦ ?_⟩
    let w := hZ.genericPoint
    have hw : closure ({w} : Set A) = closure Z := hZ.isGenericPoint_genericPoint_closure.def
    have hwa : w ⤳ a := specializes_iff_mem_closure.mpr
      (hw ▸ subset_closure (hsub (subset_closure rfl)))
    have haw : w ∈ closure ({a} : Set A) := specializes_iff_mem_closure.mp (h w hwa)
    exact subset_closure.trans (hw ▸ closure_minimal (Set.singleton_subset_iff.mpr haw)
      isClosed_closure)

attribute [local instance] specializationOrder in
/-- A surjective generalizing map `f : A ⟶ B` of quasi-sober `T₀` spaces satisfies
`dim B ≤ dim A`: a chain of specializations in `B` lifts to `A`, starting from its closed end. -/
theorem topologicalKrullDim_le_of_generalizingMap [QuasiSober A] [T0Space A] [QuasiSober B]
    [T0Space B] {f : A → B} (hf : GeneralizingMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim B ≤ topologicalKrullDim A := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_coheight,
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun b ↦ ?_
  obtain ⟨a, rfl⟩ := hsurj b
  refine le_trans (WithBot.coe_le_coe.mpr ?_)
    (le_iSup (fun a : A ↦ (Order.coheight a : WithBot ℕ∞)) a)
  suffices ∀ (n : ℕ) (p : LTSeries B) (a : A), p.length = n → p.head = f a →
      (n : ℕ∞) ≤ Order.coheight a from Order.coheight_le fun p hp ↦ this _ p a rfl hp
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro p a hn hp
    have hne : p.length ≠ 0 := by omega
    have hlt : f a < (p.tail hne).head := by
      rw [← hp, RelSeries.head_tail]
      exact p.strictMono (by rw [Fin.lt_def]; simp [hn, Nat.mod_eq_of_lt])
    obtain ⟨a', ha'a, ha'⟩ := hf hlt.le
    have haa' : a < a' := lt_of_le_of_ne ha'a (by rintro rfl; exact hlt.ne ha')
    have := ih (p.tail hne) a' (by simp [hn]) ha'.symm
    calc ((n + 1 : ℕ) : ℕ∞) = n + 1 := by push_cast; rfl
      _ ≤ Order.coheight a' + 1 := by gcongr
      _ ≤ Order.coheight a := Order.coheight_add_one_le haa'

end Topology

section FieldDimension

/-- In the spectrum of a finitely generated algebra over a field, every point `x` is a
specialization of the generic point `ξ` of an irreducible component with
`dim_x ≤ dim_ξ`: take a component through `x` of dimension `dim_x` (Stacks 00OT). -/
theorem exists_mem_genericPoints_specializes_topologicalKrullDimAt_le_of_finiteType
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : Spec (.of S)) :
    ∃ ξ ∈ genericPoints (Spec (.of S)), ξ ⤳ x ∧
      topologicalKrullDimAt x ≤ topologicalKrullDimAt ξ := by
  obtain ⟨-, -, -, n, hn, -, ⟨Z, hZ, hxZ, hZn⟩, -⟩ :=
    dimension_at_point_components (k := k) x.asIdeal
  have hξ : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents Z hZ).closure_eq] at this
  obtain ⟨-, -, -, n', hn', hle', -⟩ :=
    dimension_at_point_components (k := k) hZ.1.genericPoint.asIdeal
  refine ⟨hZ.1.genericPoint, show closure _ ∈ _ by rw [hξ.def]; exact hZ,
    hξ.specializes hxZ, ?_⟩
  change topologicalKrullDimAt (⟨x.asIdeal, inferInstance⟩ : Spec (.of S)) ≤ _
  rw [hn, ← hZn]
  exact (hle' Z hZ hξ.mem).trans_eq hn'.symm

/-- In a scheme `Y` locally of finite type over a field, every point `y` is a specialization of
the generic point `ξ` of an irreducible component with `dim_y Y ≤ dim_ξ Y`: apply
`exists_mem_genericPoints_specializes_topologicalKrullDimAt_le_of_finiteType` on an affine open
neighbourhood of `y`. -/
theorem exists_mem_genericPoints_specializes_topologicalKrullDimAt_le {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] (y : Y) :
    ∃ ξ ∈ genericPoints Y, ξ ⤳ y ∧ topologicalKrullDimAt y ≤ topologicalKrullDimAt ξ := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  change Y.Opens at W
  let := ((g.appLE ⊤ W (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have := hW.algebra_finiteType_of_field g
  let e : W ≃ₜ Spec Γ(Y, W) := hW.isoSpec.hom.homeomorph
  have hι : IsOpenEmbedding W.ι := W.ι.isOpenEmbedding
  have hy : W.ι ⟨y, hyW⟩ = y := rfl
  obtain ⟨ζ, hζ, hζy, hdim⟩ :=
    exists_mem_genericPoints_specializes_topologicalKrullDimAt_le_of_finiteType (k := k)
      (S := Γ(Y, W)) (e ⟨y, hyW⟩)
  rw [mem_genericPoints_iff_forall_specializes] at hζ
  refine ⟨W.ι (e.symm ζ), ?_, ?_, ?_⟩
  · rw [mem_genericPoints_iff_forall_specializes]
    intro b hb
    obtain ⟨b, rfl⟩ : b ∈ Set.range W.ι :=
      hb.mem_open hι.isOpen_range (Set.mem_range_self _)
    rw [hι.isInducing.specializes_iff] at hb ⊢
    have := (hζ _ (by simpa using hb.map e.continuous)).map e.symm.continuous
    simpa using this
  · rw [← hy]
    exact (by simpa using hζy.map e.symm.continuous : e.symm ζ ⤳ _).map hι.continuous
  · rw [← hy, ← topologicalKrullDimAt_eq_of_isOpenEmbedding hι,
      ← topologicalKrullDimAt_eq_of_isOpenEmbedding hι,
      topologicalKrullDimAt_eq_of_isOpenEmbedding e.isOpenEmbedding,
      topologicalKrullDimAt_eq_of_isOpenEmbedding e.isOpenEmbedding (e.symm ζ),
      Homeomorph.apply_symm_apply]
    exact hdim

end FieldDimension

section FlatFibre

variable {X T : Scheme.{u}} (f : X ⟶ T)

/-- A generic point of a fibre of a flat morphism, locally of finite presentation, generalizes
to every fibre over a generalization of its image, keeping its local fibre dimension. -/
private theorem exists_specializes_fiberι_topologicalKrullDimAt_le [Flat f]
    [LocallyOfFinitePresentation f] {t η : T} (ζ : f.fiber t)
    (hζ : ζ ∈ genericPoints (f.fiber t)) (hη : η ⤳ t) :
    ∃ x' : X, x' ⤳ f.fiberι t ζ ∧ f x' = η ∧
      topologicalKrullDimAt ζ ≤ topologicalKrullDimAt (f.asFiber x') := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, f.fiberι t ζ = ξ := ⟨_, rfl⟩
  have ht : f ξ = t := by
    have := Set.mem_range_self (f := f.fiberι t) ζ
    rw [f.range_fiberι, hξ] at this
    exact this
  subst ht
  obtain rfl : ζ = f.asFiber ξ :=
    (f.fiberι (f ξ)).isEmbedding.injective (hξ.trans (f.fiberι_asFiber ξ).symm)
  obtain ⟨x', hx'ξ, hx'⟩ := Flat.generalizingMap f hη
  exact ⟨x', by rwa [f.fiberι_asFiber], hx',
    (fibre_dimension_eq_of_specializes_component_restrict f ⊤ ξ x' trivial hx'ξ hζ).ge⟩

/-- **Generalizing the local fibre dimension** (Stacks 054U): for `f : X ⟶ T` flat and locally
of finite presentation, a point `x` of `X`, and a generalization `η ⤳ f x`, there is a
generalization `x' ⤳ x` over `η` with `dim_x X_{f x} ≤ dim_{x'} X_η`. Take a component of the
fibre through `x` of dimension `dim_x X_{f x}`, lift its generic point along the generalizing map
`f` and use the constancy of the fibre dimension along such generalizations. -/
theorem exists_specializes_topologicalKrullDimAt_asFiber_le [Flat f]
    [LocallyOfFinitePresentation f] (x : X) {η : T} (hη : η ⤳ f x) :
    ∃ x' : X, x' ⤳ x ∧ f x' = η ∧
      topologicalKrullDimAt (f.asFiber x) ≤ topologicalKrullDimAt (f.asFiber x') := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨ζ, hζ, hζx, hdim⟩ := exists_mem_genericPoints_specializes_topologicalKrullDimAt_le
    (f.fiberToSpecResidueField (f x)) (f.asFiber x)
  obtain ⟨x', hx'ζ, hx', hdim'⟩ :=
    exists_specializes_fiberι_topologicalKrullDimAt_le f ζ hζ hη
  refine ⟨x', hx'ζ.trans ?_, hx', hdim.trans hdim'⟩
  simpa using hζx.map (f.fiberι (f x)).continuous

/-- For `f : X ⟶ T` flat and locally of finite presentation and a generalization `η ⤳ f x`, the
fibre `X_η` has dimension at least `dim_x X_{f x}`. -/
theorem topologicalKrullDimAt_asFiber_le_topologicalKrullDim_fiber [Flat f]
    [LocallyOfFinitePresentation f] (x : X) {η : T} (hη : η ⤳ f x) :
    topologicalKrullDimAt (f.asFiber x) ≤ topologicalKrullDim (f.fiber η) := by
  obtain ⟨x', -, rfl, hdim⟩ := exists_specializes_topologicalKrullDimAt_asFiber_le f x hη
  exact hdim.trans ((iInf₂_le ⊤ trivial).trans (topologicalKrullDim_subspace_le _ Set.univ))

/-- The fibre `X_η` of `f : X ⟶ T` has dimension at most that of the base change of `X` along a
flat field-valued point `g : Spec K ⟶ T` with image `η`: the projection to `X` is generalizing
with image `f⁻¹{η}`. -/
theorem topologicalKrullDim_fiber_le_topologicalKrullDim_pullback {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ T) [Flat g] (z : Spec (.of K)) :
    topologicalKrullDim (f.fiber (g z)) ≤ topologicalKrullDim (pullback f g : Scheme.{u}) := by
  have hmem (p : ↥(pullback f g)) : pullback.fst f g p ∈ f ⁻¹' {g z} := by
    change f (pullback.fst f g p) = g z
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Subsingleton.elim (pullback.snd f g p) z]
  let φ : ↥(pullback f g) → f.fiber (g z) := fun p ↦
    (f.fiberHomeo (g z)).symm ⟨pullback.fst f g p, hmem p⟩
  have hφ (p : ↥(pullback f g)) : f.fiberι (g z) (φ p) = pullback.fst f g p :=
    f.fiberι_fiberHomeo_symm _ _
  have hinj := (f.fiberι (g z)).isEmbedding.injective
  refine topologicalKrullDim_le_of_generalizingMap (f := φ) ?_ ?_
  · intro p w hw
    have hw' := hw.map (f.fiberι (g z)).continuous
    rw [hφ] at hw'
    obtain ⟨p', hp'p, hp'⟩ := Flat.generalizingMap (pullback.fst f g) hw'
    exact ⟨p', hp'p, hinj ((hφ p').trans hp')⟩
  · intro w
    have hw : f (f.fiberι (g z) w) = g z := by
      have := Set.mem_range_self (f := f.fiberι (g z)) w
      rwa [f.range_fiberι] at this
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback _ z hw
    exact ⟨p, hinj ((hφ p).trans hp)⟩

/-- **Lower bound for the dimension of a flat field-valued base change** (blueprint
`lemma-quasi-finite-coordinates`, first clause): for `f : X ⟶ T` flat and locally of finite
presentation, a point `x` of `X` and a flat field-valued point `g : Spec K ⟶ T` whose image
generalizes `f x` (for instance the geometric generic point of a trait), the local fibre
dimension `dim_x X_{f x}` is at most `dim (X ×_T Spec K)`. -/
theorem topologicalKrullDimAt_asFiber_le_topologicalKrullDim_pullback [Flat f]
    [LocallyOfFinitePresentation f] (x : X) {K : Type u} [Field K] (g : Spec (.of K) ⟶ T)
    [Flat g] (z : Spec (.of K)) (hz : g z ⤳ f x) :
    topologicalKrullDimAt (f.asFiber x) ≤ topologicalKrullDim (pullback f g : Scheme.{u}) :=
  (topologicalKrullDimAt_asFiber_le_topologicalKrullDim_fiber f x hz).trans
    (topologicalKrullDim_fiber_le_topologicalKrullDim_pullback f g z)

end FlatFibre

section Trait

variable (k' : Type u) [Field k']

/-- The geometric generic point `Spec Ω ⟶ Spec k'⟦t⟧` is flat: `Ω` is a vector space over the
field of fractions of `k'⟦t⟧`, which is a localization of `k'⟦t⟧`. -/
instance flat_traitGenericPoint : Flat (traitGenericPoint k') :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.trans _ (FractionRing (PowerSeries k')) _))

/-- The image of the geometric generic point of the trait `Spec k'⟦t⟧` is its generic point: it
generalizes every point. -/
theorem traitGenericPoint_specializes (z : Spec (.of (traitGenericField k'))) (y : trait k') :
    traitGenericPoint k' z ⤳ y := by
  rw [← PrimeSpectrum.le_iff_specializes]
  intro a ha
  have h0 : algebraMap (PowerSeries k') (traitGenericField k') a = 0 := by
    have : algebraMap (PowerSeries k') (traitGenericField k') a ∈ z.asIdeal := ha
    rwa [Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot] at this
  have hinj : Function.Injective (algebraMap (PowerSeries k') (traitGenericField k')) := by
    rw [IsScalarTower.algebraMap_eq (PowerSeries k') (FractionRing (PowerSeries k'))]
    exact (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')).injective.comp
      (IsFractionRing.injective _ _)
  rw [hinj (h0.trans (map_zero _).symm)]
  exact zero_mem _

variable {k'} {X : Scheme.{u}} (f : X ⟶ trait k') [Flat f] [LocallyOfFiniteType f]

/-- **Fibre dimension and the geometric generic fibre** (blueprint
`lemma-quasi-finite-coordinates`, first clause): for `X` flat and locally of finite type over the
trait `S = Spec k'⟦t⟧` and a point `x` of `X`, `dim_x X_{f x} ≤ dim X_η̄`, where `X_η̄` is the base
change of `X` to the geometric generic point `Spec Ω ⟶ S`. -/
theorem topologicalKrullDimAt_asFiber_le_topologicalKrullDim_pullback_traitGenericPoint
    (x : X) :
    topologicalKrullDimAt (f.asFiber x) ≤
      topologicalKrullDim (pullback f (traitGenericPoint k') : Scheme.{u}) := by
  let z : Spec (.of (traitGenericField k')) := ⟨⊥, Ideal.isPrime_bot⟩
  exact topologicalKrullDimAt_asFiber_le_topologicalKrullDim_pullback f x _ z
    (traitGenericPoint_specializes k' z (f x))

/-- **Quasi-finite coordinates over the trait** (blueprint `lemma-quasi-finite-coordinates`):
let `X` be flat and locally of finite type over the trait `S = Spec k'⟦t⟧`, `x` a point of `X`
and `q = dim_x X_{f x}` the local dimension of its fibre. Then `q ≤ dim X_η̄`, and there are an
open neighbourhood `V` of `x` and a locally quasi-finite morphism `b : V ⟶ 𝔸^q_S` over `S`;
in particular `dim V_η̄ ≤ q`. Here `X_η̄` and `V_η̄` are the base changes to the geometric generic
point `Spec Ω ⟶ S`. -/
theorem exists_quasiFinite_affineSpace_chart_trait (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ (n : ℕ) (b : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); trait k')),
      LocallyOfFinitePresentation b ∧ LocallyQuasiFinite b ∧
      b ≫ (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k') = V.ι ≫ f ∧
      topologicalKrullDimAt (f.asFiber x) = n ∧
      (n : WithBot ℕ∞) ≤ topologicalKrullDim (pullback f (traitGenericPoint k') : Scheme.{u}) ∧
      topologicalKrullDim (pullback (V.ι ≫ f) (traitGenericPoint k') : Scheme.{u}) ≤ n := by
  obtain ⟨V, hxV, n, b, hb₁, hb₂, hb, hn⟩ := exists_quasiFinite_affineSpace_chart f x
  refine ⟨V, hxV, n, b, hb₁, hb₂, hb, hn, ?_, topologicalKrullDim_pullback_le_of_chart f b hb _⟩
  rw [← hn]
  exact topologicalKrullDimAt_asFiber_le_topologicalKrullDim_pullback_traitGenericPoint f x

end Trait

end AlgebraicGeometry
