import Langlands.Geometry.Building.KPLieFiltrationDual
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.DiscreteSubset

/-! # Bounded finiteness of jumps on supplied KP Lie filtrations -/

noncomputable section

universe u

open AlgebraicGeometry Langlands.GroupScheme
open scoped CategoryTheory.MonObj Topology ValuativeRel

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

/-- Submodules between `p` and `q` are recovered from their images in the quotient of `q`. -/
private theorem finite_submodule_Icc_of_finite_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p q : Submodule R M) [Finite (q ⧸ p.comap q.subtype)] : (Set.Icc p q).Finite := by
  let b := p.comap q.subtype
  have : Finite (Submodule R (q ⧸ b)) :=
    Finite.of_injective (fun U : Submodule R (q ⧸ b) => (U : Set (q ⧸ b))) SetLike.coe_injective
  let f (U : Submodule R M) := (U.comap q.subtype).map b.mkQ
  refine (Set.toFinite (f '' Set.Icc p q)).of_finite_image ?_
  intro U hU V hV e
  have he := congrArg (Submodule.comap b.mkQ) e
  have h₁ : b ≤ U.comap q.subtype := Submodule.comap_mono hU.1
  have h₂ : b ≤ V.comap q.subtype := Submodule.comap_mono hV.1
  have hUV : U.comap q.subtype = V.comap q.subtype := by
    simpa only [f, Submodule.comap_map_mkQ, sup_eq_right.mpr h₁, sup_eq_right.mpr h₂] using he
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hU.2,
    inf_eq_right.mpr hV.2] using congrArg (Submodule.map q.subtype) hUV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} (L : P.LieFiltrationData)

/-- The interval from `𝔪^n A` to `A` is finite for a finitely generated integral submodule. -/
private theorem finite_Icc_pow_smul (A : Submodule 𝒪[F] (GenericLie 𝒪[F] G))
    [Module.Finite 𝒪[F] A] (n : ℕ) : (Set.Icc (𝓂[F] ^ n • A) A).Finite := by
  let I := 𝓂[F] ^ n
  let B := (I • A).comap A.subtype
  have hann : Module.IsTorsionBySet 𝒪[F] (A ⧸ B) (I : Set 𝒪[F]) :=
    (Module.isTorsionBySet_quotient_iff B _).mpr fun x a ha =>
      Submodule.smul_mem_smul ha x.property
  let := hann.module
  have : IsScalarTower 𝒪[F] (𝒪[F] ⧸ I) (A ⧸ B) := hann.isScalarTower
  have : Finite (𝒪[F] ⧸ 𝓂[F]) := inferInstanceAs (Finite 𝓀[F])
  have : Finite (𝒪[F] ⧸ I) := Ideal.finite_quotient_pow (IsNoetherian.noetherian 𝓂[F]) n
  have : Module.Finite (𝒪[F] ⧸ I) (A ⧸ B) := Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  have : Finite (A ⧸ B) := Module.finite_of_finite (𝒪[F] ⧸ I)
  exact finite_submodule_Icc_of_finite_quotient (I • A) A

/-- On a bounded real interval the extension of the periodic Lie filtration takes finitely
many values. Finite generation is needed only for the supplied depth-zero submodule at `x`. -/
theorem finite_lieFiltrationReal_image_Icc (hL : L.IsPeriodic) (x : P.Apartment)
    [Module.Finite 𝒪[F] (L.lieFiltration x 0)] (a b : ℝ) :
    (L.lieFiltrationReal x '' Set.Icc a b).Finite := by
  let A := L.lieFiltration x 0
  let N := ⌈b⌉₊ + indexShift a
  let f (p : ℕ × Submodule 𝒪[F] (GenericLie 𝒪[F] G)) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
    ⨅ d ∈ 𝓂[F] ^ p.1, p.2.comap (d • LinearMap.id)
  have hfin := ((Set.finite_Iic (indexShift a)).prod (finite_Icc_pow_smul A N)).image f
  refine hfin.subset ?_
  rintro _ ⟨r, hr, rfl⟩
  have hn : indexShift r ≤ indexShift a := Nat.ceil_mono (neg_le_neg hr.1)
  have hbound : shiftedIndex r ≤ (N : NNReal) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    change r + (indexShift r : ℝ) ≤ (N : ℝ)
    have h₁ : (indexShift r : ℝ) ≤ indexShift a := by exact_mod_cast hn
    have h₂ : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    simp only [N, Nat.cast_add]
    linarith [hr.2]
  refine ⟨(indexShift r, L.lieFiltration x (shiftedIndex r)), ⟨hn, ?_, ?_⟩, rfl⟩
  · refine (L.smul_lieFiltration_le hL x N 0).trans ?_
    exact L.lieFiltration_antitone x (by simpa using hbound)
  · exact L.lieFiltration_antitone x zero_le

/-- Real depths at which the strict Lie piece is smaller than the non-strict one. -/
def lieJumpDepths (x : P.Apartment) : Set ℝ :=
  {r | L.lieFiltrationPlusReal x r < L.lieFiltrationReal x r}

/-- Different increasing jump depths have different starting lattices. -/
theorem strictAntiOn_lieFiltrationReal_lieJumpDepths (x : P.Apartment) :
    StrictAntiOn (L.lieFiltrationReal x) (L.lieJumpDepths x) :=
  fun _ hr _ _ hrs => (L.lieFiltrationReal_le_lieFiltrationPlusReal x hrs).trans_lt hr

theorem finite_lieJumpDepths_inter_Icc (hL : L.IsPeriodic) (x : P.Apartment)
    [Module.Finite 𝒪[F] (L.lieFiltration x 0)] (a b : ℝ) :
    (L.lieJumpDepths x ∩ Set.Icc a b).Finite := by
  have hf : (L.lieFiltrationReal x '' (L.lieJumpDepths x ∩ Set.Icc a b)).Finite :=
    (L.finite_lieFiltrationReal_image_Icc hL x a b).subset (Set.image_mono Set.inter_subset_right)
  exact hf.of_finite_image
    ((L.strictAntiOn_lieFiltrationReal_lieJumpDepths x).injOn.mono Set.inter_subset_left)

/-- A finite family of apartment points contributes only finitely many jumps in any closed
bounded depth interval. No local finiteness of an orbit set is used. -/
theorem finite_biUnion_lieJumpDepths_inter_Icc (hL : L.IsPeriodic) {X : Set P.Apartment}
    (hX : X.Finite) (hfg : ∀ x ∈ X, Module.Finite 𝒪[F] (L.lieFiltration x 0)) (a b : ℝ) :
    ((⋃ x ∈ X, L.lieJumpDepths x) ∩ Set.Icc a b).Finite := by
  have hf : (⋃ x ∈ X, L.lieJumpDepths x ∩ Set.Icc a b).Finite :=
    hX.biUnion fun x hx => by
      have := hfg x hx
      exact L.finite_lieJumpDepths_inter_Icc hL x a b
  refine hf.subset fun r hr => ?_
  obtain ⟨x, hx, hxr⟩ := Set.mem_iUnion₂.mp hr.1
  exact Set.mem_iUnion₂.mpr ⟨x, hx, hxr, hr.2⟩

private theorem isClosed_and_isDiscrete_of_finite_Icc {S : Set ℝ}
    (hf : ∀ a b, (S ∩ Set.Icc a b).Finite) : IsClosed S ∧ IsDiscrete S := by
  refine isClosed_and_discrete_iff.2 fun x => Filter.disjoint_principal_right.2 ?_
  let T := (S ∩ Set.Icc (x - 1) (x + 1)) \ {x}
  have hT : T.Finite := (hf _ _).subset Set.sdiff_subset
  have hx : x ∈ Tᶜ := fun h => h.2 (Set.mem_singleton x)
  have hTc : Tᶜ ∈ 𝓝[≠] x := mem_nhdsWithin_of_mem_nhds (hT.isClosed.isOpen_compl.mem_nhds hx)
  have hI : Set.Ioo (x - 1) (x + 1) ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  have hc : ({x} : Set ℝ)ᶜ ∈ 𝓝[≠] x := self_mem_nhdsWithin
  filter_upwards [hTc, hI, hc] with y hy hyI hyc
  exact fun h => hy ⟨⟨h, hyI.1.le, hyI.2.le⟩, hyc⟩

/-- Jump depths for finitely many points form a closed discrete subset of the real line. -/
theorem isClosed_and_isDiscrete_biUnion_lieJumpDepths (hL : L.IsPeriodic) {X : Set P.Apartment}
    (hX : X.Finite) (hfg : ∀ x ∈ X, Module.Finite 𝒪[F] (L.lieFiltration x 0)) :
    IsClosed (⋃ x ∈ X, L.lieJumpDepths x) ∧ IsDiscrete (⋃ x ∈ X, L.lieJumpDepths x) :=
  isClosed_and_isDiscrete_of_finite_Icc (L.finite_biUnion_lieJumpDepths_inter_Icc hL hX hfg)

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
