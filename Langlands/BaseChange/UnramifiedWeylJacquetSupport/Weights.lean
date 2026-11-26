import Langlands.BaseChange.UnramifiedWeylJacquetSupportStatement
import Langlands.Group.GL.ParabolicQuotient
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.CuspidalSupport.JacquetLengthDetector
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Joint generalized weights and exactness for the integral diagonal fixed space. -/

noncomputable section

namespace Langlands.BaseChange.WeylJacquet

open GeneralLinear Correspondence Unramified

universe uF uU uV uW

section LinearAlgebra

variable {ι : Type*} {U : Type uU} {V : Type uV} {W : Type uW}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

private abbrev jointWeight (a : ι → Module.End ℂ V) (z : ι → ℂ) : Submodule ℂ V :=
  ⨅ i, (a i).maxGenEigenspace (z i)

private theorem map_shift_pow (a : Module.End ℂ V) (b : Module.End ℂ W)
    (f : V →ₗ[ℂ] W) (h : ∀ x, f (a x) = b (f x)) (c : ℂ) (k : ℕ) (x : V) :
    f (((a - c • 1) ^ k) x) = ((b - c • 1) ^ k) (f x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, h, ih]

private theorem mapsTo_jointWeight {a : ι → Module.End ℂ V} {b : ι → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (h : ∀ i x, f (a i x) = b i (f x)) (z : ι → ℂ) :
    Set.MapsTo f (jointWeight a z) (jointWeight b z) := by
  intro x hx
  change x ∈ jointWeight a z at hx
  change f x ∈ jointWeight b z
  rw [Submodule.mem_iInf] at hx ⊢
  intro i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hx i)
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ⟨k, by rw [← map_shift_pow _ _ f (h i), hk, map_zero]⟩

private theorem mem_jointWeight_of_apply_mem {a : ι → Module.End ℂ V}
    {b : ι → Module.End ℂ W} (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (h : ∀ i x, f (a i x) = b i (f x)) (z : ι → ℂ) {x : V}
    (hx : f x ∈ jointWeight b z) : x ∈ jointWeight a z := by
  rw [Submodule.mem_iInf] at hx ⊢
  intro i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hx i)
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ⟨k, hf (by rw [map_shift_pow _ _ f (h i), hk, map_zero])⟩

private def jointWeightMap {a : ι → Module.End ℂ V} {b : ι → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (h : ∀ i x, f (a i x) = b i (f x)) (z : ι → ℂ) :
    jointWeight a z →ₗ[ℂ] jointWeight b z :=
  (f.comp (jointWeight a z).subtype).codRestrict _ (fun x => mapsTo_jointWeight f h z x.property)

private theorem jointWeightMap_injective {a : ι → Module.End ℂ V} {b : ι → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (h : ∀ i x, f (a i x) = b i (f x)) (z : ι → ℂ)
    (hf : Function.Injective f) : Function.Injective (jointWeightMap f h z) :=
  fun _ _ hxy => Subtype.ext (hf (congrArg Subtype.val hxy))

private theorem jointWeightMap_surjective [FiniteDimensional ℂ V]
    {a : ι → Module.End ℂ V} {b : ι → Module.End ℂ W}
    (ha : ∀ i j, Commute (a i) (a j)) (hb : ∀ i j, Commute (b i) (b j))
    (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (h : ∀ i x, f (a i x) = b i (f x)) (z : ι → ℂ) :
    Function.Surjective (jointWeightMap f h z) := by
  classical
  have htop : ⨆ c, jointWeight a c = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute a
      (fun i j _ => ha i j) (fun i => (a i).iSup_maxGenEigenspace_eq_top)
  have hind : iSupIndep (jointWeight b) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo b
      (fun i j c => Module.End.mapsTo_maxGenEigenspace_of_comm (hb j i) c)
  let C := ⨆ (c : ι → ℂ) (_ : c ≠ z), jointWeight a c
  let D := ⨆ (c : ι → ℂ) (_ : c ≠ z), jointWeight b c
  have hsplit : jointWeight a z ⊔ C = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun c => ?_
    by_cases hz : c = z
    · subst c
      exact le_sup_left
    · exact (le_iSup₂ (f := fun c (_ : c ≠ z) => jointWeight a c) c hz).trans le_sup_right
  have hfCD : C ≤ D.comap f := by
    refine iSup₂_le fun c hc x hx => ?_
    exact (le_iSup₂ (f := fun c (_ : c ≠ z) => jointWeight b c) c hc)
      (mapsTo_jointWeight f h c hx)
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  have hx' : x ∈ jointWeight a z ⊔ C := hsplit ▸ Submodule.mem_top
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hx'
  have hfw : f w ∈ jointWeight b z := by
    have he : f w = y.val - f v := by simp only [← hx, map_add, add_sub_cancel_left]
    rw [he]
    exact (jointWeight b z).sub_mem y.property (mapsTo_jointWeight f h z hv)
  have hz : f w = 0 := Submodule.disjoint_def.mp (hind z) (f w) hfw (hfCD hw)
  refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
  change f v = y.val
  simpa only [map_add, hz, add_zero] using hx

private theorem finrank_exact_jointWeight [FiniteDimensional ℂ V]
    {a : ι → Module.End ℂ U} {b : ι → Module.End ℂ V} {c : ι → Module.End ℂ W}
    (hb : ∀ i j, Commute (b i) (b j)) (hc : ∀ i j, Commute (c i) (c j))
    (f : U →ₗ[ℂ] V) (g : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : LinearMap.range f = LinearMap.ker g)
    (hfa : ∀ i x, f (a i x) = b i (f x)) (hgb : ∀ i x, g (b i x) = c i (g x))
    (z : ι → ℂ) :
    Module.finrank ℂ (jointWeight b z) =
      Module.finrank ℂ (jointWeight a z) + Module.finrank ℂ (jointWeight c z) := by
  let f' := jointWeightMap f hfa z
  let g' := jointWeightMap g hgb z
  have hfg : LinearMap.range f' = LinearMap.ker g' := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change g (f v.val) = 0
      exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f v.val)
    · intro hx
      have hx' : x.val ∈ LinearMap.ker g := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (hex.symm ▸ hx')
      have hv' : v ∈ jointWeight a z :=
        mem_jointWeight_of_apply_mem f hf hfa z (hv ▸ x.property)
      exact ⟨⟨v, hv'⟩, Subtype.ext hv⟩
  have hfin := g'.finrank_range_add_finrank_ker
  rw [← hfg, LinearMap.range_eq_top.mpr (jointWeightMap_surjective hb hc g hg hgb z),
    finrank_top, ← (LinearEquiv.ofInjective f' (jointWeightMap_injective f hfa z hf)).finrank_eq,
    add_comm] at hfin
  exact hfin.symm

end LinearAlgebra

section Torus

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup

/-- The integral diagonal is the inverse image of the compact spherical subgroup under
 the closed embedding of the Borel Levi. -/
theorem borelIntegralDiagonal_isCompact (r : ℕ) :
    IsCompact (borelIntegralDiagonalOpen F r : Set ((borelShape r).Levi F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.fieldT2
  let := T.localField
  let := T.valuativeRel
  let B := borelShape r
  have he : Topology.IsClosedEmbedding (B.leviEmbedding F.Carrier) :=
    (B.isClosed_leviSubgroup F.Carrier).isClosedEmbedding_subtypeVal.comp
      (B.leviEquivContinuous F.Carrier).toHomeomorph.isClosedEmbedding
  exact he.isCompact_preimage (sphericalOpenSubgroup_isCompact F r)

variable {U : Type uU} {V : Type uV} {W : Type uW}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

set_option hygiene false in
local notation "M" => (borelShape r).Levi F.Carrier
set_option hygiene false in
local notation "K" => borelIntegralDiagonal F r

/-- Restriction of the `i`th uniformizer action to the integral diagonal fixed space. -/
def torusUniformizerAction (ρ : Representation ℂ M V) (i : Fin (r + 1)) :
    Module.End ℂ (fixedVectors ρ K) :=
  (ρ (borelUniformizerLevi F r i)).restrict (by
    intro x hx k
    have hz := Subgroup.mem_center_iff.mp (borelUniformizerLevi_mem_center F r i) k.val
    have hxk : ρ k.val x = x := hx k
    change ρ k.val (ρ (borelUniformizerLevi F r i) x) = ρ (borelUniformizerLevi F r i) x
    rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply, hxk])

theorem torusUniformizerAction_commute (ρ : Representation ℂ M V) (i j : Fin (r + 1)) :
    Commute (torusUniformizerAction F ρ i) (torusUniformizerAction F ρ j) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ρ (borelUniformizerLevi F r i) (ρ (borelUniformizerLevi F r j) x.val) =
    ρ (borelUniformizerLevi F r j) (ρ (borelUniformizerLevi F r i) x.val)
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.mp
    (borelUniformizerLevi_mem_center F r i) (borelUniformizerLevi F r j),
    map_mul, Module.End.mul_apply]

/-- The joint generalized weight space on the integral diagonal fixed vectors of a
 Borel Levi representation. -/
abbrev torusWeightSpace (ρ : Representation ℂ M V) (z : Fin (r + 1) → ℂˣ) :
    Submodule ℂ (fixedVectors ρ K) :=
  jointWeight (torusUniformizerAction F ρ) (fun i => (z i : ℂ))

private theorem torusUniformizerAction_intertwines {ρ : Representation ℂ M V}
    {σ : Representation ℂ M W} (f : ρ.IntertwiningMap σ) (i : Fin (r + 1))
    (x : fixedVectors ρ K) :
    fixedVectorsMap f K (torusUniformizerAction F ρ i x) =
      torusUniformizerAction F σ i (fixedVectorsMap f K x) :=
  Subtype.ext (f.isIntertwining ρ σ (borelUniformizerLevi F r i) x.val)

private def torusWeightMap {ρ : Representation ℂ M V} {σ : Representation ℂ M W}
    (f : ρ.IntertwiningMap σ) (z : Fin (r + 1) → ℂˣ) :
    torusWeightSpace F ρ z →ₗ[ℂ] torusWeightSpace F σ z :=
  jointWeightMap (fixedVectorsMap f K) (torusUniformizerAction_intertwines F f) _

private theorem torusWeightMap_injective {ρ : Representation ℂ M V}
    {σ : Representation ℂ M W} (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (z : Fin (r + 1) → ℂˣ) : Function.Injective (torusWeightMap F f z) :=
  jointWeightMap_injective _ _ _ (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))

private theorem fixedMap_surjective {ρ : Representation ℂ M V}
    {σ : Representation ℂ M W} (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : IsSmooth ρ) : Function.Surjective (fixedVectorsMap f K) := by
  let := F.canonicalTopologicalData.leviTopologicalGroup (borelShape r)
  exact Compact.CharZero.fixedVectorMap_surjective ρ σ hρ (isSmooth_of_surjective f hf hρ)
    (borelIntegralDiagonalOpen F r) (borelIntegralDiagonal_isCompact F r) f hf

private theorem torusWeightMap_surjective {ρ : Representation ℂ M V}
    {σ : Representation ℂ M W} [FiniteDimensional ℂ (fixedVectors ρ K)]
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (hρ : IsSmooth ρ)
    (z : Fin (r + 1) → ℂˣ) : Function.Surjective (torusWeightMap F f z) :=
  jointWeightMap_surjective (torusUniformizerAction_commute F ρ)
    (torusUniformizerAction_commute F σ) _ (fixedMap_surjective F f hf hρ) _ _

/-- Equivariantly isomorphic Levi representations have weight spaces of the same dimension. -/
theorem finrank_torusWeightSpace_equiv {ρ : Representation ℂ M V}
    {σ : Representation ℂ M W} (e : ρ.Equiv σ) (z : Fin (r + 1) → ℂˣ) :
    Module.finrank ℂ (torusWeightSpace F ρ z) = Module.finrank ℂ (torusWeightSpace F σ z) := by
  refine (LinearEquiv.ofBijective (torusWeightMap F e.toIntertwiningMap z)
    ⟨torusWeightMap_injective F _ e.injective z, ?_⟩).finrank_eq
  intro y
  refine ⟨torusWeightMap F e.symm.toIntertwiningMap z y, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact e.apply_symm_apply y.val.val

/-- Generalized weight multiplicities are additive in a short exact sequence of smooth
 Borel Levi representations with finite-dimensional integral diagonal fixed vectors. -/
theorem finrank_torusWeightSpace_exact {ρ : Representation ℂ M U}
    {σ : Representation ℂ M V} {τ : Representation ℂ M W}
    [FiniteDimensional ℂ (fixedVectors σ K)] (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    (z : Fin (r + 1) → ℂˣ) :
    Module.finrank ℂ (torusWeightSpace F σ z) =
      Module.finrank ℂ (torusWeightSpace F ρ z) + Module.finrank ℂ (torusWeightSpace F τ z) := by
  let f' := fixedVectorsMap f K
  let g' := fixedVectorsMap g K
  have hfg : LinearMap.range f' = LinearMap.ker g' := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change g (f v.val) = 0
      exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f.toLinearMap v.val)
    · intro hx
      have hx' : x.val ∈ LinearMap.ker g.toLinearMap :=
        congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (hex.symm ▸ hx')
      have hv' : v ∈ fixedVectors ρ K := by
        intro k
        apply hf
        change f (ρ k.val v) = f v
        rw [f.isIntertwining, show f v = x.val from hv]
        exact x.property k
      exact ⟨⟨v, hv'⟩, Subtype.ext hv⟩
  exact finrank_exact_jointWeight (torusUniformizerAction_commute F σ)
    (torusUniformizerAction_commute F τ) f' g'
    (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))
    (fixedMap_surjective F g hg hσ) hfg (torusUniformizerAction_intertwines F f)
    (torusUniformizerAction_intertwines F g) _

/-- An admissible subquotient has at most the Borel Jacquet multiplicities of the
 admissible ambient representation. -/
theorem borelJacquetMultiset_le_of_subquotient {ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W}
    (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ) (h : IsSubquotientOf ρ σ) :
    borelJacquetMultiset F (r := r) σ ≤ borelJacquetMultiset F (r := r) ρ := by
  classical
  obtain ⟨S, q, hq⟩ := h
  let i : S.toRepresentation.IntertwiningMap ρ :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hi : Function.Injective i := Subtype.val_injective
  have hS := isAdmissible_of_injective i hi hρ
  let T := F.canonicalTopologicalData
  let j := T.normalizedJacquetMap (borelShape r) i
  let g := T.normalizedJacquetMap (borelShape r) q
  have hj : Function.Injective j.toLinearMap := by
    change Function.Injective (T.normalizedJacquetMap (borelShape r) i).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_injective_of_smooth
      (Parabolic.unipotentFiniteContainment F T (borelShape r)) _ hi
      (Parabolic.isSmooth_radical F T (borelShape r) ρ hρ.1)
  have hg : Function.Surjective g.toLinearMap := by
    change Function.Surjective (T.normalizedJacquetMap (borelShape r) q).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_surjective _ hq
  let : FiniteDimensional ℂ (fixedVectors (T.normalizedJacquet (borelShape r) ρ) K) :=
    finiteDimensional_borelJacquetIntegralFixed F (r := r) ρ hρ
  let : FiniteDimensional ℂ (fixedVectors (T.normalizedJacquet (borelShape r) S.toRepresentation) K) :=
    finiteDimensional_borelJacquetIntegralFixed F (r := r) S.toRepresentation hS
  apply Multiset.le_iff_count.mpr
  intro z
  rw [count_borelJacquetMultiset F _ hσ, count_borelJacquetMultiset F _ hρ]
  have h₁ := (torusWeightMap F g z).finrank_le_finrank_of_surjective
    (torusWeightMap_surjective F g hg (T.isSmooth_normalizedJacquet _ hS.1) z)
  have h₂ := (torusWeightMap F j z).finrank_le_finrank_of_injective (torusWeightMap_injective F j hj z)
  exact h₁.trans h₂

/-- The actual Borel Jacquet multiset is invariant under equivariant equivalence. -/
theorem borelJacquetMultiset_eq_of_equiv {ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W}
    (hρ : IsAdmissible ρ) (e : ρ.Equiv σ) :
    borelJacquetMultiset F (r := r) ρ = borelJacquetMultiset F (r := r) σ := by
  classical
  have hσ := (isAdmissible_iff_of_equiv e).mp hρ
  apply Multiset.ext.mpr
  intro z
  rw [count_borelJacquetMultiset F _ hρ, count_borelJacquetMultiset F _ hσ]
  let T := F.canonicalTopologicalData
  let eJ : (T.normalizedJacquet (borelShape r) ρ).Equiv
      (T.normalizedJacquet (borelShape r) σ) :=
    CuspidalSupport.JacquetLength.normalizedJacquetEquiv T (borelShape r) e
  exact finrank_torusWeightSpace_equiv F eJ z

end Torus

end Langlands.BaseChange.WeylJacquet
