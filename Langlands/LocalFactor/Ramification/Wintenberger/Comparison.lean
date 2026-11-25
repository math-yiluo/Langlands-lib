import Langlands.LocalFactor.Ramification.Wintenberger.APF
import Langlands.LocalFactor.Ramification.Wintenberger.NormField
import Langlands.LocalFactor.Ramification.Wintenberger.NormFieldResidue
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.LocalField.LaurentSeries
import Langlands.Weil.Local.Assembly
import FontaineWintenberger.APF.Tower.AlgebraicResidue
import FontaineWintenberger.APF.Tower.Residue
import FontaineWintenberger.FieldOfNorms.Structure.Laurent
import FontaineWintenberger.FieldOfNorms.Galois.AbsoluteGroup

/-!
# Wintenberger's comparison in the Library's filtrations

For an infinite, arithmetically profinite, totally ramified extension `L` of a `p`-adic field `F`
in its algebraic closure, the field of norms of `L/F` is the Laurent series field `X = k((t))` over
the residue field `k` of `F`, and the absolute Galois group of `L` is isomorphic, as a topological
group, to that of `X`, carrying the upper filtration of `F` restricted to `L` onto the upper
filtration of `X` with the change of index `ψ_{L/F}` (Wintenberger, Corollaires 3.2.3 and 3.3.6).
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe u

section LaurentCongr

variable {k k' : Type*} [Field k] [Field k']

/-- Laurent series over isomorphic fields are isomorphic, coefficient by coefficient. -/
def laurentSeriesCongr (f : k ≃+* k') : LaurentSeries k ≃+* LaurentSeries k' where
  toFun x := x.map f
  invFun x := x.map f.symm
  left_inv x := by
    ext n
    simp
  right_inv x := by
    ext n
    simp
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom
  map_add' x y := HahnSeries.map_add f.toAddMonoidHom

@[simp]
theorem laurentSeriesCongr_coeff (f : k ≃+* k') (x : LaurentSeries k) (n : ℤ) :
    (laurentSeriesCongr f x).coeff n = f (x.coeff n) := rfl

/-- The change of coefficients preserves the `X`-adic valuation. -/
theorem valued_laurentSeriesCongr (f : k ≃+* k') (x : LaurentSeries k) :
    (Valued.v (laurentSeriesCongr f x) : WithZero (Multiplicative ℤ)) = Valued.v x := by
  have key : ∀ (y : LaurentSeries k) (D : WithZero (Multiplicative ℤ)),
      (Valued.v (laurentSeriesCongr f y) : WithZero (Multiplicative ℤ)) ≤ D ↔ Valued.v y ≤ D := by
    intro y D
    by_cases hD : D = 0
    · subst hD
      simp only [le_zero_iff, map_eq_zero]
    · rw [LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero _ hD,
        LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero _ hD]
      simp only [laurentSeriesCongr_coeff, map_eq_zero]
  exact le_antisymm ((key x _).mpr le_rfl) ((key x _).mp le_rfl)

end LaurentCongr

section RestrictScalarsContinuous

variable (R S A : Type*) [Field R] [Field S] [Field A] [Algebra R S] [Algebra S A] [Algebra R A]
  [IsScalarTower R S A]

open scoped Topology in
/-- Restriction of scalars is continuous for the Krull topologies. -/
theorem continuous_restrictScalarsHom [Algebra.IsAlgebraic R A] :
    Continuous (AlgEquiv.restrictScalarsHom R : (A ≃ₐ[S] A) →* (A ≃ₐ[R] A)) := by
  apply continuous_of_continuousAt_one
  change Filter.Tendsto _ (𝓝 1) (𝓝 (AlgEquiv.restrictScalarsHom R (1 : A ≃ₐ[S] A)))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff R A s).mp hs
  have : FiniteDimensional R E := hE
  let b := Module.finBasis R E
  let T : Set A := Set.range fun i => ((b i : E) : A)
  have hT : FiniteDimensional S (IntermediateField.adjoin S T) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨i, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := R) ((b i : E) : A)).tower_top
  apply (krullTopology_mem_nhds_one_iff S A _).mpr
  refine ⟨IntermediateField.adjoin S T, hT, fun σ hσ => hEs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  change σ x = x
  have hxspan : (⟨x, hx⟩ : E) ∈ Submodule.span R (Set.range b) := by
    rw [b.span_eq]
    trivial
  have key : ∀ z : E, z ∈ Submodule.span R (Set.range b) → σ (z : A) = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hσ _ (IntermediateField.subset_adjoin S T ⟨i, rfl⟩)
    | zero => exact map_zero σ
    | add y z _ _ hy hz =>
      rw [IntermediateField.coe_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [IntermediateField.coe_smul, show σ (r • (y : A)) = r • σ (y : A) from
        σ.toAlgHom.map_smul_of_tower r (y : A), hy]
  exact key _ hxspan

end RestrictScalarsContinuous

section Residue

/-- A field `A` of degree one over `R` is `R` itself; the algebra structures are read off an
isomorphism `e`, which saves a typeclass search. -/
def ringEquivOfFinrankEqOne {R A B : Type*} [Field R] [Field A] [Ring B]
    {_iA : Algebra R A} {_iB : Algebra R B} (_e : A ≃ₐ[R] B) (h : Module.finrank R A = 1) :
    R ≃+* A :=
  RingEquiv.ofBijective (algebraMap R A) (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance comparisonPadicFieldNormedField : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance comparisonPadicFieldNormedAlgebra : NormedAlgebra (Padic p) F.Carrier :=
  F.canonicalNormedAlgebra
local instance comparisonPadicFieldLocalField : FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  padicField_isPerfectResidueLocalField F
local instance comparisonPadicFieldCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

theorem padicField_valuationSubring_eq_integers :
    (NormedField.valuation (K := F.Carrier)).valuationSubring.toSubring =
      (LocalField.canonicalTopologicalData (Padic p) F.Carrier (padicBaseNorm_compatible p)).Integers := by
  ext x
  rw [mem_canonicalIntegers_iff]
  rfl

/-- The residue field of the unit ball of the canonical norm of a `p`-adic field is the Library's
residue field of its canonical realization. -/
def padicFieldResidueEquiv :
    IsLocalRing.ResidueField (NormedField.valuation (K := F.Carrier)).valuationSubring ≃+*
      Weil.Local.localResidueField F :=
  IsLocalRing.ResidueField.mapEquiv
    (RingEquiv.subringCongr (padicField_valuationSubring_eq_integers F))

variable {F} (L : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))

/-- The integers of `F` act on an intermediate field through `F`, as in the FontaineWintenberger
library (and not through the algebraic closure). -/
@[instance_reducible]
def integersAlgebra : Algebra (NormedField.valuation (K := F.Carrier)).valuationSubring L :=
  Algebra.ofSubsemiring (NormedField.valuation (K := F.Carrier)).valuationSubring

attribute [local instance high] integersAlgebra

/-- The integral closure of the integers of `F` in an algebraic extension is a local ring (a
valuation ring, by the FontaineWintenberger library). -/
theorem integralClosure_isLocalRing :
    IsLocalRing (integralClosure (NormedField.valuation (K := F.Carrier)).valuationSubring L) :=
  @ValuationRing.isLocalRing _ _ inferInstance
    (FontaineWintenberger.integralClosure_valuationRing F.Carrier _).toPreValuationRing

attribute [local instance] integralClosure_isLocalRing

set_option maxHeartbeats 400000 in
/-- **The residue field of a totally ramified APF extension.** If `L/F` is arithmetically
profinite and `G_L ⊔ G_F^0 = G_F` in the Library's filtration, then the residue field of `L` in the
sense of the FontaineWintenberger library (that of the integral closure of the integers of `F`) is
the Library's residue field of `F`. -/
def apfResidueEquiv (hAPF : FontaineWintenberger.IsAPF F.Carrier L)
    (htot : L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 = ⊤) :
    IsLocalRing.ResidueField (integralClosure (NormedField.valuation (K := F.Carrier)).valuationSubring
      L) ≃+* Weil.Local.localResidueField F := by
  let E := FontaineWintenberger.apfResidueLayer F.Carrier L
  let e := FontaineWintenberger.integralClosureResidueEquiv F.Carrier L E le_rfl
  let s : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] SeparableClosure F.Carrier :=
    IsSepClosure.equiv F.Carrier (AlgebraicClosure F.Carrier) (SeparableClosure F.Carrier)
  let j : E.val →ₐ[F.Carrier] SeparableClosure F.Carrier := s.toAlgHom.comp (L.val.comp E.val.val)
  let S : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
    (L.val.comp E.val.val).fieldRange
  have hj : j.fieldRange = S.map s.toAlgHom := by
    rw [AlgHom.map_fieldRange]
  have hSL : S ≤ L := by
    rintro _ ⟨x, rfl⟩
    exact (E.val.val x).property
  have htop' : S.fixingSubgroup ⊔
      Local.absoluteUpperRamificationGroup (Padic p) F.Carrier (AlgebraicClosure F.Carrier)
        (padicBaseNorm_compatible p) 0 = ⊤ := by
    apply top_unique
    rw [← htot]
    exact sup_le_sup_right (IntermediateField.fixingSubgroup_antitone hSL) _
  have hindex := FontaineWintenberger.apfSubgroup_index_zero_eq_residueDegree F.Carrier E.val j
  rw [hj, apfSubgroup_eq_map (Padic p) (padicBaseNorm_compatible p) F.Carrier s S
    (by norm_num), htop', Subgroup.map_top_of_surjective _ s.autCongr.surjective,
    Subgroup.index_top] at hindex
  exact (e.symm.toRingEquiv.trans (ringEquivOfFinrankEqOne e hindex.symm).symm).trans
    (padicFieldResidueEquiv F)

end Residue

section Comparison

variable {p : ℕ} [Fact p.Prime]

/-- Wintenberger's function `ψ_{L/F}` (1.2.1) in the Library's filtration of a `p`-adic field: the
integral of the index `(G_F^0 : (G_L ⊓ G_F^0) G_F^v)`, extended by the identity below `0`. -/
def wintenbergerPsi (F : PadicField.{u} p)
    (L : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)) (u : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..u,
    (((L.fixingSubgroup ⊓ Padic.absoluteUpperRamificationGroup F 0) ⊔
      Padic.absoluteUpperRamificationGroup F (max v 0)).relIndex
        (Padic.absoluteUpperRamificationGroup F 0) : ℝ)

variable (F : PadicField.{u} p)

local instance comparisonPadicFieldNormedField₂ : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance comparisonPadicFieldNormedAlgebra₂ : NormedAlgebra (Padic p) F.Carrier :=
  F.canonicalNormedAlgebra
local instance comparisonPadicFieldLocalField₂ : FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  padicField_isPerfectResidueLocalField F
local instance comparisonPadicFieldCharZero₂ : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

/-- `wintenbergerPsi` is the function `apfPsi` of the FontaineWintenberger library. -/
theorem wintenbergerPsi_eq_apfPsi (L : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (u : ℝ) : wintenbergerPsi F L u = FontaineWintenberger.apfPsi F.Carrier L u := by
  apply intervalIntegral.integral_congr
  intro v _
  change _ = (FontaineWintenberger.apfIndex F.Carrier L (max v 0) : ℝ)
  rw [apfIndex_eq_relIndex (Padic p) (padicBaseNorm_compatible p) F.Carrier
    (AlgebraicClosure F.Carrier) L L.val (le_max_right v 0), IntermediateField.fieldRange_val]
  rfl

end Comparison

section PadicResidue

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The unit balls of the canonical spectral norm and of the Library's normed-field adapter of a
`p`-adic field coincide. -/
theorem padic_norm_le_one_iff (a : F.Carrier) :
    (letI := F.canonicalTopologicalData.topology
     letI := F.canonicalTopologicalData.valuativeRel
     letI := F.canonicalTopologicalData.localField
     @Norm.norm F.Carrier (LocalGalois.localNormedField F.Carrier).toNorm a ≤ 1) ↔
      @Norm.norm F.Carrier F.canonicalNormedField.toNorm a ≤ 1 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := LocalGalois.localNormedField F.Carrier
  have h1 := LocalGalois.localNormedField_le F.Carrier a 1
  have h2 := mem_canonicalIntegers_iff (Padic p) (padicBaseNorm_compatible p) F.Carrier a
  rw [map_one, norm_one] at h1
  rw [h1]
  exact h2

/-- The integral closure of the integers of `F` in its algebraic closure, for the canonical norm,
and the Library's spectral integers for the normed-field adapter, have the same elements. -/
theorem padic_mem_extensionIntegers_iff (x : AlgebraicClosure F.Carrier) :
    (letI := F.canonicalTopologicalData.topology
     letI := F.canonicalTopologicalData.valuativeRel
     letI := F.canonicalTopologicalData.localField
     letI := LocalGalois.localNormedField F.Carrier
     letI := LocalGalois.localNormedField_ultrametric F.Carrier
     letI := LocalGalois.localNormedField_complete F.Carrier
     x ∈ LocalGalois.extensionIntegers F.Carrier (AlgebraicClosure F.Carrier)) ↔
      (letI := F.canonicalNormedField
       letI := padicField_isUltrametricDist F
       spectralNorm F.Carrier (AlgebraicClosure F.Carrier) x ≤ 1) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hm : (minpoly F.Carrier x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  change (letI := LocalGalois.localNormedField F.Carrier;
    spectralValue (minpoly F.Carrier x) ≤ 1) ↔
    (letI := F.canonicalNormedField; spectralValue (minpoly F.Carrier x) ≤ 1)
  rw [@spectralValue_le_one_iff F.Carrier (LocalGalois.localNormedField F.Carrier).toNormedDivisionRing
    _ hm, @spectralValue_le_one_iff F.Carrier F.canonicalNormedField.toNormedDivisionRing _ hm]
  exact forall_congr' fun n => padic_norm_le_one_iff F _

/-- A Frobenius-power residue action of an automorphism of the algebraic closure of a `p`-adic
field, for the Library's normed-field adapter, is the same Frobenius power for the residue action
of the FontaineWintenberger library, for the canonical norm. -/
theorem padic_algebraicResidueAut_isFrobPow
    (σ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier) {q : ℕ} {M : ℤ}
    (h : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := LocalGalois.localNormedField F.Carrier
      letI := LocalGalois.localNormedField_ultrametric F.Carrier
      letI := LocalGalois.localNormedField_complete F.Carrier
      IsFrobPow (⇑(LocalGalois.residueHom F.Carrier (AlgebraicClosure F.Carrier) σ)) q M) :
    letI := F.canonicalNormedField
    haveI := padicField_isPerfectResidueLocalField F
    haveI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    IsFrobPow (FontaineWintenberger.algebraicResidueAut F.Carrier (AlgebraicClosure F.Carrier) σ)
      q M := by
  let := F.canonicalNormedField
  have := padicField_isPerfectResidueLocalField F
  have : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : Algebra (NormedField.valuation (K := F.Carrier)).valuationSubring
      (AlgebraicClosure F.Carrier) :=
    Algebra.ofSubsemiring (NormedField.valuation (K := F.Carrier)).valuationSubring
  have := integralClosure_isLocalRing' F.Carrier (AlgebraicClosure F.Carrier)
  let A := integralClosure (NormedField.valuation (K := F.Carrier)).valuationSubring
    (AlgebraicClosure F.Carrier)
  have hA : ∀ y : AlgebraicClosure F.Carrier, y ∈ A ↔ _ := fun y =>
    ((FontaineWintenberger.isIntegral_iff_spectralNorm_le_one F.Carrier y).trans
      (padic_mem_extensionIntegers_iff F y).symm)
  let T := F.canonicalTopologicalData
  let nl : NontriviallyNormedField F.Carrier :=
    @LocalGalois.localNormedField F.Carrier _ T.valuativeRel T.topology T.localField
  let hu := @LocalGalois.localNormedField_ultrametric F.Carrier _ T.valuativeRel T.topology
    T.localField
  let hc := @LocalGalois.localNormedField_complete F.Carrier _ T.valuativeRel T.topology
    T.localField
  let B := @LocalGalois.extensionIntegers F.Carrier (AlgebraicClosure F.Carrier) nl hu hc _ _ _
  let Φ : A ≃+* B :=
    { toFun := fun y => ⟨y, (hA y).mp y.2⟩
      invFun := fun y => ⟨y, (hA y).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let Ψ := IsLocalRing.ResidueField.mapEquiv Φ
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  refine FrobPowAt.of_map Ψ.toRingHom Ψ.injective ?_ (h (Ψ (IsLocalRing.residue _ y)))
  rfl

/-- An automorphism of the algebraic closure of a `p`-adic field of residue degree `n` acts on the
residue field of the integral closure of the integers of the canonical norm as the `(-n)`-th power
of the `q`-power map. -/
theorem padic_isFrobPow_of_localResidueDegree
    (σ : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier) (n : Weil.Degree)
    (hn : Weil.Local.localResidueDegree F σ = Weil.frobenius n) :
    letI := F.canonicalNormedField
    haveI := padicField_isPerfectResidueLocalField F
    haveI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    IsFrobPow (FontaineWintenberger.algebraicResidueAut F.Carrier (AlgebraicClosure F.Carrier) σ)
      (Nat.card (Weil.Local.localResidueField F)) (-Multiplicative.toAdd n) := by
  let T := F.canonicalTopologicalData
  exact padic_algebraicResidueAut_isFrobPow F σ
    ((@localResidueDegree_eq_frobenius_iff F.Carrier _ T.valuativeRel T.topology T.localField
      (AlgebraicClosure F.Carrier) _ _ _ _ σ (Multiplicative.toAdd n)).mp hn)

/-- If `G_L ⊔ G_F^0 = G_F`, every integral residue degree is the degree of an automorphism of the
algebraic closure of `F` over `L`. -/
theorem padic_exists_localResidueDegree_eq
    (L : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (htot : L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 = ⊤) (n : Weil.Degree) :
    ∃ a : AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier,
      Weil.Local.localResidueDegree F (AlgEquiv.restrictScalarsHom F.Carrier a) =
        Weil.frobenius n := by
  obtain ⟨g, hg⟩ := Weil.Local.localResidueDegree_surjective F (Weil.frobenius n)
  have hgmem : g ∈ L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 :=
    htot ▸ Subgroup.mem_top g
  obtain ⟨h, hh, m, hm, rfl⟩ := (Subgroup.mem_sup_of_normal_right
    (ht := Padic.absoluteUpperRamificationGroup_normal F 0)).mp hgmem
  have hm' : m ∈ (Weil.Local.localResidueDegree F).toMonoidHom.ker := by
    rw [Weil.Local.localResidueDegree_ker F]
    exact (HerbrandBridge.absoluteUpperCanonicalInertia F) ▸ hm
  have hm0 : Weil.Local.localResidueDegree F m = 1 := hm'
  refine ⟨(IntermediateField.fixingSubgroupEquiv L) ⟨h, hh⟩, ?_⟩
  rw [← hg, map_mul, hm0, mul_one]
  rfl

end PadicResidue

section NormFieldComparison

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] LocalField.Laurent.valuativeRel
attribute [local instance high] integersAlgebra
attribute [local instance] integralClosure_isLocalRing

local instance comparisonPadicFieldNormedField₃ (F : PadicField.{u} p) : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance comparisonPadicFieldNormedAlgebra₃ (F : PadicField.{u} p) : NormedAlgebra (Padic p) F.Carrier :=
  F.canonicalNormedAlgebra
local instance comparisonPadicFieldLocalField₃ (F : PadicField.{u} p) :
    FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  padicField_isPerfectResidueLocalField F
local instance comparisonPadicFieldCharZero₃ (F : PadicField.{u} p) : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

set_option maxHeartbeats 400000 in
/-- **Wintenberger, Corollaires 3.2.3 and 3.3.6, in the Library's filtrations.** Let `L` be an
infinite extension of a `p`-adic field `F` in its algebraic closure, arithmetically profinite
(`G_L ⊔ G_F^v` is open for `v ≥ -1`) and totally ramified (`G_L ⊔ G_F^0 = G_F`), and let
`X = k((t))` be the Laurent series field over the residue field `k` of `F`. Then the absolute Galois
group of `L` is isomorphic, as a topological group, to the automorphism group of a separable closure
of `X`, and the isomorphism carries `G_F^u ∩ G_L` onto the upper group of `X` at
`wintenbergerPsi F L u`, for every `u ≥ -1`. -/
theorem normFieldComparison (F : PadicField.{u} p)
    (L : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (hinf : ¬ Module.Finite F.Carrier L)
    (hopen : ∀ v : ℝ, -1 ≤ v → IsOpen ((L.fixingSubgroup ⊔
      Padic.absoluteUpperRamificationGroup F v : Subgroup (Field.absoluteGaloisGroup F.Carrier)) :
        Set (Field.absoluteGaloisGroup F.Carrier)))
    (htot : L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 = ⊤) :
    ∃ θ : (AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier) ≃ₜ*
        (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F)) ≃ₐ[
          LaurentSeries (Weil.Local.localResidueField F)]
          SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))),
      (∀ u : ℝ, -1 ≤ u →
        ((Padic.absoluteUpperRamificationGroup F u).comap
            (AlgEquiv.restrictScalarsHom F.Carrier)).map θ.toMulEquiv.toMonoidHom =
          Local.localAbsoluteUpperRamificationGroup (LaurentSeries (Weil.Local.localResidueField F))
            (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F)))
            (wintenbergerPsi F L u)) ∧
      ∀ a : AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier,
        Weil.Local.localResidueDegree F (AlgEquiv.restrictScalarsHom F.Carrier a) =
          Weil.Local.SepClosed.localResidueDegree (LaurentSeries (Weil.Local.localResidueField F))
            (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))) (θ a) := by
  have hsepL : IsSepClosure L (AlgebraicClosure F.Carrier) :=
    FontaineWintenberger.closure_isSepClosure F.Carrier L (AlgebraicClosure F.Carrier)
  have hAPF : FontaineWintenberger.IsAPF F.Carrier L := by
    rw [isAPF_iff_isOpen (Padic p) (padicBaseNorm_compatible p) F.Carrier
      (AlgebraicClosure F.Carrier) L L.val, IntermediateField.fieldRange_val]
    exact hopen
  have : Fact (¬ Module.Finite F.Carrier L) := ⟨hinf⟩
  set k := Weil.Local.localResidueField F
  let ι : LaurentSeries k ≃+* FontaineWintenberger.FieldOfNorms F.Carrier L :=
    (laurentSeriesCongr (apfResidueEquiv L hAPF htot).symm).trans
      (FontaineWintenberger.FieldOfNorms.laurentEquiv F.Carrier L
        (FontaineWintenberger.FieldOfNorms.uniformizer F.Carrier L)
        (FontaineWintenberger.FieldOfNorms.valuation_uniformizer F.Carrier L))
  let := ι.toRingHom.toAlgebra
  let : Algebra (LaurentSeries k)
      (FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier)) :=
    ((algebraMap (FontaineWintenberger.FieldOfNorms F.Carrier L)
      (FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier))).comp
        ι.toRingHom).toAlgebra
  have : IsScalarTower (LaurentSeries k) (FontaineWintenberger.FieldOfNorms F.Carrier L)
      (FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hbij : Function.Bijective
      (algebraMap (LaurentSeries k) (FontaineWintenberger.FieldOfNorms F.Carrier L)) :=
    ι.bijective
  have hval : ∀ x y : LaurentSeries k, ValuativeRel.vle x y ↔
      FontaineWintenberger.FieldOfNorms.fieldValuation F.Carrier L (algebraMap _ _ x) ≤
        FontaineWintenberger.FieldOfNorms.fieldValuation F.Carrier L (algebraMap _ _ y) := by
    intro x y
    change (Valued.v x : WithZero (Multiplicative ℤ)) ≤ Valued.v y ↔
      FontaineWintenberger.FieldOfNorms.valuation F.Carrier L
          (FontaineWintenberger.FieldOfNorms.laurentEquiv F.Carrier L _ _
            (laurentSeriesCongr (apfResidueEquiv L hAPF htot).symm x)) ≤
        FontaineWintenberger.FieldOfNorms.valuation F.Carrier L
          (FontaineWintenberger.FieldOfNorms.laurentEquiv F.Carrier L _ _
            (laurentSeriesCongr (apfResidueEquiv L hAPF htot).symm y))
    have h1 := FontaineWintenberger.FieldOfNorms.laurentEquiv_valuation F.Carrier L
      (FontaineWintenberger.FieldOfNorms.uniformizer F.Carrier L)
      (FontaineWintenberger.FieldOfNorms.valuation_uniformizer F.Carrier L)
      (laurentSeriesCongr (apfResidueEquiv L hAPF htot).symm x)
    have h2 := FontaineWintenberger.FieldOfNorms.laurentEquiv_valuation F.Carrier L
      (FontaineWintenberger.FieldOfNorms.uniformizer F.Carrier L)
      (FontaineWintenberger.FieldOfNorms.valuation_uniformizer F.Carrier L)
      (laurentSeriesCongr (apfResidueEquiv L hAPF htot).symm y)
    rw [h1, h2, valued_laurentSeriesCongr, valued_laurentSeriesCongr]
  have := relFieldOfNorms_isSepClosure F.Carrier L (AlgebraicClosure F.Carrier) (LaurentSeries k)
    hbij
  let es : FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier) ≃ₐ[
      LaurentSeries k] SeparableClosure (LaurentSeries k) :=
    IsSepClosure.equiv (LaurentSeries k) _ (SeparableClosure (LaurentSeries k))
  let κ2 := restrictScalarsMulEquiv (LaurentSeries k) (FontaineWintenberger.FieldOfNorms F.Carrier L)
    (FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier)) hbij.2
  let θ0 := (FontaineWintenberger.RelFieldOfNorms.krullEquiv F.Carrier L
    (AlgebraicClosure F.Carrier)).toMulEquiv.trans (κ2.trans es.autCongr)
  have hcont : Continuous θ0 :=
    (continuous_autCongr es).comp ((continuous_restrictScalarsHom (LaurentSeries k)
      (FontaineWintenberger.FieldOfNorms F.Carrier L) _).comp
        (FontaineWintenberger.RelFieldOfNorms.krullEquiv F.Carrier L
          (AlgebraicClosure F.Carrier)).continuous)
  have : IsGalois L (AlgebraicClosure F.Carrier) := inferInstance
  have : T2Space (SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k]
      SeparableClosure (LaurentSeries k)) := krullTopology_t2
  let θ : (AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier) ≃ₜ*
      (SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k] SeparableClosure (LaurentSeries k)) :=
    { θ0 with
      continuous_toFun := hcont
      continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 (f := θ0.toEquiv) }
  refine ⟨θ, fun u hu => ?_, ?_⟩
  swap
  · -- the residue degrees
    have hres : Continuous (AlgEquiv.restrictScalarsHom F.Carrier :
        (AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier) →*
          Field.absoluteGaloisGroup F.Carrier) :=
      continuous_restrictScalarsHom F.Carrier L (AlgebraicClosure F.Carrier)
    have hq : Nat.card (Weil.Local.SepClosed.localResidueField (LaurentSeries k)) = Nat.card k :=
      LocalField.Laurent.residueCardinality_eq k
    have key := eq_of_frobenius
      ((Weil.Local.localResidueDegree F).comp ⟨AlgEquiv.restrictScalarsHom F.Carrier, hres⟩)
      ((Weil.Local.SepClosed.localResidueDegree (LaurentSeries k)
        (SeparableClosure (LaurentSeries k))).comp ⟨θ.toMulEquiv.toMonoidHom, θ.continuous⟩)
      (fun a n hn => relFieldOfNorms_localResidueDegree F.Carrier L (AlgebraicClosure F.Carrier)
        (LaurentSeries k) hbij hval (SeparableClosure (LaurentSeries k)) es a _ hq
        (padic_isFrobPow_of_localResidueDegree F (a.restrictScalars F.Carrier) n hn))
      (padic_exists_localResidueDegree_eq F L htot)
    exact fun a => DFunLike.congr_fun key a
  have hw : -1 ≤ FontaineWintenberger.apfPsi F.Carrier L u :=
    FontaineWintenberger.IsAPF.apfPsi_mem_Ici F.Carrier L hu
  rw [wintenbergerPsi_eq_apfPsi, ← upperRamificationGroupInfinite_eq_padic F u,
    ← FontaineWintenberger.RelFieldOfNorms.upperRamificationGroup_eq_comap F.Carrier L
      (AlgebraicClosure F.Carrier) hu]
  set w := FontaineWintenberger.apfPsi F.Carrier L u
  have hB2 : (FontaineWintenberger.RelFieldOfNorms.normUpperRamificationGroup F.Carrier L
      (AlgebraicClosure F.Carrier) w).map κ2.toMonoidHom =
      Local.localAbsoluteUpperRamificationGroup (LaurentSeries k)
        (FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier)) w := by
    ext ρ
    rw [Subgroup.mem_map_equiv, mem_normUpperRamificationGroup_iff F.Carrier L
      (AlgebraicClosure F.Carrier) (LaurentSeries k) hbij hval _ hw]
    exact Iff.of_eq (congrArg (· ∈ _) (κ2.apply_symm_apply ρ))
  have hclosure : (Local.localAbsoluteUpperRamificationGroup (LaurentSeries k)
      (FontaineWintenberger.RelFieldOfNorms F.Carrier L (AlgebraicClosure F.Carrier)) w).map
        es.autCongr.toMonoidHom =
      Local.localAbsoluteUpperRamificationGroup (LaurentSeries k)
        (SeparableClosure (LaurentSeries k)) w := by
    let := LocalGalois.localNormedField (LaurentSeries k)
    have := LocalGalois.localNormedField_ultrametric (LaurentSeries k)
    have := LocalGalois.localNormedField_complete (LaurentSeries k)
    have := (localField_isPerfectResidueLocalField (LaurentSeries k)).toIsCompleteDiscreteValuedField
    exact absoluteUpperRamificationGroup_map_autCongr (LaurentSeries k)
      (localBaseNorm_compatible (LaurentSeries k)) (LaurentSeries k) es hw
  rw [← hclosure, ← hB2, FontaineWintenberger.RelFieldOfNorms.normUpperRamificationGroup,
    Subgroup.map_map, Subgroup.map_map]
  rfl

end NormFieldComparison

end Langlands.Ramification.Wintenberger
