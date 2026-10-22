import Langlands.Galois.Local.AbsoluteStatement

noncomputable section

open IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

omit [CharZero K] in
theorem localResidueClosureEquiv_residue_base (a : 𝒪[K]) :
    localResidueClosureEquiv K (residue _ (localIntegerMap K a)) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (residue 𝒪[K] a) := by
  have h : algebraMap (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K))
      ((localResidueEquiv K).symm (residue 𝒪[K] a)) =
        residue _ (localIntegerMap K a) := rfl
  rw [← h, localResidueClosureEquiv_base, RingEquiv.apply_symm_apply]

omit [CharZero K] in
theorem localResidue_isAlgClosure :
    letI := standardResidueAlgebra K
    IsAlgClosure 𝓀[K] (ResidueField (closureIntegers K)) := by
  let := standardResidueAlgebra K
  let : Algebra.IsIntegral 𝓀[K] (ResidueField (closureIntegers K)) :=
    ⟨fun x => (isIntegral_algEquiv (localResidueClosureAlgEquiv K)).mp
      (Algebra.IsIntegral.isIntegral ((localResidueClosureAlgEquiv K) x))⟩
  exact
    { isAlgClosed := residue_isAlgClosed _
      isAlgebraic := inferInstance }

omit [CharZero K] in
theorem localClosureValuation_invariant (σ : Field.absoluteGaloisGroup K)
    (x : AlgebraicClosure K) :
    localClosureValuation K (AlgEquiv.toAlgHom σ x) = localClosureValuation K x := by
  apply NNReal.eq
  exact (spectralNorm_eq_of_equiv σ x).symm

end Langlands.LocalGalois

namespace Langlands.LocalGalois

variable {K k L M : Type*} [Field K] [Field k] [Field L] [Field M]
    [Algebra K L] [Algebra k M]

open scoped Topology in
theorem semilinearAutCongr_continuous [Algebra.IsAlgebraic K L]
    (b : K ≃+* k) (e : L ≃+* M)
    (h : ∀ x, e (algebraMap K L x) = algebraMap k M (b x)) :
    Continuous (semilinearAutCongr b e h) := by
  let f := semilinearAutCongr b e h
  apply continuous_of_continuousAt_one f.toMonoidHom (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hEN⟩ := hN
  let := hE
  let B := Module.finBasis k E
  let U : Set Gal(L/K) := ⋂ i, MulAction.stabilizer Gal(L/K) (e.symm (B i))
  have hopen : IsOpen U :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (e.symm (B i))
  have hone : (1 : Gal(L/K)) ∈ U := by
    simp only [U, Set.mem_iInter, SetLike.mem_coe, Subgroup.one_mem, implies_true]
  apply Filter.mem_of_superset (hopen.mem_nhds hone)
  intro σ hσ
  apply hEN
  change f σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, f σ (B i : M) = (B i : M) := by
    intro i
    change e (σ (e.symm (B i))) = (B i : M)
    have hi : σ (e.symm (B i)) = e.symm (B i) := Set.mem_iInter.mp hσ i
    exact (congrArg e hi).trans (e.apply_symm_apply _)
  have heq : (f σ).toLinearMap.comp E.val.toLinearMap = E.val.toLinearMap := B.ext hb
  intro y hy
  exact LinearMap.congr_fun heq (⟨y, hy⟩ : E)

end Langlands.LocalGalois

namespace Langlands.LocalGalois

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem residueInclusion_residue (E : IntermediateField K L)
    (x : extensionIntegers K E) :
    residueInclusion K L E (residue _ x) = residue _ (integerInclusion K L E x) := rfl

theorem residueHom_restrict (E : IntermediateField K L) [Normal K E]
    (σ : Gal(L/K)) (y : ResidueField (extensionIntegers K E)) :
    residueInclusion K L E (residueHom K E (σ.restrictNormal E) y) =
      residueHom K L σ (residueInclusion K L E y) := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  change residue _ (integerInclusion K L E (integerAut K E (σ.restrictNormal E) x)) =
    residue _ (integerAut K L σ (integerInclusion K L E x))
  congr 1
  apply Subtype.ext
  exact σ.restrictNormal_commutes E (x : E)

end Langlands.LocalGalois

namespace Langlands.LocalGalois

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

omit [CharZero K] in
theorem localResidueTransport_continuous : Continuous (localResidueTransport K) :=
  semilinearAutCongr_continuous (localResidueEquiv K) (localResidueClosureEquiv K)
    (localResidueClosureEquiv_base K)

def localResidueTransportEquiv :
    Gal(ResidueField (closureIntegers K)/ResidueField (baseIntegers K)) ≃ₜ*
      Field.absoluteGaloisGroup 𝓀[K] := by
  letI := residueExtension_isAlgClosure K (AlgebraicClosure K)
  letI : IsAlgClosed (ResidueField (closureIntegers K)) := residue_isAlgClosed _
  letI : IsGalois (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K)) := ⟨⟩
  letI : T2Space (Field.absoluteGaloisGroup 𝓀[K]) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure 𝓀[K]/𝓀[K]))
  exact
    { toMulEquiv := localResidueTransport K
      continuous_toFun := localResidueTransport_continuous K
      continuous_invFun :=
        (localResidueTransport_continuous K).continuous_symm_of_equiv_compact_to_t2 }

omit [CharZero K] in
theorem absoluteResidueHom_continuous : Continuous (absoluteResidueHom K) :=
  (localResidueTransport_continuous K).comp (residueHom_continuous K (AlgebraicClosure K))

theorem absoluteResidueHom_surjective : Function.Surjective (absoluteResidueHom K) :=
  (localResidueTransport K).surjective.comp (residueHom_surjective K (AlgebraicClosure K))

theorem absoluteResidueHom_isOpenMap : IsOpenMap (absoluteResidueHom K) :=
  (localResidueTransportEquiv K).toHomeomorph.isOpenMap.comp
    (residueHom_isOpenMap K (AlgebraicClosure K))

omit [CharZero K] in
theorem absoluteResidueHom_residue (σ : Field.absoluteGaloisGroup K)
    (x : closureIntegers K) :
    (AlgEquiv.toAlgHom (absoluteResidueHom K σ))
      (localResidueClosureEquiv K (residue _ x)) =
      localResidueClosureEquiv K (residue _ (integerAut K (AlgebraicClosure K) σ x)) := by
  change localResidueClosureEquiv K
      (residueHom K (AlgebraicClosure K) σ
        ((localResidueClosureEquiv K).symm (localResidueClosureEquiv K (residue _ x)))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

omit [CharZero K] in
theorem absoluteResidueHom_ker : (absoluteResidueHom K).ker = absoluteInertia K := by
  ext σ
  change localResidueTransport K (residueHom K (AlgebraicClosure K) σ) = 1 ↔
    residueHom K (AlgebraicClosure K) σ = 1
  exact (localResidueTransport K).map_eq_one_iff

omit [CharZero K] in
theorem absoluteInertia_mem (σ : Field.absoluteGaloisGroup K) :
    σ ∈ absoluteInertia K ↔ ∀ x : closureIntegers K,
      residue _ (integerAut K (AlgebraicClosure K) σ x) = residue _ x :=
  mem_inertia_iff K (AlgebraicClosure K) σ

omit [CharZero K] in
theorem absoluteInertia_eq_comap_valuationSubring :
    absoluteInertia K = ((closureIntegers K).inertiaSubgroup K).comap
      (decompositionHom K (AlgebraicClosure K)) :=
  inertia_eq_comap_valuationSubring K (AlgebraicClosure K)

omit [CharZero K] in
theorem absoluteInertia_isClosed : IsClosed (absoluteInertia K : Set (Field.absoluteGaloisGroup K)) :=
  inertia_isClosed K (AlgebraicClosure K)

theorem absoluteInertia_compactSpace : CompactSpace (absoluteInertia K) :=
  inertia_compactSpace K (AlgebraicClosure K)

theorem absoluteInertia_totallyDisconnectedSpace : TotallyDisconnectedSpace (absoluteInertia K) :=
  inertia_totallyDisconnectedSpace K (AlgebraicClosure K)

omit [CharZero K] in
theorem absoluteInertia_t2Space : T2Space (absoluteInertia K) :=
  inferInstanceAs (T2Space (inertia K (AlgebraicClosure K)))

def absoluteResidueQuotientEquiv :
    (Field.absoluteGaloisGroup K ⧸ absoluteInertia K) ≃ₜ* Field.absoluteGaloisGroup 𝓀[K] :=
  (residueQuotientEquiv K (AlgebraicClosure K)).trans (localResidueTransportEquiv K)

theorem absoluteResidueQuotientEquiv_mk (σ : Field.absoluteGaloisGroup K) :
    absoluteResidueQuotientEquiv K (QuotientGroup.mk σ) = absoluteResidueHom K σ := rfl

omit [CharZero K] in
theorem closureIntegers_integral (x : AlgebraicClosure K) :
    IsIntegral 𝒪[K] x ↔ x ∈ closureIntegers K := by
  let e := RingEquiv.subringCongr (localNormedField_integer K)
  have hi : IsIntegral (baseIntegers K) x ↔ IsIntegral 𝒪[K] x :=
    e.isIntegral_iff (by ext y; rfl) x
  exact hi.symm.trans (integral_iff_mem_spectralIntegers K (AlgebraicClosure K) x)

omit [CharZero K] in
theorem absoluteResidueHom_restrict (E : IntermediateField K (AlgebraicClosure K))
    [Normal K E] (σ : Field.absoluteGaloisGroup K)
    (y : ResidueField (extensionIntegers K E)) :
    (AlgEquiv.toAlgHom (absoluteResidueHom K σ))
        (localResidueClosureEquiv K (residueInclusion K (AlgebraicClosure K) E y)) =
      localResidueClosureEquiv K (residueInclusion K (AlgebraicClosure K) E
        (residueHom K E (σ.restrictNormal E) y)) := by
  change localResidueClosureEquiv K
      (residueHom K (AlgebraicClosure K) σ
        ((localResidueClosureEquiv K).symm (localResidueClosureEquiv K _))) = _
  rw [RingEquiv.symm_apply_apply]
  exact congrArg (localResidueClosureEquiv K)
    (residueHom_restrict K (AlgebraicClosure K) E σ y).symm

end Langlands.LocalGalois

namespace Langlands.PadicField

open ValuativeRel IsLocalRing

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

theorem residueField_finite : Finite (F.residueField T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

theorem absoluteResidueHom_continuous : Continuous (F.absoluteResidueHom T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteResidueHom_continuous F.Carrier

theorem absoluteResidueHom_surjective : Function.Surjective (F.absoluteResidueHom T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact LocalGalois.absoluteResidueHom_surjective F.Carrier

theorem absoluteResidueHom_isOpenMap : IsOpenMap (F.absoluteResidueHom T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact LocalGalois.absoluteResidueHom_isOpenMap F.Carrier

theorem absoluteResidueHom_ker : (F.absoluteResidueHom T).ker = F.absoluteInertia T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteResidueHom_ker F.Carrier

theorem absoluteInertia_isClosed :
    IsClosed (F.absoluteInertia T : Set (Field.absoluteGaloisGroup F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteInertia_isClosed F.Carrier

theorem absoluteInertia_compactSpace : CompactSpace (F.absoluteInertia T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact LocalGalois.absoluteInertia_compactSpace F.Carrier

theorem absoluteInertia_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (F.absoluteInertia T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact LocalGalois.absoluteInertia_totallyDisconnectedSpace F.Carrier

def absoluteResidueQuotientEquiv :
    (Field.absoluteGaloisGroup F.Carrier ⧸ F.absoluteInertia T) ≃ₜ*
      Field.absoluteGaloisGroup (F.residueField T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact LocalGalois.absoluteResidueQuotientEquiv F.Carrier

theorem absoluteResidueQuotientEquiv_mk (σ : Field.absoluteGaloisGroup F.Carrier) :
    F.absoluteResidueQuotientEquiv T (QuotientGroup.mk σ) = F.absoluteResidueHom T σ := rfl

end Langlands.PadicField

namespace Langlands.LocalGalois

open ValuativeRel

universe u

theorem localResidueProperties (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] :
    LocalResidueProperties K := by
  refine ⟨localNormedField_topology K, ?_⟩
  let := localNormedField K
  let := localNormedField_ultrametric K
  let := localNormedField_complete K
  exact ⟨inferInstance, inferInstance, localNormedField_integer K,
    closureIntegers_integral K, localClosureValuation_invariant K,
    localResidue_isAlgClosure K, localResidueClosureEquiv_residue_base K,
    absoluteResidueHom_residue K, absoluteResidueHom_continuous K,
    absoluteResidueHom_surjective K, absoluteResidueHom_isOpenMap K,
    absoluteResidueHom_ker K, absoluteInertia_mem K,
    absoluteInertia_eq_comap_valuationSubring K, inferInstance,
    absoluteInertia_isClosed K, absoluteInertia_compactSpace K,
    absoluteInertia_totallyDisconnectedSpace K, absoluteInertia_t2Space K,
    ⟨absoluteResidueQuotientEquiv K, absoluteResidueQuotientEquiv_mk K⟩,
    fun E [_] σ y => absoluteResidueHom_restrict K E σ y⟩

theorem padicResidueExactness : PadicResidueExactness := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact localResidueProperties F.Carrier

end Langlands.LocalGalois
