import Langlands.Galois.Local.SpectralProof
import Langlands.LocalField.Definitions
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section

open IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois

open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

@[instance_reducible]
def localRankOne : (valuation K).RankOne where
  hom' := IsRankLeOne.nonempty.some.emb.comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

@[instance_reducible]
def localNormedField : NontriviallyNormedField K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := localRankOne K
  exact Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

theorem localNormedField_topology :
    (localNormedField K).toNormedField.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace K› := rfl

theorem localNormedField_complete :
    letI := localNormedField K
    CompleteSpace K := by
  let := localNormedField K
  infer_instance

theorem localNormedField_ultrametric :
    letI := localNormedField K
    IsUltrametricDist K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let := localRankOne K
  let := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  infer_instance

theorem localNormedField_integer :
    letI := localNormedField K
    letI := localNormedField_ultrametric K
    (NormedField.valuation (K := K)).integer = (valuation K).integer := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let := localRankOne K
  let := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  ext x
  exact Valued.toNormedField.norm_le_one_iff

theorem localNormedField_le (x y : K) :
    letI := localNormedField K
    ‖x‖ ≤ ‖y‖ ↔ valuation K x ≤ valuation K y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let := localRankOne K
  let := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  exact Valued.toNormedField.norm_le_iff

open IsLocalRing in
def localResidueEquiv :
    letI := localNormedField K
    letI := localNormedField_ultrametric K
    ResidueField (baseIntegers K) ≃+* 𝓀[K] := by
  let := localNormedField K
  let := localNormedField_ultrametric K
  exact ResidueField.mapEquiv (RingEquiv.subringCongr (localNormedField_integer K))

open IsLocalRing in
theorem localResidue_finite :
    letI := localNormedField K
    letI := localNormedField_ultrametric K
    Finite (ResidueField (baseIntegers K)) := by
  let := localNormedField K
  let := localNormedField_ultrametric K
  exact Finite.of_equiv 𝓀[K] (localResidueEquiv K).symm.toEquiv

end Langlands.LocalGalois

namespace Langlands.LocalGalois

variable {K k L M : Type*} [Field K] [Field k] [Field L] [Field M]
    [Algebra K L] [Algebra k M]

def semilinearAutCongr (b : K ≃+* k) (e : L ≃+* M)
    (h : ∀ x, e (algebraMap K L x) = algebraMap k M (b x)) :
    Gal(L/K) ≃* Gal(M/k) := by
  have hi (y : k) : e.symm (algebraMap k M y) = algebraMap K L (b.symm y) := by
    apply e.injective
    rw [e.apply_symm_apply, h, b.apply_symm_apply]
  exact
    { toFun := fun σ =>
        { e.symm.trans (σ.toRingEquiv.trans e) with
          commutes' := by
            intro y
            change e (σ (e.symm (algebraMap k M y))) = algebraMap k M y
            rw [hi, σ.commutes, h, b.apply_symm_apply] }
      invFun := fun τ =>
        { e.trans (τ.toRingEquiv.trans e.symm) with
          commutes' := by
            intro x
            change e.symm (τ (e (algebraMap K L x))) = algebraMap K L x
            rw [h, τ.commutes, hi, b.symm_apply_apply] }
      left_inv := by
        intro σ
        ext x
        change e.symm (e (σ (e.symm (e x)))) = σ x
        rw [e.symm_apply_apply, e.symm_apply_apply]
      right_inv := by
        intro τ
        ext y
        change e (e.symm (τ (e (e.symm y)))) = τ y
        rw [e.apply_symm_apply, e.apply_symm_apply]
      map_mul' := by
        intro σ τ
        ext y
        change e (σ (τ (e.symm y))) = e (σ (e.symm (e (τ (e.symm y)))))
        rw [e.symm_apply_apply] }

end Langlands.LocalGalois

namespace Langlands.LocalGalois

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

def integerInclusion (E : IntermediateField K L) :
    extensionIntegers K E →ₐ[baseIntegers K] extensionIntegers K L where
  toFun x := ⟨(x : E), by
    change spectralNorm K L (algebraMap E L (x : E)) ≤ 1
    rw [← spectralNorm.eq_of_tower (x : E)]
    exact x.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

instance integerInclusion_isLocalHom (E : IntermediateField K L) :
    IsLocalHom (integerInclusion K L E) where
  map_nonunit x hx := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (spectralValuation K E))).mpr
    have h := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (spectralValuation K L))).mp hx
    apply NNReal.eq
    have h' := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    change spectralNorm K L (algebraMap E L (x : E)) = 1 at h'
    change spectralNorm K E (x : E) = 1
    rwa [spectralNorm.eq_of_tower (L := L) (x : E)]

def residueInclusion (E : IntermediateField K L) :
    ResidueField (extensionIntegers K E) →ₐ[ResidueField (baseIntegers K)]
      ResidueField (extensionIntegers K L) :=
  ResidueField.mapAlgHom' (integerInclusion K L E)

end Langlands.LocalGalois

namespace Langlands.LocalGalois

open Polynomial IsLocalRing

theorem lifted_separable {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (φ : A →+* k) [IsLocalHom φ] {g : A[X]} (hg : g.Monic)
    (hsep : (g.map φ).Separable) : g.Separable := by
  nontriviality A
  have hgm : (g.map φ).Monic := hg.map φ
  have hm : (g.map φ).natDegree = g.natDegree := hg.natDegree_map φ
  have hn : (derivative (g.map φ)).natDegree ≤ (derivative g).natDegree := by
    rw [derivative_map]
    exact natDegree_map_le
  have hres : IsUnit (resultant (g.map φ) (derivative (g.map φ))) :=
    (isUnit_resultant_iff_isCoprime hgm).mpr ((separable_def _).mp hsep)
  have hk : resultant (g.map φ) (derivative (g.map φ)) (g.map φ).natDegree
      (derivative g).natDegree =
      resultant (g.map φ) (derivative (g.map φ)) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, hgm.coeff_natDegree, one_pow, one_mul]
  rw [← hk, hm, derivative_map, resultant_map_map] at hres
  exact (separable_def _).mpr ((isUnit_resultant_iff_isCoprime hg).mp (hres.of_map φ _))

theorem residue_isSepClosed {L : Type*} [Field L] [IsSepClosed L]
    (A : ValuationSubring L) : IsSepClosed (ResidueField A) := by
  apply IsSepClosed.of_exists_root
  intro f hf hirr hsep
  obtain ⟨g, hg, hdeg, hmonic⟩ :=
    lifts_and_degree_eq_and_monic
      (mem_lifts_of_surjective (residue_surjective (R := A)) f) hf
  have hgsep : g.Separable := lifted_separable (residue A) hmonic (hg ▸ hsep)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (g.map (algebraMap A L)) (by
    rw [degree_map_eq_of_injective (IsFractionRing.injective A L), hdeg]
    exact ne_of_gt hirr.degree_pos) hgsep.map
  have hi : IsIntegral A x := ⟨g, hmonic, by simpa only [IsRoot, eval_map, aeval_def] using hx⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  have hy : g.eval y = 0 := by
    apply IsFractionRing.injective A L
    simpa only [map_zero, IsRoot, eval_map, eval₂_at_apply] using hx
  refine ⟨residue A y, ?_⟩
  rw [← hg, eval_map, eval₂_at_apply, hy, map_zero]

end Langlands.LocalGalois

namespace Langlands.LocalGalois.SepClosed

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

abbrev closureIntegers := extensionIntegers K Ω

def closureValuation : Valuation Ω ℝ≥0 :=
  spectralValuation K Ω

instance closureValuation_extends :
    (valuation K).HasExtension (closureValuation K Ω) where
  val_isEquiv_comap x y := by
    change valuation K x ≤ valuation K y ↔
      spectralNorm K Ω (algebraMap K Ω x) ≤ spectralNorm K Ω (algebraMap K Ω y)
    simp only [spectralNorm_extends]
    exact (localNormedField_le K x y).symm

def integerMap : 𝒪[K] →+* closureIntegers K Ω :=
  algebraMap (valuation K).valuationSubring (closureValuation K Ω).valuationSubring

@[instance_reducible]
def residueAlgebra : Algebra 𝓀[K] (ResidueField (closureIntegers K Ω)) :=
  ((algebraMap (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K Ω))).comp
    (localResidueEquiv K).symm.toRingHom).toAlgebra

def absoluteInertia : Subgroup Gal(Ω/K) :=
  inertia K Ω

instance absoluteInertia_normal : (absoluteInertia K Ω).Normal :=
  inertia_normal K Ω

variable [IsSepClosed Ω]

theorem residue_isAlgClosure :
    IsAlgClosure (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K Ω)) := by
  have := residue_isSepClosed (closureIntegers K Ω)
  have := Algebra.IsAlgebraic.perfectField (ResidueField (baseIntegers K))
    (L := ResidueField (closureIntegers K Ω))
  exact ⟨inferInstance, inferInstance⟩

def residueClosureEquiv :
    ResidueField (closureIntegers K Ω) ≃+* AlgebraicClosure 𝓀[K] := by
  letI := residue_isAlgClosure K Ω
  exact IsAlgClosure.equivOfEquiv _ _ (localResidueEquiv K)

theorem residueClosureEquiv_base (x : ResidueField (baseIntegers K)) :
    residueClosureEquiv K Ω (algebraMap _ (ResidueField (closureIntegers K Ω)) x) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (localResidueEquiv K x) := by
  let := residue_isAlgClosure K Ω
  exact IsAlgClosure.equivOfEquiv_algebraMap _ _ (localResidueEquiv K) x

def residueClosureAlgEquiv :
    letI := residueAlgebra K Ω
    ResidueField (closureIntegers K Ω) ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K] := by
  letI := residueAlgebra K Ω
  exact
    { residueClosureEquiv K Ω with
      commutes' := by
        intro x
        change residueClosureEquiv K Ω
            (algebraMap (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K Ω))
              ((localResidueEquiv K).symm x)) = _
        rw [residueClosureEquiv_base, RingEquiv.apply_symm_apply] }

def residueTransport :
    Gal(ResidueField (closureIntegers K Ω)/ResidueField (baseIntegers K)) ≃*
      Field.absoluteGaloisGroup 𝓀[K] :=
  semilinearAutCongr (localResidueEquiv K) (residueClosureEquiv K Ω)
    (residueClosureEquiv_base K Ω)

def absoluteResidueHom : Gal(Ω/K) →* Field.absoluteGaloisGroup 𝓀[K] :=
  (residueTransport K Ω).toMonoidHom.comp (residueHom K Ω)

end Langlands.LocalGalois.SepClosed

namespace Langlands.LocalGalois

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

abbrev closureIntegers := extensionIntegers K (AlgebraicClosure K)

def localClosureValuation : Valuation (AlgebraicClosure K) ℝ≥0 :=
  SepClosed.closureValuation K (AlgebraicClosure K)

instance localClosureValuation_extends :
    (valuation K).HasExtension (localClosureValuation K) :=
  SepClosed.closureValuation_extends K (AlgebraicClosure K)

def localIntegerMap : 𝒪[K] →+* closureIntegers K :=
  SepClosed.integerMap K (AlgebraicClosure K)

def localResidueClosureEquiv :
    ResidueField (closureIntegers K) ≃+* AlgebraicClosure 𝓀[K] :=
  SepClosed.residueClosureEquiv K (AlgebraicClosure K)

omit [CharZero K] in
theorem localResidueClosureEquiv_base (x : ResidueField (baseIntegers K)) :
    localResidueClosureEquiv K (algebraMap _ (ResidueField (closureIntegers K)) x) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (localResidueEquiv K x) :=
  SepClosed.residueClosureEquiv_base K (AlgebraicClosure K) x

@[instance_reducible]
def standardResidueAlgebra : Algebra 𝓀[K] (ResidueField (closureIntegers K)) :=
  SepClosed.residueAlgebra K (AlgebraicClosure K)

def localResidueClosureAlgEquiv :
    letI := standardResidueAlgebra K
    ResidueField (closureIntegers K) ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K] :=
  SepClosed.residueClosureAlgEquiv K (AlgebraicClosure K)

end Langlands.LocalGalois

namespace Langlands.LocalGalois

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K
local instance : Finite (ResidueField (baseIntegers K)) := localResidue_finite K

def localResidueTransport :
    Gal(ResidueField (closureIntegers K)/ResidueField (baseIntegers K)) ≃*
      Field.absoluteGaloisGroup 𝓀[K] :=
  SepClosed.residueTransport K (AlgebraicClosure K)

def absoluteResidueHom :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K] :=
  SepClosed.absoluteResidueHom K (AlgebraicClosure K)

def absoluteInertia : Subgroup (Field.absoluteGaloisGroup K) :=
  SepClosed.absoluteInertia K (AlgebraicClosure K)

instance absoluteInertia_normal : (absoluteInertia K).Normal :=
  SepClosed.absoluteInertia_normal K (AlgebraicClosure K)

end Langlands.LocalGalois

namespace Langlands.PadicField

open ValuativeRel IsLocalRing

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

abbrev residueField : Type u := by
  letI := T.valuativeRel
  exact 𝓀[F.Carrier]

abbrev closureIntegers : ValuationSubring (AlgebraicClosure F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact LocalGalois.closureIntegers F.Carrier

def absoluteResidueHom :
    Field.absoluteGaloisGroup F.Carrier →* Field.absoluteGaloisGroup (F.residueField T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteResidueHom F.Carrier

def absoluteInertia : Subgroup (Field.absoluteGaloisGroup F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteInertia F.Carrier

instance absoluteInertia_normal : (F.absoluteInertia T).Normal := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.absoluteInertia_normal F.Carrier

end Langlands.PadicField
