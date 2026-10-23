import Langlands.Representation.Unramified.SphericalClassificationStatement
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Whittaker.Iwasawa

/-! # Existence of spherical constituents of unramified principal series -/

noncomputable section

namespace Langlands.Unramified

open Correspondence

universe uF uG uV uW

namespace SphericalExistence

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Admissibility passes to the target of a surjective intertwiner when every
open subgroup contains a compact open subgroup. -/
theorem isAdmissible_of_surjective
    (hG : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (hρ : IsAdmissible ρ) :
    IsAdmissible σ := by
  have hσ : IsSmooth σ := isSmooth_of_surjective f hf hρ.1
  refine ⟨hσ, fun H => ?_⟩
  obtain ⟨K, hK, hKH⟩ := hG H
  have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  have hsurj := Compact.fixedVectorSurjectivity G V W ρ σ hρ.1 hσ K hK f hf
  have : Module.Finite ℂ (fixedVectors σ K.toSubgroup) :=
    Module.Finite.of_surjective (Compact.fixedVectorMap ρ σ f K.toSubgroup) hsurj
  exact finite_fixedVectors_of_le (ρ := σ) (show K.toSubgroup ≤ H.toSubgroup from hKH)

/-- A vector fixed by `P ∩ K` extends to a right `K`-invariant smooth induced
function, when `G = P K` and `K` is open. -/
theorem exists_fixed_smoothFunction (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hPK : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = (p : G) * k)
    (v₀ : V) (hv₀ : ∀ p : P, (p : G) ∈ K → σ p v₀ = v₀) :
    ∃ f : Induction.SmoothFunctions P σ,
      Induction.eval P σ f 1 = v₀ ∧
      f ∈ fixedVectors (Induction.smoothInduced P σ) K.toSubgroup := by
  classical
  choose pOf kOf hkOf hdec using hPK
  have key : ∀ (p : P) (k : G), k ∈ K → ∀ g : G, (p : G) * k = g →
      σ (pOf g) v₀ = σ p v₀ := by
    intro p k hk g hg
    have hmem : ((p⁻¹ * pOf g : P) : G) ∈ K := by
      have he : ((p⁻¹ * pOf g : P) : G) = k * (kOf g)⁻¹ := by
        have h1 : (pOf g : G) = (p : G) * k * (kOf g)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, hg]
          exact (hdec g).symm
        rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, mul_assoc, inv_mul_cancel_left]
      rw [he]
      exact K.mul_mem hk (K.inv_mem (hkOf g))
    calc σ (pOf g) v₀ = σ (p * (p⁻¹ * pOf g)) v₀ := by rw [mul_inv_cancel_left]
      _ = σ p (σ (p⁻¹ * pOf g) v₀) := by rw [map_mul, Module.End.mul_apply]
      _ = σ p v₀ := by rw [hv₀ _ hmem]
  let f : G → V := fun g => σ (pOf g) v₀
  have hcov : ∀ (p : P) (x : G), f ((p : G) * x) = σ p (f x) := by
    intro p x
    have h := key (p * pOf x) (kOf x) (hkOf x) ((p : G) * x) (by
      rw [Subgroup.coe_mul, mul_assoc, ← hdec x])
    change σ (pOf ((p : G) * x)) v₀ = σ p (σ (pOf x) v₀)
    rw [h, map_mul, Module.End.mul_apply]
  have hinv : ∀ (k : K) (x : G), f (x * (k : G)) = f x := by
    intro k x
    exact key (pOf x) (kOf x * k) (K.mul_mem (hkOf x) k.property) (x * k) (by
      rw [← mul_assoc, ← hdec x])
  refine ⟨Induction.smoothFunctionOf P σ f hcov K hinv, ?_, ?_⟩
  · change σ (pOf 1) v₀ = v₀
    rw [key 1 1 K.one_mem 1 (by simp), map_one, Module.End.one_apply]
  · intro k
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hinv k x

end Generic

section Specific

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance sphericalExistenceFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance sphericalExistenceGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance sphericalExistenceGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- An invertible matrix whose entries and inverse entries are integral has
determinant of normalized absolute value one. -/
theorem determinantNorm_eq_one_of_integral (T : F.TopologicalData) {m : ℕ}
    (g : GeneralLinear m F.Carrier) (hg : ∀ a b, g a b ∈ T.Integers)
    (hginv : ∀ a b, g⁻¹ a b ∈ T.Integers) :
    T.determinantNorm m g = 1 := by
  have hdet : ∀ h : GeneralLinear m F.Carrier, (∀ a b, h a b ∈ T.Integers) →
      (GeneralLinear.determinant h : F.Carrier) ∈ T.Integers := by
    intro h hh
    let M : Matrix (Fin m) (Fin m) T.Integers := Matrix.of fun a b => ⟨h a b, hh a b⟩
    have hM : T.Integers.subtype.mapMatrix M = h.val := by
      ext a b
      rfl
    have he : (GeneralLinear.determinant h : F.Carrier) = T.Integers.subtype M.det := by
      rw [RingHom.map_det, hM, Matrix.GeneralLinearGroup.val_det_apply]
    rw [he]
    exact M.det.property
  have h1 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g hg)
  have h2 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g⁻¹ hginv)
  have hprod : T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) *
      T.normalizedAbs (GeneralLinear.determinant g⁻¹ : F.Carrier) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hnn := T.normalizedAbs_nonneg (GeneralLinear.determinant g : F.Carrier)
  have hnn' := T.normalizedAbs_nonneg (GeneralLinear.determinant g⁻¹ : F.Carrier)
  have heq : T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) = 1 := by
    nlinarith
  apply Units.ext
  apply NNReal.eq
  rw [T.determinantNorm_coe]
  simpa using heq

/-- Upper triangular elements of `GL_(r+1)(O_F)` have norm-one diagonal blocks. -/
theorem leviProjection_mem_normOneLevi {r : ℕ} (g : (borelShape r).parabolic F.Carrier)
    (hg : (g : GeneralLinear (r + 1) F.Carrier) ∈ sphericalSubgroup F r) :
    (borelShape r).leviProjection F.Carrier g ∈
      F.canonicalTopologicalData.normOneLevi (borelShape r) := by
  let := F.canonicalTopologicalData.valuativeRel
  have hK := (Conductor.mem_integralSubgroup _ r _).mp hg
  rw [F.canonicalTopologicalData.mem_normOneLevi]
  intro i
  apply determinantNorm_eq_one_of_integral F
  · intro a b
    exact hK.1 _ _
  · intro a b
    rw [← Pi.inv_apply, ← map_inv]
    exact hK.2 _ _

/-- The unramified block characters inducing the ordered principal series. -/
abbrev blockCharacters {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    ∀ i : Fin (borelShape r).length,
      Representation ℂ (GeneralLinear ((borelShape r).size i) F.Carrier) ℂ :=
  fun i => characterRepresentation (determinantQuasiCharacter F 1 (characterTuple F z i))

/-- The inducing representation of the Borel subgroup. -/
abbrev borelInducing {r : ℕ} (z : Fin (r + 1) → ℂˣ) :=
  twist (F.canonicalTopologicalData.parabolicHalfModulus (borelShape r))
    (((borelShape r).blockTensor (blockCharacters F z)).comp
      ((borelShape r).leviProjection F.Carrier))

/-- The pure tensor of ones in the inducing line. -/
abbrev sphericalTensor (r : ℕ) : PiTensorProduct ℂ (fun _ : Fin (borelShape r).length => ℂ) :=
  PiTensorProduct.tprod ℂ fun _ => (1 : ℂ)

theorem sphericalTensor_ne_zero (r : ℕ) : sphericalTensor r ≠ 0 := by
  intro h
  have h1 := congrArg (PiTensorProduct.lift
    (MultilinearMap.mkPiAlgebra ℂ (Fin (borelShape r).length) ℂ)) h
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.mkPiAlgebra_apply] at h1
  simp at h1

/-- The pure tensor of ones is fixed by the Borel elements of `GL_(r+1)(O_F)`. -/
theorem borelInducing_sphericalTensor {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (g : (borelShape r).parabolic F.Carrier)
    (hg : (g : GeneralLinear (r + 1) F.Carrier) ∈ sphericalSubgroup F r) :
    borelInducing F z g (sphericalTensor r) = sphericalTensor r := by
  let T := F.canonicalTopologicalData
  have hm := leviProjection_mem_normOneLevi F g hg
  have hmod : T.leviModulus (borelShape r) ((borelShape r).leviProjection F.Carrier g) = 1 :=
    T.normOneLevi_le_ker_leviModulus (borelShape r) hm
  have hhalf : T.parabolicHalfModulus (borelShape r) g = 1 := by
    rw [T.parabolicHalfModulus_apply]
    exact (T.leviHalfModulus_eq_one (borelShape r) _).mpr hmod
  have hnorm := (T.mem_normOneLevi (borelShape r) _).mp hm
  have hχ : ∀ i, determinantQuasiCharacter F 1 (characterTuple F z i)
      ((borelShape r).leviProjection F.Carrier g i) = 1 := by
    intro i
    exact T.ker_determinantNorm_le_ker_determinantUnramifiedCharacter 1 (z i) (hnorm i)
  change ((T.parabolicHalfModulus (borelShape r) g : ℂˣ) : ℂ) •
      (borelShape r).blockTensor (blockCharacters F z)
        ((borelShape r).leviProjection F.Carrier g) (sphericalTensor r) = sphericalTensor r
  rw [hhalf, Units.val_one, one_smul, GeneralLinear.BlockShape.blockTensor_tprod]
  congr 1
  funext i
  change ((determinantQuasiCharacter F 1 (characterTuple F z i)
      ((borelShape r).leviProjection F.Carrier g i) : ℂˣ) : ℂ) • (1 : ℂ) = 1
  rw [hχ i, Units.val_one, one_smul]

/-- Iwasawa decomposition `GL_(r+1)(F) = B(F) GL_(r+1)(O_F)` for the upper Borel. -/
theorem exists_borel_mul_spherical {r : ℕ} (g : GeneralLinear (r + 1) F.Carrier) :
    ∃ b : (borelShape r).parabolic F.Carrier, ∃ k ∈ sphericalOpenSubgroup F r,
      g = (b : GeneralLinear (r + 1) F.Carrier) * k := by
  let := F.canonicalTopologicalData.valuativeRel
  obtain ⟨b, hb, k, hk, rfl⟩ :=
    GeneralLinear.Iwasawa.exists_upperTriangular_mul (ValuativeRel.valuation F.Carrier) g
  exact ⟨⟨b, (borelShape r).mem_parabolic_of_isUpperTriangular b hb⟩, k, hk, rfl⟩

/-- Every open subgroup of `GL_(r+1)(F)` contains a compact open subgroup. -/
theorem exists_compactOpenSubgroup_le {r : ℕ}
    (H : OpenSubgroup (GeneralLinear (r + 1) F.Carrier)) :
    ∃ K : OpenSubgroup (GeneralLinear (r + 1) F.Carrier),
      IsCompact (K : Set (GeneralLinear (r + 1) F.Carrier)) ∧ K ≤ H := by
  obtain ⟨K, hK, hKH, -⟩ :=
    GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization
      (borelShape r) F.canonicalTopologicalData
      (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, hKH⟩

/-- The unramified block characters are admissible. -/
theorem blockCharacters_isAdmissible {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (i : Fin (borelShape r).length) : IsAdmissible (blockCharacters F z i) := by
  refine ⟨fun v => ?_, fun H => inferInstance⟩
  let H : OpenSubgroup (GeneralLinear ((borelShape r).size i) F.Carrier) :=
    { toSubgroup := (determinantQuasiCharacter F 1 (characterTuple F z i)).ker
      isOpen' := F.canonicalTopologicalData.isOpen_ker_determinantUnramifiedCharacter 1 (z i) }
  refine ⟨H, fun k => ?_⟩
  change ((determinantQuasiCharacter F 1 (characterTuple F z i) k.1 : ℂˣ) : ℂ) • v = v
  rw [k.property, Units.val_one, one_smul]

/-- The ordered normalized unramified principal series is admissible. -/
theorem principalSeriesOfTuple_isAdmissible {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    IsAdmissible (principalSeriesOfTuple F z) :=
  Parabolic.normalizedInductionAdmissibility F F.canonicalTopologicalData (borelShape r) _
    ((borelShape r).blockTensor (blockCharacters F z))
    (FiniteTensor.isAdmissible_external _ (blockCharacters_isAdmissible F z))

/-- Every ordered normalized unramified principal series has an irreducible
admissible spherical constituent. -/
theorem sphericalConstituentExistence : SphericalConstituentExistenceStatement.{uF} := by
  intro p _ F r z
  let π := principalSeriesOfTuple F z
  have hπ : IsAdmissible π := principalSeriesOfTuple_isAdmissible F z
  obtain ⟨f₀, hf₀1, hf₀K⟩ := exists_fixed_smoothFunction
    ((borelShape r).parabolic F.Carrier) (borelInducing F z) (sphericalOpenSubgroup F r)
    (exists_borel_mul_spherical F) (sphericalTensor r)
    (fun b hb => borelInducing_sphericalTensor F z b hb)
  have hf₀ : f₀ ≠ 0 := by
    intro h
    apply sphericalTensor_ne_zero r
    rw [← hf₀1, h]
    rfl
  let sπ : SmoothRep ℂ (GeneralLinear (r + 1) F.Carrier) := SmoothRep.of π hπ.1
  let S : Subrepresentation π :=
    { toSubmodule := Submodule.span ℂ (Set.range fun g => π g f₀)
      apply_mem_toSubmodule := by
        intro g w hw
        have hle : Submodule.span ℂ (Set.range fun g => π g f₀) ≤
            (Submodule.span ℂ (Set.range fun g => π g f₀)).comap (π g) := by
          rw [Submodule.span_le]
          rintro _ ⟨h, rfl⟩
          apply Submodule.subset_span
          refine ⟨g * h, ?_⟩
          change π (g * h) f₀ = π g (π h f₀)
          rw [map_mul, Module.End.mul_apply]
        exact hle hw }
  let W := SmoothRep.subrepresentation sπ S
  let w₀ : W := ⟨f₀, Submodule.subset_span ⟨1, by simp⟩⟩
  have hW : ∀ U : Subrepresentation W.representation, w₀ ∈ U → U = ⊤ := by
    intro U hU
    have hle : Submodule.span ℂ (Set.range fun g => π g f₀) ≤
        U.toSubmodule.map S.toSubmodule.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨W.representation g w₀, U.apply_mem_toSubmodule g hU, rfl⟩
    apply SetLike.ext
    intro w
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hle w.property
    have : u = w := Subtype.ext hu'
    rw [← this]
    exact hu
  have hw₀ : w₀ ≠ 0 := by
    intro h
    exact hf₀ (congrArg Subtype.val h)
  have : Nontrivial W := ⟨⟨w₀, 0, hw₀⟩⟩
  obtain ⟨S', hS'⟩ := CuspidalSupport.QuasicuspidalEmbedding.exists_isCoatom_subrepresentation
    W.representation {w₀} (fun U hU => hW U (hU w₀ (Finset.mem_singleton_self w₀)))
  let Q := SmoothRep.quotient W S'
  let q : W.representation.IntertwiningMap Q.representation := SmoothRep.hom (SmoothRep.mkQ W S')
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective W S'
  have hqker : ∀ x, q x = 0 ↔ x ∈ S' := fun x => Submodule.Quotient.mk_eq_zero _
  have hirr : Q.IsIrreducible :=
    CuspidalSupport.QuasicuspidalEmbedding.isIrreducible_of_isCoatom q hq S' hS' hqker
  have hWadm : IsAdmissible W.representation :=
    isAdmissible_of_injective (SmoothRep.hom (SmoothRep.subtype sπ S))
      (SmoothRep.subtype_injective sπ S) hπ
  have hQadm : IsAdmissible Q.representation :=
    isAdmissible_of_surjective (exists_compactOpenSubgroup_le F) q hq hWadm
  refine ⟨⟨Q, hirr, hQadm⟩, ?_, S, ⟨q.toLinearMap, q.isIntertwining'⟩, hq⟩
  rw [Submodule.ne_bot_iff]
  refine ⟨q w₀, ?_, ?_⟩
  · intro k
    change Q.representation k.1 (q w₀) = q w₀
    refine (Representation.IntertwiningMap.isIntertwining _ _ q k.1 w₀).symm.trans ?_
    congr 1
    exact Subtype.ext (hf₀K k)
  · intro h
    have hmem := (hqker w₀).mp h
    exact hS'.1 (hW S' hmem)

end Specific

end SphericalExistence

end Langlands.Unramified
