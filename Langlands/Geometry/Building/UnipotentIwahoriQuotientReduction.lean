import Langlands.Geometry.Building.IwahoriWeylStatement
import Langlands.GroupScheme.Dynamic.Decomposition

/-!
# Quotient construction for the unipotent Iwahori double-coset bijections

The geometric Iwasawa and corrected normalizer-coset facts remain explicit inputs
to this supporting construction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section QuotientConstruction

variable {Γ : Type*} [Group Γ] (N : Subgroup Γ) (Z : Subgroup N)
  (L I : Subgroup Γ)

/-- The map induced by normalizer representatives, when equality of classes
modulo `Z` implies equality of their double cosets. -/
def normalizerDoubleCosetMap
    (hdescent : ∀ a b : N,
      (QuotientGroup.mk a : N ⧸ Z) = QuotientGroup.mk b →
        DoubleCoset.mk L I (a : Γ) = DoubleCoset.mk L I (b : Γ)) :
    (N ⧸ Z) → DoubleCoset.Quotient (L : Set Γ) I :=
  Quotient.lift (fun n : N => DoubleCoset.mk L I (n : Γ))
    (fun a b hab => hdescent a b (Quotient.sound hab))

@[simp]
theorem normalizerDoubleCosetMap_mk
    (hdescent : ∀ a b : N,
      (QuotientGroup.mk a : N ⧸ Z) = QuotientGroup.mk b →
        DoubleCoset.mk L I (a : Γ) = DoubleCoset.mk L I (b : Γ))
    (n : N) :
    normalizerDoubleCosetMap N Z L I hdescent (QuotientGroup.mk n) =
      DoubleCoset.mk L I (n : Γ) :=
  rfl

/-- A representative criterion and representative surjectivity give an
equivalence with its prescribed value on every representative. -/
theorem exists_normalizerDoubleCosetEquiv
    (hrel : ∀ a b : N,
      DoubleCoset.mk L I (a : Γ) = DoubleCoset.mk L I (b : Γ) ↔
        (QuotientGroup.mk a : N ⧸ Z) = QuotientGroup.mk b)
    (hcover : ∀ g : Γ, ∃ n : N,
      DoubleCoset.mk L I (n : Γ) = DoubleCoset.mk L I g) :
    ∃ e : (N ⧸ Z) ≃ DoubleCoset.Quotient (L : Set Γ) I,
      ∀ n : N, e (QuotientGroup.mk n) = DoubleCoset.mk L I (n : Γ) := by
  let f := normalizerDoubleCosetMap N Z L I (fun a b => (hrel a b).mpr)
  have hinj : Function.Injective f := by
    intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        exact (hrel a b).mp
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨n, hn⟩ := hcover g
      exact ⟨QuotientGroup.mk n, hn⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

end QuotientConstruction

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The corrected normalizer-coset criterion forces normality of the actual
zero subgroup in the full normalizer. -/
theorem normalizerZero_normal_of_unipotentNormalizerCoset
    (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (hcoset : P.UnipotentNormalizerCoset C ν) :
    P.normalizerZero.Normal := by
  refine ⟨?_⟩
  intro z hz n
  have hzI := P.map_centralizerZero_le_parahoric C
    (P.mem_normalizerZero_iff.mp (P.normalizerZero.inv_mem hz))
  have heq : (n : rationalPoints G) =
      1 * ((n * z : normalizerPoints P.i) : rationalPoints G) *
        ((z⁻¹ : normalizerPoints P.i) : rationalPoints G) := by
    simp
  exact (hcoset n (n * z)).mp
    ⟨1, (standardUnipotentPoints P.i ν ∅).one_mem,
      ((z⁻¹ : normalizerPoints P.i) : rationalPoints G), hzI, heq⟩

/-- Every centralizer point preserves the literal standard unipotent,
using its defining intersection of dynamic unipotents. -/
theorem centralizer_conj_mem_standardUnipotent
    (ν : cocharacterLattice P.S) (J : Set (characterLattice P.S))
    (z : rationalPoints P.centralizer.Z) {g : rationalPoints G}
    (hg : g ∈ standardUnipotentPoints P.i ν J) :
    rationalPoints.map P.centralizer.j z * g *
        (rationalPoints.map P.centralizer.j z)⁻¹ ∈
      standardUnipotentPoints P.i ν J := by
  apply (mem_standardUnipotent P.i ν).mpr
  intro ζ hζ
  have hz : rationalPoints.map P.centralizer.j z ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ P.i)).carrier
        (Over.mk (𝟙 _)) :=
    torusCentralizer_le_dynamicCentralizer P.i (CommGroupScheme.groupHom ζ) _
      (by
        have hz0 := map_mem_centralizerPoints P.centralizer.isRepresentedBy z
        rw [← torusCentralizer_carrier_base P.i] at hz0
        exact hz0)
  exact Dynamic.conj_mem_unipotent _
    (Dynamic.centralizer_le_parabolic _ _ hz)
    ((mem_standardUnipotent P.i ν).mp hg ζ hζ)

/-- The actual image of the central zero subgroup normalizes the literal
standard unipotent. -/
theorem map_centralizerZero_le_normalizer_standardUnipotent
    (ν : cocharacterLattice P.S) (J : Set (characterLattice P.S)) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      Subgroup.normalizer (standardUnipotentPoints P.i ν J) := by
  rintro _ ⟨z, _, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact P.centralizer_conj_mem_standardUnipotent ν J z
  · intro hg
    have h := P.centralizer_conj_mem_standardUnipotent ν J z⁻¹ hg
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using h

/-- The first prescribed quotient equivalence, conditional on the two
geometric inputs. -/
theorem exists_unipotentIwahoriDoubleCosetEquiv_of_iwasawa_coset
    (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (hiwasawa : P.IwasawaDecomposition C ν)
    (hcoset : P.UnipotentNormalizerCoset C ν) :
    ∃ e : P.IwahoriWeylGroup ≃
        DoubleCoset.Quotient
          (standardUnipotentPoints P.i ν ∅ : Set (rationalPoints G))
          (P.parahoric C),
      ∀ n : normalizerPoints P.i,
        e (QuotientGroup.mk n) =
          DoubleCoset.mk (standardUnipotentPoints P.i ν ∅)
            (P.parahoric C) (n : rationalPoints G) := by
  let := P.normalizerZero_normal_of_unipotentNormalizerCoset C ν hcoset
  apply exists_normalizerDoubleCosetEquiv (normalizerPoints P.i) P.normalizerZero
    (standardUnipotentPoints P.i ν ∅) (P.parahoric C)
  · intro n n'
    rw [DoubleCoset.eq, hcoset n' n, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  · intro g
    obtain ⟨u, hu, n, p, hp, hg⟩ := hiwasawa g
    exact ⟨n, DoubleCoset.eq.mpr ⟨u, hu, p, hp, hg⟩⟩

/-- Both prescribed equivalences follow from Iwasawa and the corrected
normalizer-coset criterion, retaining the literal pointwise-product target. -/
theorem unipotentIwahoriDoubleCosetBijection_of_iwasawa_coset
    (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (hiwasawa : P.IwasawaDecomposition C ν)
    (hcoset : P.UnipotentNormalizerCoset C ν) :
    P.UnipotentIwahoriDoubleCosetBijection C ν := by
  refine ⟨P.exists_unipotentIwahoriDoubleCosetEquiv_of_iwasawa_coset
    C ν hiwasawa hcoset, ?_⟩
  let := P.normalizerZero_normal_of_unipotentNormalizerCoset C ν hcoset
  let U := standardUnipotentPoints P.i ν ∅
  let Z := P.centralizerZero.map (rationalPoints.map P.centralizer.j)
  let L := U ⊔ Z
  have hL : (L : Set (rationalPoints G)) =
      (standardUnipotentPoints P.i ν ∅ : Set (rationalPoints G)) *
        (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
          Set (rationalPoints G)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U Z
      (P.map_centralizerZero_le_normalizer_standardUnipotent ν ∅)
  have hrel : ∀ n n' : normalizerPoints P.i,
      DoubleCoset.mk L (P.parahoric C) (n : rationalPoints G) =
          DoubleCoset.mk L (P.parahoric C) (n' : rationalPoints G) ↔
        (QuotientGroup.mk n : P.IwahoriWeylGroup) = QuotientGroup.mk n' := by
    intro n n'
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    constructor
    · intro h
      obtain ⟨a, ha, p, hp, hn'⟩ := DoubleCoset.eq.mp h
      rw [← SetLike.mem_coe, hL] at ha
      obtain ⟨u, hu, z, hz, rfl⟩ := Set.mem_mul.mp ha
      obtain ⟨z, hz, rfl⟩ := hz
      let zn : normalizerPoints P.i := P.centralizer.toNormalizer z
      have hzn : zn ∈ P.normalizerZero :=
        Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      have hconj : n⁻¹ * zn * n ∈ P.normalizerZero :=
        (inferInstance : P.normalizerZero.Normal).conj_mem' zn hzn n
      have hp' : (((n⁻¹ * zn * n : normalizerPoints P.i) :
          rationalPoints G) * p) ∈ P.parahoric C :=
        (P.parahoric C).mul_mem
          (P.map_centralizerZero_le_parahoric C
            (P.mem_normalizerZero_iff.mp hconj)) hp
      apply (hcoset n' n).mp
      refine ⟨u, hu, _, hp', ?_⟩
      rw [hn']
      change (u * rationalPoints.map P.centralizer.j z) *
          (n : rationalPoints G) * p =
        u * (n : rationalPoints G) *
          (((n : rationalPoints G)⁻¹ *
            rationalPoints.map P.centralizer.j z * (n : rationalPoints G)) * p)
      simp only [mul_assoc, mul_inv_cancel_left]
    · intro h
      obtain ⟨u, hu, p, hp, hn'⟩ := (hcoset n' n).mpr h
      exact DoubleCoset.eq.mpr ⟨u, (show U ≤ L from le_sup_left) hu, p, hp, hn'⟩
  have hcover : ∀ g : rationalPoints G, ∃ n : normalizerPoints P.i,
      DoubleCoset.mk L (P.parahoric C) (n : rationalPoints G) =
        DoubleCoset.mk L (P.parahoric C) g := by
    intro g
    obtain ⟨u, hu, n, p, hp, hg⟩ := hiwasawa g
    exact ⟨n, DoubleCoset.eq.mpr
      ⟨u, (show U ≤ L from le_sup_left) hu, p, hp, hg⟩⟩
  have htarget : ∃ e : P.IwahoriWeylGroup ≃
      DoubleCoset.Quotient (L : Set (rationalPoints G)) (P.parahoric C),
      ∀ n : normalizerPoints P.i,
        e (QuotientGroup.mk n) = Quotient.mk'' (n : rationalPoints G) :=
    exists_normalizerDoubleCosetEquiv (normalizerPoints P.i) P.normalizerZero
      L (P.parahoric C) hrel hcover
  exact Eq.mp (congrArg
    (fun S : Set (rationalPoints G) =>
      ∃ e : P.IwahoriWeylGroup ≃ DoubleCoset.Quotient S (P.parahoric C),
        ∀ n : normalizerPoints P.i,
          e (QuotientGroup.mk n) = Quotient.mk'' (n : rationalPoints G)) hL) htarget

end ParahoricBuildingData

end Langlands.Geometry.Building
