import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Aubert.ProductLeviGrothendieck
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Tensor.ExternalSubquotient
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Bijectivity of the actual product-Levi tensor comparison

Proof of `Langlands.Aubert.ProductLeviTensorBijectiveStatement`.
-/

noncomputable section

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped TensorProduct

namespace Langlands.Aubert.ProductLeviTensorBijectiveProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- The external tensor of two irreducible general linear representations is
irreducible on the product Levi. -/
theorem isIrreducible_obj
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) (hB : letI := T.topology; B.IsIrreducible) :
    letI := T.topology
    ((binaryProductLeviTensorFunctor.{uF, uV} F T ha hb).obj (A, B)).IsIrreducible := by
  let := T.topology
  let fam := (T.binaryPairFamilyFunctor ha hb).obj (A, B)
  have hirr : ∀ i, (fam i).representation.IsIrreducible := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hA
    · exact hB
  have hadm : ∀ i, (fam i).IsAdmissible := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact glFiniteLengthAdmissibility.{uF, max uF uV} F T a A
        (SmoothRep.hasFiniteLength_of_isIrreducible hA)
    · exact glFiniteLengthAdmissibility.{uF, max uF uV} F T b B
        (SmoothRep.hasFiniteLength_of_isIrreducible hB)
  have : ∀ i, (fam i).representation.IsIrreducible := hirr
  exact FiniteTensor.isIrreducible_external (fun i => (fam i).representation)
    (fun i φ => (admissibleSchur_scalarEndomorphism _ (hadm i) (hirr i) φ).exists)

/-- Every irreducible representation of the binary product Levi is isomorphic
to the external tensor of two irreducible general linear representations. -/
theorem exists_iso_obj
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ
      ((GeneralLinear.BlockShape.binary a b ha hb).Levi F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible) :
    letI := T.topology
    ∃ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      A.IsIrreducible ∧ B.IsIrreducible ∧
        Nonempty (σ ≅ (binaryProductLeviTensorFunctor.{uF, uV} F T ha hb).obj (A, B)) := by
  let := T.topology
  have hσa := CuspidalSupport.irreducibleLeviAdmissibility.{uF, max uF uV} F T (a + b)
    (GeneralLinear.BlockShape.binary a b ha hb) σ hσ
  obtain ⟨C, hCi, -, ⟨E⟩⟩ := CuspidalSupport.padicLeviAdmissibleFactorization.{uF, max uF uV}
    p F T (a + b) (by omega) (GeneralLinear.BlockShape.binary a b ha hb) σ hσ hσa
  refine ⟨C (0 : Fin 2), C (1 : Fin 2), hCi (0 : Fin 2), hCi (1 : Fin 2), ⟨?_⟩⟩
  have hC : C = (T.binaryPairFamilyFunctor ha hb).obj (C (0 : Fin 2), C (1 : Fin 2)) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rw [Fin.fin_one_eq_zero j]
    rfl
  exact SmoothRep.mkIso (B := FiniteTensor.externalFunctor.obj C) E ≪≫
    FiniteTensor.externalFunctor.mapIso (eqToIso hC)

/-- Isomorphic external tensors of irreducible factors have isomorphic factors. -/
theorem nonempty_iso_of_iso_obj
    (A A' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B B' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) (hA' : letI := T.topology; A'.IsIrreducible)
    (hB : letI := T.topology; B.IsIrreducible) (hB' : letI := T.topology; B'.IsIrreducible)
    (e : letI := T.topology;
      (binaryProductLeviTensorFunctor.{uF, uV} F T ha hb).obj (A, B) ≅
        (binaryProductLeviTensorFunctor.{uF, uV} F T ha hb).obj (A', B')) :
    letI := T.topology
    Nonempty (A ≅ A') ∧ Nonempty (B ≅ B') := by
  let := T.topology
  let J := fun i => ((T.binaryPairFamilyFunctor ha hb).obj (A, B) i).representation
  let ρ := fun i => ((T.binaryPairFamilyFunctor ha hb).obj (A', B') i).representation
  have hρ : ∀ i, (ρ i).IsIrreducible := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hA'
    · exact hB'
  have hsub : WeylBranchPieces.IsSubquotient (FiniteTensor.external J)
      (FiniteTensor.external ρ) :=
    WeylBranchPieces.IsSubquotient.of_equiv (SmoothRep.equivOfIso e)
  have h0 := FiniteTensor.isSubquotient_factor_of_external J ρ hρ hsub (0 : Fin 2)
  have h1 := FiniteTensor.isSubquotient_factor_of_external J ρ hρ hsub (1 : Fin 2)
  obtain ⟨E0⟩ :=
    CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient (A := A.representation)
    (Y := A'.representation) hA hA' h0
  obtain ⟨E1⟩ :=
    CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient (A := B.representation)
    (Y := B'.representation) hB hB' h1
  exact ⟨⟨SmoothRep.mkIso E0⟩, ⟨SmoothRep.mkIso E1⟩⟩

/-- The external tensor label of a pair of irreducible general linear labels. -/
def pairLabel :
    letI := T.topology
    SmoothRep.IrreducibleIsoClass.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.IrreducibleIsoClass.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier) →
      SmoothRep.IrreducibleIsoClass.{0, uF, max uF uV} ℂ
        ((GeneralLinear.BlockShape.binary a b ha hb).Levi F.Carrier) :=
  letI := T.topology
  fun x => Quotient.liftOn₂ x.1 x.2
    (fun A B => SmoothRep.irreducibleIsoClass
      ((binaryProductLeviTensorFunctor.{uF, uV} F T ha hb).obj (A.val, B.val))
      (isIrreducible_obj F T ha hb A.val B.val A.property B.property))
    (fun _ _ _ _ hA hB => by
      obtain ⟨e⟩ := hA
      obtain ⟨f⟩ := hB
      exact SmoothRep.irreducibleIsoClass_eq_of_iso _ _
        ((binaryProductLeviTensorFunctor F T ha hb).mapIso (Iso.prod e f)))

/-- On actual irreducible representatives the label is the external tensor class. -/
theorem pairLabel_mk
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) (hB : letI := T.topology; B.IsIrreducible) :
    letI := T.topology
    pairLabel.{uF, uV} F T ha hb
        (SmoothRep.irreducibleIsoClass A hA, SmoothRep.irreducibleIsoClass B hB) =
      SmoothRep.irreducibleIsoClass ((binaryProductLeviTensorFunctor.{uF, uV} F T ha hb).obj (A, B))
        (isIrreducible_obj F T ha hb A B hA hB) :=
  rfl

/-- The external tensor label map is a bijection of irreducible labels. -/
theorem pairLabel_bijective : Function.Bijective (pairLabel.{uF, uV} F T ha hb) := by
  let := T.topology
  constructor
  · rintro ⟨c, d⟩ ⟨c', d'⟩ h
    induction c using SmoothRep.IrreducibleIsoClass.inductionOn with | h A hA => ?_
    induction d using SmoothRep.IrreducibleIsoClass.inductionOn with | h B hB => ?_
    induction c' using SmoothRep.IrreducibleIsoClass.inductionOn with | h A' hA' => ?_
    induction d' using SmoothRep.IrreducibleIsoClass.inductionOn with | h B' hB' => ?_
    rw [pairLabel_mk, pairLabel_mk] at h
    obtain ⟨e⟩ := (SmoothRep.irreducibleIsoClass_eq_iff _ _).mp h
    obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_iso_of_iso_obj F T ha hb A A' B B' hA hA' hB hB' e
    exact Prod.ext (SmoothRep.irreducibleIsoClass_eq_of_iso hA hA' e0)
      (SmoothRep.irreducibleIsoClass_eq_of_iso hB hB' e1)
  · intro z
    induction z using SmoothRep.IrreducibleIsoClass.inductionOn with | h σ hσ => ?_
    obtain ⟨A, B, hA, hB, ⟨e⟩⟩ := exists_iso_obj F T ha hb σ hσ
    refine ⟨(SmoothRep.irreducibleIsoClass A hA, SmoothRep.irreducibleIsoClass B hB), ?_⟩
    rw [pairLabel_mk]
    exact SmoothRep.irreducibleIsoClass_eq_of_iso _ _ e.symm

end Langlands.Aubert.ProductLeviTensorBijectiveProof

namespace Langlands.Aubert

open ProductLeviTensorBijectiveProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- The actual product-Levi tensor comparison is bijective for every supplied
prerequisite proof. -/
theorem productLeviTensorBijective
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb) :
    ProductLeviTensorBijectiveStatement.{uF, uV} F T ha hb hp := by
  let := T.topology
  let eA := LinearEquiv.ofBijective _
    (GeneralLinear.irreducibleGrothendieckStatement.{uV, uF} a F.Carrier)
  let eB := LinearEquiv.ofBijective _
    (GeneralLinear.irreducibleGrothendieckStatement.{uV, uF} b F.Carrier)
  let eL := LinearEquiv.ofBijective _
    ((GeneralLinear.BlockShape.binary a b ha hb).irreducibleGrothendieckStatement.{uV, uF}
      F.Carrier)
  let μ := Equiv.ofBijective _ (pairLabel_bijective.{uF, uV} F T ha hb)
  let C := TensorProduct.congr eA eB
  let N := (finsuppTensorFinsupp' ℤ _ _).trans ((Finsupp.domLCongr μ).trans eL)
  have base : ∀ c d, productLeviTensorMap F T ha hb hp
      (C (Finsupp.single c 1 ⊗ₜ[ℤ] Finsupp.single d 1)) =
        N (Finsupp.single c 1 ⊗ₜ[ℤ] Finsupp.single d 1) := by
    intro c d
    induction c using SmoothRep.IrreducibleIsoClass.inductionOn with | h A hA => ?_
    induction d using SmoothRep.IrreducibleIsoClass.inductionOn with | h B hB => ?_
    have hfA := SmoothRep.hasFiniteLength_of_isIrreducible hA
    have hfB := SmoothRep.hasFiniteLength_of_isIrreducible hB
    have h1 : eA (Finsupp.single (SmoothRep.irreducibleIsoClass A hA) 1) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofObject ⟨A, hfA⟩ :=
      SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass A hA hfA
    have h2 : eB (Finsupp.single (SmoothRep.irreducibleIsoClass B hB) 1) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofObject ⟨B, hfB⟩ :=
      SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass B hB hfB
    have h3 : eL (Finsupp.single
        (pairLabel F T ha hb (SmoothRep.irreducibleIsoClass A hA,
          SmoothRep.irreducibleIsoClass B hB)) 1) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
          ((binaryProductLeviTensorFunctor F T ha hb).obj (A, B)) (hp.1 _ _ hfA hfB) :=
      SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass _
        (isIrreducible_obj F T ha hb A B hA hB) _
    simp only [C, N, TensorProduct.congr_tmul, LinearEquiv.trans_apply,
      finsuppTensorFinsupp'_single_tmul_single, mul_one, Finsupp.domLCongr_single, μ,
      Equiv.ofBijective_apply]
    rw [h1, h2, h3]
    exact productLeviTensorMap_classes F T ha hb hp ⟨A, hfA⟩ ⟨B, hfB⟩
  have key : ∀ x, productLeviTensorMap F T ha hb hp (C x) = N x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul u v =>
      induction u using Finsupp.induction_linear with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, map_add, map_add, hu, hu']
      | single c m =>
        induction v using Finsupp.induction_linear with
        | zero => simp only [TensorProduct.tmul_zero, map_zero]
        | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, map_add, map_add, hv, hv']
        | single d n =>
          rw [← Finsupp.smul_single_one c m, ← Finsupp.smul_single_one d n,
            TensorProduct.smul_tmul_smul, map_zsmul, map_zsmul, map_zsmul, base]
  have hfun : ⇑(productLeviTensorMap F T ha hb hp) = ⇑N ∘ ⇑C.symm := by
    funext x
    have hx := key (C.symm x)
    rwa [LinearEquiv.apply_symm_apply] at hx
  change Function.Bijective (productLeviTensorMap F T ha hb hp)
  rw [hfun]
  exact N.bijective.comp C.symm.bijective

end Langlands.Aubert
