import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.Picard.InverseLineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.AmplePowerTwistProof
import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyProof

/-! # The Euler characteristic of an inverse line bundle on an abelian variety -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

section Twist

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The untwisted term of the Euler sequence of a coherent module is its Euler
characteristic. -/
lemma coherentEulerSequence_zero_eq (F : X.Modules) [F.IsQuasicoherent]
    (hF : HasFiniteAffineSections F) (L : LineBundle X) (h : HasFiniteCohomology f F) :
    coherentEulerSequence f F hF L 0 = (eulerCharacteristic f F h : ℚ) := by
  have hL := tensorPow_isLocallyFreeRankOne X L 0
  let := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle F _ hL
  change (eulerCharacteristic f (tensorObj F (structureSheaf X)) _ : ℚ) = _
  exact congrArg (Int.cast : ℤ → ℚ) (eulerCharacteristic_eq_of_iso f _ _ (tensorRightUnitor F))

end Twist

variable {K : Type u} [Field K]

/-- **Ample case.** On an abelian scheme of relative dimension `g` over an algebraically
closed field, the published `k^(2g)` scaling theorem gives `χ(N) = (-1)^g χ(H)` for an ample
line bundle `H` and an inverse `N` of `H`. -/
theorem eulerCharacteristic_inverse_of_ample [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : A.HasRelativeDimension g)
    (H N : LineBundle A.X.left) (hH : H.IsAmple)
    (hHN : Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left))
    (hH' : HasFiniteCohomology A.X.hom H.obj) (hN' : HasFiniteCohomology A.X.hom N.obj) :
    eulerCharacteristic A.X.hom N.obj hN' =
      (-1) ^ g * eulerCharacteristic A.X.hom H.obj hH' := by
  obtain ⟨e⟩ := hHN
  refine field_eulerCharacteristic_inverse_of_mul_eq A g hg H N ⟨e⟩
    (eulerCharacteristic A.X.hom H.obj hH' * eulerCharacteristic A.X.hom N.obj hN')
    (fun k hk hHk hNk => ?_) hH' hN'
  rw [algClosedFieldAmpleEulerInverseScaling K A g hg H N hH ⟨e⟩ k hk ⟨tensorPow N.obj k, tensorPow_isLocallyFreeRankOne _ N k⟩
    ⟨tensorPowInverseIso H.obj N.obj e k⟩ hH' hN' hHk hNk, mul_comm]

/-- **From the ample case to all line bundles.** Let `A` be an abelian scheme of relative
dimension `g` over a field, carrying an ample line bundle `H`. Suppose that
`χ(Q) = (-1)^g χ(P)` whenever `P` is ample and `P ⊗ Q` is trivial. Then the same holds for
every pair of line bundles `N`, `M` with `N ⊗ M` trivial. -/
theorem eulerCharacteristic_inverse_of_ampleCase
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : A.HasRelativeDimension g)
    (ampleCase : ∀ P Q : LineBundle A.X.left, P.IsAmple →
      Nonempty (tensorObj P.obj Q.obj ≅ structureSheaf A.X.left) →
        ∀ (hP : HasFiniteCohomology A.X.hom P.obj) (hQ : HasFiniteCohomology A.X.hom Q.obj),
          eulerCharacteristic A.X.hom Q.obj hQ =
            (-1) ^ g * eulerCharacteristic A.X.hom P.obj hP)
    (H : LineBundle A.X.left) (hH : H.IsAmple) (N M : LineBundle A.X.left)
    (hNM : Nonempty (tensorObj N.obj M.obj ≅ structureSheaf A.X.left))
    (hN : HasFiniteCohomology A.X.hom N.obj) (hM : HasFiniteCohomology A.X.hom M.obj) :
    eulerCharacteristic A.X.hom M.obj hM = (-1) ^ g * eulerCharacteristic A.X.hom N.obj hN := by
  have := field_isNoetherian A
  have := field_isSeparated A
  obtain ⟨e⟩ := hNM
  let H' := H.inverse
  let eH : tensorObj H.obj H'.obj ≅ structureSheaf A.X.left := H.tensorInverseIso
  obtain ⟨b₀, hb₀⟩ := amplePowerTwist A.X.left H N hH
  let := N.property.isQuasicoherent
  let := M.property.isQuasicoherent
  have hNs := hasFiniteAffineSections_lineBundle N
  have hMs := hasFiniteAffineSections_lineBundle M
  have hX : topologicalKrullDim A.X.left ≤ g := (field_topologicalKrullDim hg).le
  have hPN := coherentEulerPolynomial_eval A.X.hom N.obj hNs H g
    (HasSupportDimensionLT.of_topologicalKrullDim_le hX _)
  have hPM := coherentEulerPolynomial_eval A.X.hom M.obj hMs H' g
    (HasSupportDimensionLT.of_topologicalKrullDim_le hX _)
  have fin : ∀ L : LineBundle A.X.left, HasFiniteCohomology A.X.hom L.obj := fun L =>
    smoothProperLineBundleFiniteCohomology K A.X.left A.X.hom inferInstance inferInstance L
  have key : coherentEulerPolynomial A.X.hom M.obj hMs H' g =
      C ((-1 : ℚ) ^ g) * coherentEulerPolynomial A.X.hom N.obj hNs H g := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => ((j + b₀ : ℕ) : ℚ))
      (fun a b hab => by simpa using hab) fun j => ?_
    simp only [Set.mem_ofPred_eq, eval_mul, eval_C]
    rw [hPM, hPN]
    let P : LineBundle A.X.left := ⟨tensorObj N.obj (tensorPow H.obj (j + b₀)),
      N.property.tensor pullbackTensorComparisonIsIso
        (tensorPow_isLocallyFreeRankOne _ H (j + b₀))⟩
    let Q : LineBundle A.X.left := ⟨tensorObj M.obj (tensorPow H'.obj (j + b₀)),
      M.property.tensor pullbackTensorComparisonIsIso
        (tensorPow_isLocallyFreeRankOne _ H' (j + b₀))⟩
    have hPa : P.IsAmple := hb₀ (j + b₀) (by omega) P ⟨Iso.refl _⟩
    have ePQ : tensorObj P.obj Q.obj ≅ structureSheaf A.X.left :=
      tensorMiddleFourIso N.obj (tensorPow H.obj (j + b₀)) M.obj (tensorPow H'.obj (j + b₀)) ≪≫
        tensorMapIso e (tensorPowInverseIso H.obj H'.obj eH (j + b₀)) ≪≫
          tensorLeftUnitor (structureSheaf A.X.left)
    have hPQ := ampleCase P Q hPa ⟨ePQ⟩ (fin P) (fin Q)
    change (eulerCharacteristic A.X.hom Q.obj _ : ℚ) =
      (-1) ^ g * (eulerCharacteristic A.X.hom P.obj _ : ℚ)
    exact_mod_cast hPQ
  have h0 := congrArg (Polynomial.eval ((0 : ℕ) : ℚ)) key
  simp only [eval_mul, eval_C] at h0
  rw [hPM, hPN, coherentEulerSequence_zero_eq A.X.hom M.obj hMs H' hM,
    coherentEulerSequence_zero_eq A.X.hom N.obj hNs H hN] at h0
  exact_mod_cast h0

/-- **Conditional assembly.** Ample existence over algebraically closed fields implies the
target. -/
theorem algClosedFieldEulerInverseSymmetry_of_ample
    (ample : Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}) :
    AlgClosedFieldEulerInverseSymmetryStatement.{u} := by
  intro K _ _ A g hg N M hNM hN hM
  obtain ⟨H, hH⟩ := ample K A.toGrp inferInstance inferInstance inferInstance
  exact eulerCharacteristic_inverse_of_ampleCase A g hg
    (fun P Q hP hPQ hP' hQ' => eulerCharacteristic_inverse_of_ample A g hg P Q hP hPQ hP' hQ')
    H hH N M hNM hN hM

/-- On an abelian variety of dimension `g` over an algebraically closed field, if
`N ⊗ M ≅ 𝒪_A` then `χ(M) = (-1)^g χ(N)`. -/
theorem algClosedFieldEulerInverseSymmetry : AlgClosedFieldEulerInverseSymmetryStatement.{u} :=
  algClosedFieldEulerInverseSymmetry_of_ample
    Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence

end Langlands.AbelianScheme
