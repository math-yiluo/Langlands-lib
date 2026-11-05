import Langlands.GroupScheme.MatrixRepresentation.FrobeniusStableCoordinates
import Langlands.GroupScheme.MatrixRepresentation.InverseMultipleNormalKernel

/-! # Inverse multiple characters via Frobenius-stable coordinates -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
/-- A split-coordinate projection identity survives every coefficient ring map. -/
theorem map_projection_mulVec (f : k →+* k) (B : Matrix n m k) (C : Matrix m n k)
    {v : n → k} (hv : (B * C) *ᵥ v = v) :
    (B.map f * C.map f) *ᵥ (fun r => f (v r)) = fun r => f (v r) := by
  rw [← Matrix.map_mul]
  funext r
  exact ((f.map_mulVec (B * C) v r).symm).trans (congrArg (fun w => f (w r)) hv)

/-- Powered split coordinates of the original character span yield a
character-spanned restriction whenever they are stable. -/
theorem characterSpan_restrictCoordinates_frobenius
    (p : ℕ) [ExpChar k p] (e : ℕ) (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hCB' : C.map (characteristicPowerMap k p k e) *
      B.map (characteristicPowerMap k p k e) = 1)
    (hs : (ρ.frobeniusPower p e).IsStableCoordinates
      (B.map (characteristicPowerMap k p k e))
      (C.map (characteristicPowerMap k p k e)))
    (hcols : ∀ s, (fun r => B r s) ∈ (ρ.restrict i).characterSpan)
    (hproj : ∀ v, v ∈ (ρ.restrict i).characterSpan → (B * C) *ᵥ v = v) :
    ((restrictCoordinates (ρ.frobeniusPower p e)
      (B.map (characteristicPowerMap k p k e))
      (C.map (characteristicPowerMap k p k e)) hCB' hs).restrict i).characterSpan = ⊤ := by
  classical
  let f := characteristicPowerMap k p k e
  let τ := restrictCoordinates (ρ.frobeniusPower p e) (B.map f) (C.map f) hCB' hs
  change (τ.restrict i).characterSpan = ⊤
  have hmaps (v : n → k) (hv : v ∈ (ρ.restrict i).characterSpan) :
      C.map f *ᵥ (fun r => f (v r)) ∈ (τ.restrict i).characterSpan := by
    refine Submodule.iSup_induction (ρ.restrict i).characterSpace
      (motive := fun v => C.map f *ᵥ (fun r => f (v r)) ∈
        (τ.restrict i).characterSpan) hv ?_ ?_ ?_
    · intro ψ v hv
      apply Submodule.mem_iSup_of_mem ((p ^ e) • ψ)
      apply characterSpace_restrictCoordinates (ρ.frobeniusPower p e) i
        (B.map f) (C.map f) hCB' hs
      · simpa only [f, characteristicPowerMap_apply, frobeniusPower_restrict] using
          (frobeniusPower_characterSpace (p := p) (ρ.restrict i) hv e)
      · exact map_projection_mulVec f B C (hproj _ (Submodule.mem_iSup_of_mem ψ hv))
    · simp only [Pi.zero_apply, map_zero]
      change C.map f *ᵥ (0 : n → k) ∈ _
      rw [Matrix.mulVec_zero]
      exact (τ.restrict i).characterSpan.zero_mem
    · intro v w hv hw
      have hadd : (fun r => f ((v + w) r)) =
          (fun r => f (v r)) + (fun r => f (w r)) := by
        funext r
        exact map_add f _ _
      rw [hadd, Matrix.mulVec_add]
      exact (τ.restrict i).characterSpan.add_mem hv hw
  have hsingle (s : m) : Pi.single s (1 : k) ∈ (τ.restrict i).characterSpan := by
    have hCv : C *ᵥ (fun r => B r s) = Pi.single s (1 : k) := by
      funext r
      change (C * B) r s = _
      rw [hCB]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    have he : C.map f *ᵥ (fun r => f (B r s)) = Pi.single s (1 : k) := by
      funext r
      calc
        _ = f ((C *ᵥ (fun r => B r s)) r) :=
          (f.map_mulVec C (fun r => B r s) r).symm
        _ = _ := by rw [hCv]; simp [Pi.single_apply]
    rw [← he]
    exact hmaps _ (hcols s)
  apply eq_top_iff.mpr
  intro w _
  have he : w = ∑ s, w s • Pi.single s (1 : k) := by
    ext r
    simp [Pi.single_apply]
  rw [he]
  exact (τ.restrict i).characterSpan.sum_mem (fun s _ =>
    (τ.restrict i).characterSpan.smul_mem (w s) (hsingle s))

omit [Fintype m] [DecidableEq m] in
/-- In positive characteristic an occurring normal-subgroup character has an
inverse characteristic-power multiple in another actual ambient representation.
The ambient group need not be reduced. -/
theorem exists_inverse_frobenius_normal_characterVector
    [IsAffineHom G.X.hom] [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (ρ : MatrixRepresentation G n) (i : H ⟶ G) [Mono i.hom.hom]
    (hN : (SubgroupFunctor.range i).IsNormal)
    (χ : rationalCharacters H) {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ) (hne : v ≠ 0) :
    ∃ (e d : ℕ) (σ : MatrixRepresentation G (Fin d)) (w : Fin d → k),
      w ≠ 0 ∧ w ∈ (σ.restrict i).characterSpace (-((p ^ e) • χ)) := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    exists_subspace_split_coordinates (ρ.restrict i).characterSpan
  have hrational (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
      (ρ.rationalMatrix g : Matrix n n k) * B =
        B * (C * (ρ.rationalMatrix g : Matrix n n k) * B) := by
    have he : (B * C) * ((ρ.rationalMatrix g : Matrix n n k) * B) =
        (ρ.rationalMatrix g : Matrix n n k) * B := by
      ext r s
      exact congrFun (hproj _
        (rationalMatrix_mulVec_mem_characterSpan ρ i hN g (hcols s))) r
    simpa only [Matrix.mul_assoc] using he.symm
  obtain ⟨e, hs⟩ := exists_frobeniusPower_isStableCoordinates p hp ρ B C hrational
  let f := characteristicPowerMap k p k e
  have hCB' : C.map f * B.map f = 1 := by
    rw [← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _)]
  let τ := restrictCoordinates (ρ.frobeniusPower p e) (B.map f) (C.map f) hCB' hs
  have hvspan : v ∈ (ρ.restrict i).characterSpan := Submodule.mem_iSup_of_mem χ hv
  have hvpow : (fun r => f (v r)) ∈
      ((ρ.frobeniusPower p e).restrict i).characterSpace ((p ^ e) • χ) := by
    simpa only [f, characteristicPowerMap_apply, frobeniusPower_restrict] using
      (frobeniusPower_characterSpace (p := p) (ρ.restrict i) hv e)
  have hprojection := map_projection_mulVec f B C (hproj v hvspan)
  have hv' : C.map f *ᵥ (fun r => f (v r)) ∈
      (τ.restrict i).characterSpace ((p ^ e) • χ) :=
    characterSpace_restrictCoordinates (ρ.frobeniusPower p e) i
      (B.map f) (C.map f) hCB' hs hvpow hprojection
  have hnepow : (fun r => f (v r)) ≠ 0 := by
    intro hz
    apply hne
    funext r
    apply f.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hz r
  have hne' : C.map f *ᵥ (fun r => f (v r)) ≠ 0 := by
    intro hz
    apply hnepow
    rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero] at hprojection
    exact hprojection.symm
  have hspan : (⨆ ψ, (τ.restrict i).characterSpace ψ) = ⊤ :=
    characterSpan_restrictCoordinates_frobenius p e ρ i B C hCB hCB' hs hcols hproj
  obtain ⟨w, hw, hχ⟩ :=
    exists_inverse_characterVector (τ.restrict i) hspan ((p ^ e) • χ) hv' hne'
  refine ⟨e, d, τ.dual, w, hw, ?_⟩
  simpa only [dual_restrict] using hχ

omit [Fintype m] [DecidableEq m] in
/-- Choose an inverse positive multiple character vector using a Frobenius
power. Only positive characteristic and algebraic closedness are required. -/
def inverseFrobeniusNormalCharacterVector
    [IsAffineHom G.X.hom] [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (ρ : MatrixRepresentation G n) (i : H ⟶ G) [Mono i.hom.hom]
    (hN : (SubgroupFunctor.range i).IsNormal)
    (χ : rationalCharacters H) {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ) (hne : v ≠ 0) :
    InverseMultipleNormalCharacterVector i χ := by
  classical
  apply Classical.choice
  obtain ⟨e, d, σ, w, hw, hχ⟩ :=
    exists_inverse_frobenius_normal_characterVector p hp ρ i hN χ hv hne
  have hpos : 0 < p ^ e := pow_pos hp.pos e
  refine ⟨⟨p ^ e - 1, d, σ, w, hw, ?_⟩⟩
  simpa only [Nat.sub_add_cancel hpos] using hχ

/-- Inverse positive multiple occurrence holds for every normal closed
subgroup in positive characteristic over an algebraically closed field. -/
theorem hasInverseMultipleNormalCharacters_of_prime_expChar
    [IsAffineHom G.X.hom] [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (i : H ⟶ G) [Mono i.hom.hom] (hN : (SubgroupFunctor.range i).IsNormal) :
    HasInverseMultipleNormalCharacters i := by
  intro a ρ χ v hne hv
  exact ⟨inverseFrobeniusNormalCharacterVector p hp ρ i hN χ hv hne⟩

end Langlands.GroupScheme.MatrixRepresentation
