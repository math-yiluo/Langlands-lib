import Langlands.LocalFactor.WeilDeligne
import Langlands.WeilDeligne.Restriction

/-!
# Transport of Weil–Deligne factor constructions

The existing restriction constructor pulls the action and norm character back
along the same group equivalence. Inertia is its actual inverse image.
-/

noncomputable section

universe uK uG uH uV

namespace Langlands.LocalFactor.WeilDeligne.Transport

variable {K : Type uK} {G : Type uG} {H : Type uH}
  [Field K] [Group G] [Group H] {ν : G →* Kˣ}

open WeilDeligneRepresentation Polynomial

/-- Reindexing by a group equivalence identifies the actual fixed spaces. -/
def invariantsEquiv (e : H ≃* G) (R : FiniteRepresentation.{uK, uG, uV} K G)
    (I : Subgroup G) [I.Normal] :
    FiniteRepresentation.Equiv
      (FiniteRepresentation.invariants (I.comap e.toMonoidHom)
        (FiniteRepresentation.restrict e.toMonoidHom R))
      (FiniteRepresentation.restrict e.toMonoidHom (FiniteRepresentation.invariants I R)) where
  toLinearEquiv := {
    toFun := fun x => ⟨x.val, fun i => by
      have hi : e (e.symm i.val) ∈ I := by simpa only [e.apply_symm_apply] using i.property
      have hx := x.property ⟨e.symm i.val, hi⟩
      change R.representation (e (e.symm i.val)) x.val = x.val at hx
      change R.representation i.val x.val = x.val
      simpa only [e.apply_symm_apply] using hx⟩
    invFun := fun x => ⟨x.val, fun i => x.property ⟨e i.val, i.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  isIntertwining' _ := by ext x; rfl

/-- The fixed monodromy kernel is preserved by reindexing the actual action. -/
def kernelEquiv (e : H ≃* G) (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] :
    FiniteRepresentation.Equiv
      ((restrict e.toMonoidHom A).inertiaKernelRepresentation (I.comap e.toMonoidHom))
      (FiniteRepresentation.restrict e.toMonoidHom (A.inertiaKernelRepresentation I)) :=
  invariantsEquiv e A.kernelRepresentation I

private theorem kernel_map (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] :
    (kernelInInvariants (restrict e.toMonoidHom A) (I.comap e.toMonoidHom)).map
      (invariantsEquiv e A.toFiniteRepresentation I).toLinearEquiv.toLinearMap =
        kernelInInvariants A I := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨(invariantsEquiv e A.toFiniteRepresentation I).toLinearEquiv.symm x, ?_, ?_⟩
    · exact hx
    · exact (invariantsEquiv e A.toFiniteRepresentation I).toLinearEquiv.apply_symm_apply x

/-- The identity on underlying vectors induces the actual quotient equivalence. -/
def quotientEquiv (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] :
    FiniteRepresentation.Equiv
      (quotientRepresentation (restrict e.toMonoidHom A) (I.comap e.toMonoidHom))
      (FiniteRepresentation.restrict e.toMonoidHom (quotientRepresentation A I)) where
  toLinearEquiv := Submodule.Quotient.equiv _ _
    (invariantsEquiv e A.toFiniteRepresentation I).toLinearEquiv (kernel_map e A I)
  isIntertwining' h := by
    apply (kernelInInvariants (restrict e.toMonoidHom A) (I.comap e.toMonoidHom)).quot_hom_ext
    intro x
    rfl

@[simp]
theorem quotientEquiv_mk (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal]
    (x : inertiaRepresentation (restrict e.toMonoidHom A) (I.comap e.toMonoidHom)) :
    quotientEquiv e A I
      ((kernelInInvariants (restrict e.toMonoidHom A) (I.comap e.toMonoidHom)).mkQ x) =
        (kernelInInvariants A I).mkQ (invariantsEquiv e A.toFiniteRepresentation I x) := rfl

theorem conductorCorrection_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] :
    conductorCorrection (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) =
      conductorCorrection A I :=
  (quotientEquiv e A I).toLinearEquiv.finrank_eq

theorem eulerPolynomial_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    eulerPolynomial (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h =
      eulerPolynomial A I (e h) := by
  have hp := LocalFactor.eulerPolynomial_conj (kernelEquiv e A I).toLinearEquiv
    (kernelOperator (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h)
  rw [Representation.Equiv.conj_apply_self] at hp
  exact hp.symm

theorem rationalLFactor_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    rationalLFactor (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h =
      rationalLFactor A I (e h) := by
  change (algebraMap K[X] (RatFunc K)
    (eulerPolynomial (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h))⁻¹ =
      (algebraMap K[X] (RatFunc K) (eulerPolynomial A I (e h)))⁻¹
  rw [eulerPolynomial_restrict]

theorem quotientDeterminant_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    quotientDeterminant (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h =
      quotientDeterminant A I (e h) := by
  have hc := Representation.Equiv.conj_apply_self h (quotientEquiv e A I)
  have hd := LinearMap.det_conj
    (-quotientOperator (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h)
    (quotientEquiv e A I).toLinearEquiv
  change LinearMap.det ((quotientEquiv e A I).toLinearEquiv.conj
    (-quotientOperator (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h)) =
      quotientDeterminant (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h at hd
  rw [map_neg, hc] at hd
  exact hd.symm

theorem quotientCorrectionPolynomial_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    quotientCorrectionPolynomial (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h =
      quotientCorrectionPolynomial A I (e h) := by
  simp only [quotientCorrectionPolynomial, conductorCorrection_restrict,
    quotientDeterminant_restrict]

theorem quotientCorrection_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    quotientCorrection (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h =
      quotientCorrection A I (e h) := by
  unfold quotientCorrection
  rw [quotientCorrectionPolynomial_restrict]

theorem quotientConstantCorrection_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    quotientConstantCorrection (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h =
      quotientConstantCorrection A I (e h) := by
  apply Units.ext
  exact quotientDeterminant_restrict e A I h

theorem quotientCorrectionValue_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) (z : Kˣ) :
    quotientCorrectionValue (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h z =
      quotientCorrectionValue A I (e h) z := by
  simp only [quotientCorrectionValue, quotientConstantCorrection_restrict,
    conductorCorrection_restrict]

/-- Reindexing preserves exactly the finite-value domain, with unchanged coordinate. -/
def regularPointEquiv (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H) :
    RegularPoint (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h ≃
      RegularPoint A I (e h) where
  toFun z := ⟨z.val, by
    change (eulerPolynomial A I (e h)).eval z.val ≠ 0
    rw [← eulerPolynomial_restrict e A I h]
    exact z.property⟩
  invFun z := ⟨z.val, by
    change (eulerPolynomial (restrict e.toMonoidHom A)
      (I.comap e.toMonoidHom) h).eval z.val ≠ 0
    rw [eulerPolynomial_restrict]
    exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem regularPointEquiv_val (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H)
    (z : RegularPoint (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h) :
    (regularPointEquiv e A I h z).val = z.val := rfl

theorem regularLValue_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (h : H)
    (z : RegularPoint (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h) :
    regularLValue (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h z =
      regularLValue A I (e h) (regularPointEquiv e A I h z) := by
  apply Units.ext
  change ((eulerPolynomial (restrict e.toMonoidHom A)
    (I.comap e.toMonoidHom) h).eval z.val)⁻¹ =
      ((eulerPolynomial A I (e h)).eval z.val)⁻¹
  rw [eulerPolynomial_restrict]

section Spectral

variable {ν : G →* ℂˣ}

/-- For the same positive `q`, transport preserves the regular spectral parameter. -/
def spectralRegularPointEquiv (e : H ≃* G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (h : H) (q : ℝ) (hq : 0 < q) :
    SpectralRegularPoint (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h q hq ≃
      SpectralRegularPoint A I (e h) q hq where
  toFun s := ⟨s.val, by
    change (eulerPolynomial A I (e h)).eval (spectralParameter q hq s.val : ℂ) ≠ 0
    rw [← eulerPolynomial_restrict e A I h]
    exact s.property⟩
  invFun s := ⟨s.val, by
    change (eulerPolynomial (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h).eval
      (spectralParameter q hq s.val : ℂ) ≠ 0
    rw [eulerPolynomial_restrict]
    exact s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem spectralRegularPointEquiv_val (e : H ≃* G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (h : H) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint (restrict e.toMonoidHom A)
      (I.comap e.toMonoidHom) h q hq) :
    (spectralRegularPointEquiv e A I h q hq s).val = s.val := rfl

theorem spectralLValue_restrict (e : H ≃* G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (h : H) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint (restrict e.toMonoidHom A)
      (I.comap e.toMonoidHom) h q hq) :
    spectralLValue (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h q hq s =
      spectralLValue A I (e h) q hq (spectralRegularPointEquiv e A I h q hq s) := by
  apply Units.ext
  change ((eulerPolynomial (restrict e.toMonoidHom A) (I.comap e.toMonoidHom) h).eval
    (spectralParameter q hq s.val : ℂ))⁻¹ =
      ((eulerPolynomial A I (e h)).eval (spectralParameter q hq s.val : ℂ))⁻¹
  rw [eulerPolynomial_restrict]

end Spectral

end Langlands.LocalFactor.WeilDeligne.Transport
