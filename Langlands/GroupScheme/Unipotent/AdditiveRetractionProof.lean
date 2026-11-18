import Langlands.GroupScheme.Unipotent.AdditiveRetractionStatement
import Langlands.GroupScheme.Rational.ClosedVectorSubgroupRelation
import Langlands.GroupScheme.Rational.TorusLinearization.Euclid

/-! # Retraction onto a closed additive line -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.GroupScheme

open TorusLinearization

private theorem exists_additive_preimage_X {k : Type u} [Field k] {p : ℕ}
    [Fact p.Prime] [CharP k p] {n : ℕ}
    (φ : MvPolynomial (Fin n) k →ₐ[k] k[X]) (hφ : Function.Surjective φ)
    (hcoord : ∀ j, IsAddPoly₁ (φ (MvPolynomial.X j))) :
    ∃ f, IsAddPoly f ∧ φ f = X := by
  classical
  have hmap {f : MvPolynomial (Fin n) k} (hf : IsAddPoly f) : IsAddPoly₁ (φ f) := by
    intro B _ _ x y
    let v (z : B) (j : Fin n) := aeval z (φ (MvPolynomial.X j))
    have hsubst (z : B) : (aeval z).comp φ = MvPolynomial.aeval (v z) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [v]
    have hadd : v (x + y) = v x + v y := funext fun j => hcoord j B x y
    simp only [← AlgHom.comp_apply, hsubst, hadd]
    exact hf B (v x) (v y)
  have hnonzero : ∃ j, φ (MvPolynomial.X j) ≠ 0 := by
    by_contra! hzero
    have hfactor : φ = (Algebra.ofId k k[X]).comp
        (MvPolynomial.aeval (fun _ : Fin n => (0 : k))) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [hzero j]
    obtain ⟨F, hF⟩ := hφ X
    rw [hfactor] at hF
    simpa [AlgHom.comp_apply, Polynomial.algebraMap_apply] using congrArg natDegree hF
  have hex : ∃ d, ∃ f : MvPolynomial (Fin n) k,
      IsAddPoly f ∧ φ f ≠ 0 ∧ (φ f).natDegree = d := by
    obtain ⟨j, hj⟩ := hnonzero
    exact ⟨_, MvPolynomial.X j, isAddPoly_X j, hj, rfl⟩
  obtain ⟨g, hg, hg0, hdeg⟩ := Nat.find_spec hex
  have hdivide (j : Fin n) : ∃ ψ : k[X], φ (MvPolynomial.X j) = ψ.comp (φ g) := by
    obtain ⟨ψ, ρ, hψ, -, hsum, hlt⟩ :=
      (hmap hg).exists_comp_add (p := p) hg0 _ (hcoord j)
    let r := MvPolynomial.X j - aeval g ψ
    have hr : IsAddPoly r := by
      simpa only [r, sub_eq_add_neg] using (isAddPoly_X j).add (hψ.aeval hg).neg
    have hρ : φ r = ρ := by
      rw [show r = MvPolynomial.X j - aeval g ψ from rfl, map_sub,
        ← Polynomial.aeval_algHom_apply, ← comp_eq_aeval, hsum, add_sub_cancel_left]
    have hzero : ρ = 0 := by
      by_contra hn
      have hle := Nat.find_min' hex ⟨r, hr, hρ ▸ hn, rfl⟩
      rw [hρ, ← hdeg] at hle
      exact (not_lt_of_ge hle) (natDegree_lt_natDegree hn hlt)
    exact ⟨ψ, by simpa only [hzero, add_zero] using hsum⟩
  choose ψ hψ using hdivide
  have hfactor : φ = (aeval (φ g)).comp (MvPolynomial.aeval ψ) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, ← comp_eq_aeval]
    exact hψ j
  obtain ⟨F, hF⟩ := hφ X
  have hcomp : (MvPolynomial.aeval ψ F).comp (φ g) = X := by
    rw [comp_eq_aeval, ← AlgHom.comp_apply, ← hfactor, hF]
  have hlin : (φ g).natDegree = 1 := by
    have hd := congrArg natDegree hcomp
    rw [natDegree_comp, natDegree_X] at hd
    exact Nat.eq_one_of_dvd_one ⟨_, hd.symm.trans (Nat.mul_comm _ _)⟩
  obtain ⟨a, ha, b, hab⟩ := Polynomial.natDegree_eq_one.mp hlin
  have hb : b = 0 := by
    simpa [(hmap hg).coeff_zero] using congrArg (fun s : k[X] => s.coeff 0) hab
  refine ⟨a⁻¹ • g, hg.smul _, ?_⟩
  rw [map_smul, ← hab, hb, C_0, add_zero, smul_eq_C_mul, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ ha, C_1, one_mul]

private theorem vector_retraction {k : Type u} [Field k] {p : ℕ}
    [Fact p.Prime] [CharP k p] {n : ℕ}
    (q : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶
      VectorGroup.groupScheme (CommRingCat.of k) n) (hq : IsClosedSubgroup q) :
    ∃ s : VectorGroup.groupScheme (CommRingCat.of k) n ⟶
      VectorGroup.groupScheme (CommRingCat.of k) 1, q ≫ s = 𝟙 _ := by
  let e₁ := VectorGroup.corepresentableBy (CommRingCat.of k) 1
  let π := ClosedVectorSubgroup.coordinatePullback e₁ q
  let line := MvPolynomial.uniqueAlgEquiv k (Fin 1)
  let φ : MvPolynomial (Fin n) k →ₐ[k] k[X] := line.toAlgHom.comp π.hom
  have hline : line.toAlgHom = MvPolynomial.aeval (fun _ => (X : k[X])) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [line, MvPolynomial.uniqueAlgEquiv_apply]
  let : IsClosedImmersion q.hom.hom.left := hq
  have hsurj : Function.Surjective φ :=
    line.surjective.comp (ClosedVectorSubgroup.coordinatePullback_surjective e₁ q)
  have hcoord (j : Fin n) : IsAddPoly₁ (φ (MvPolynomial.X j)) := by
    intro B _ _ x y
    have heval (t : B) : (aeval t).comp line.toAlgHom =
        MvPolynomial.aeval (fun _ : Fin 1 => t) := by
      rw [hline, MvPolynomial.comp_aeval]
      simp
    have htest (t : B) : aeval t (φ (MvPolynomial.X j)) =
        MvPolynomial.aeval (fun _ : Fin 1 => t) (π.hom (MvPolynomial.X j)) := by
      change aeval t (line.toAlgHom (π.hom (MvPolynomial.X j))) = _
      rw [← AlgHom.comp_apply, heval]
    simp only [htest]
    exact ClosedVectorSubgroup.coordinateFamily_primitive e₁ q (CommAlgCat.of (CommRingCat.of k) B)
      (Multiplicative.ofAdd fun _ => x) (Multiplicative.ofAdd fun _ => y) j
  obtain ⟨f, hf, hφf⟩ := exists_additive_preimage_X (p := p) φ hsurj hcoord
  have hπf : π.hom f = MvPolynomial.X (0 : Fin 1) := by
    apply line.injective
    change φ f = line.toAlgHom (MvPolynomial.X 0)
    rw [hφf, hline, MvPolynomial.aeval_X]
  have hprim : VectorGroup.IsPrimitiveFamily (VectorGroup.corepresentableBy (CommRingCat.of k) n)
      (fun _ : Fin 1 => f) := by
    intro A x y _
    exact hf A x.toAdd y.toAdd
  have hcomp : π.hom.comp (MvPolynomial.aeval (fun _ : Fin 1 => f)) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.id_apply,
      show j = 0 from Subsingleton.elim _ _, hπf]
  refine ⟨VectorGroup.quotientMap hprim, ?_⟩
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  rw [Grp.comp_hom_hom, Over.comp_left, Grp.id_hom_hom, Over.id_left]
  have hqSpec : Spec.map (CommRingCat.ofHom π.hom.toRingHom) = q.hom.hom.left :=
    congrArg CommaMorphism.left (ClosedVectorSubgroup.map_coordinatePullback e₁ q)
  have hid : Spec.map (CommRingCat.ofHom π.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval fun _ : Fin 1 => f).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp]
    change Spec.map
      (CommRingCat.ofHom (π.hom.comp (MvPolynomial.aeval fun _ : Fin 1 => f)).toRingHom) = _
    rw [hcomp]
    exact Spec.map_id _
  exact Eq.trans (congrArg₂ (· ≫ ·) hqSpec.symm (VectorGroup.quotientMap_left hprim)) hid

/-- A closed additive line in an elementary unipotent group has a homomorphic retraction. -/
theorem elementaryUnipotentAdditiveRetraction : ElementaryUnipotentAdditiveRetractionStatement.{u} := by
  intro k _ p _ _ G n e he i hi
  have hq : IsClosedSubgroup (i ≫ e) := by
    let : IsClosedImmersion i.hom.hom.left := hi
    let : IsClosedImmersion e.hom.hom.left := he
    change IsClosedImmersion (i.hom.hom.left ≫ e.hom.hom.left)
    infer_instance
  obtain ⟨s, hs⟩ := vector_retraction (p := p) (i ≫ e) hq
  exact ⟨e ≫ s, by rw [← Category.assoc, hs]⟩

end Langlands.GroupScheme
