import Langlands.Algebra.GradedHopf.Section
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.Rational.CharacterLatticeProof

/-! # Split unipotence of graded unipotent Hopf algebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Algebra.GradedHopf

section Geometry

variable {k : Type u} [Field k] (A : CommHopfAlgCat.{u} (CommRingCat.of k))

/-- Smoothness of `Spec A` gives formal smoothness and finite type of `A`. -/
theorem smooth_hopfSpec_iff :
    Smooth ((hopfSpec (CommRingCat.of k)).obj (op A)).X.hom ↔
      Algebra.Smooth (CommRingCat.of k) A :=
  GroupScheme.DynamicSmooth.smooth_algSpec_iff (CommAlgCat.of (CommRingCat.of k) A)

/-- The coordinate algebra of a smooth connected affine group over a field is a domain. -/
theorem isDomain_of_hopfSpec
    (hSmooth : Smooth ((hopfSpec (CommRingCat.of k)).obj (op A)).X.hom)
    (hConn : ConnectedSpace ((hopfSpec (CommRingCat.of k)).obj (op A)).X.left) :
    IsDomain A := by
  have hA : Algebra.Smooth (CommRingCat.of k) A := (smooth_hopfSpec_iff A).1 hSmooth
  have : Algebra.FiniteType (CommRingCat.of k) A := inferInstance
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) A
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of k) A))) := hSmooth
  have : ConnectedSpace (Spec (CommRingCat.of A)) := hConn
  have := GroupScheme.CharacterLatticeProof.isIntegral_of_smooth k
    (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of k) A)))
  exact (affine_isIntegral_iff (CommRingCat.of A)).mp this

/-- If every element of `A` is a scalar, every point of `Spec A` is the identity, so the group has
the split series of length `0`. -/
theorem hasSplitSeries_zero_of_forall_mem_range [Nontrivial A]
    (hA : ∀ a : A, a ∈ Set.range (algebraMap (CommRingCat.of k) A)) :
    GroupScheme.RelativeRoot.HasSplitSeries 0 ((hopfSpec (CommRingCat.of k)).obj (op A)) := by
  set H := (hopfSpec (CommRingCat.of k)).obj (op A)
  have hbij : Function.Bijective (algebraMap (CommRingCat.of k) A) :=
    ⟨(algebraMap (CommRingCat.of k) A).injective, fun a => hA a⟩
  have hiso : IsIso (CommRingCat.ofHom (algebraMap (CommRingCat.of k) A)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have hX : IsIso H.X.hom := by
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of k) A)))
    infer_instance
  have hpt : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ H.X), x = y := by
    intro T x y
    ext
    rw [← cancel_mono H.X.hom, Over.w x, Over.w y]
  change GroupScheme.SubgroupFunctor.range (𝟙 H) = ⊥
  refine GroupScheme.SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
  simp only [GroupScheme.SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro _
    exact hpt T x 1
  · intro hx
    rw [hx]
    exact one_mem _

end Geometry

section QuotientData

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A] {𝒜 : ℤ → Submodule k A}
  (J : Ideal A) [(J.restrictScalars k).IsCoideal]

/-- Every degree-`0` element of the augmentation ideal of the quotient lies in its square,
provided this holds in `A`. -/
theorem quot_h0
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) :
    ∀ a ∈ quotGrade 𝒜 J (AddMonoidHom.id ℤ) 0, Bialgebra.counitAlgHom k (A ⧸ J) a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k (A ⧸ J)) ^ 2 := by
  intro a ha hεa
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_quotGrade ha
  have hεb : Bialgebra.counitAlgHom k A b = 0 := by
    rw [← hεa]
    exact (Bialgebra.Quotient.counit_mk J b).symm
  have hle : (RingHom.ker (Bialgebra.counitAlgHom k A)).map (Ideal.Quotient.mk J) ≤
      RingHom.ker (Bialgebra.counitAlgHom k (A ⧸ J)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact (Bialgebra.Quotient.counit_mk J x).trans hx
  have h1 : Ideal.Quotient.mk J b ∈
      ((RingHom.ker (Bialgebra.counitAlgHom k A)) ^ 2).map (Ideal.Quotient.mk J) :=
    Ideal.mem_map_of_mem _ (h0 b hb hεb)
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hle 2 h1

/-- The images of matrix coefficients in a quotient bialgebra are matrix coefficients for the
quotient grading. -/
def GradedMatrixCoefficients.quot (G : GradedMatrixCoefficients 𝒜) :
    GradedMatrixCoefficients (quotGrade 𝒜 J (AddMonoidHom.id ℤ)) where
  n := G.n
  w := G.w
  M i j := Ideal.Quotient.mk J (G.M i j)
  comul_apply i j := by
    rw [Bialgebra.Quotient.comul_mk, G.comul_apply, map_sum]
    simp only [TensorProduct.map_tmul]
    rfl
  counit_apply i j := by rw [Bialgebra.Quotient.counit_mk, G.counit_apply]
  mem i j := mk_mem_quotGrade (e := AddMonoidHom.id ℤ) (G.mem i j)
  adjoin_eq_top := by
    have h := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ k J)) G.adjoin_eq_top
    rw [AlgHom.map_adjoin, Algebra.map_top,
      (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective k J), ← Set.range_comp] at h
    exact h

theorem GradedMatrixCoefficients.quot_M (G : GradedMatrixCoefficients 𝒜) (i j : Fin G.n) :
    (G.quot J).M i j = Ideal.Quotient.mk J (G.M i j) :=
  rfl

end QuotientData

section Induction

variable {k : Type u} [Field k]

/-- **Split unipotence of graded unipotent Hopf algebras.** Let `A` be a commutative Hopf
algebra over a field `k` with `Spec A` smooth and connected, and `𝒜` a `ℤ`-grading making `A`
a graded bialgebra, such that every degree-`0` element of the augmentation ideal lies in its
square. Suppose `A` is generated by the entries of an upper unitriangular multiplicative
matrix of homogeneous elements. Then `Spec A` is split unipotent. -/
theorem isSplitUnipotent_of_graded (A : CommHopfAlgCat.{u} (CommRingCat.of k))
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (h𝒜 : IsGradedBialgebra 𝒜)
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2)
    (G : GradedMatrixCoefficients 𝒜) (hdiag : ∀ i, G.M i i = 1)
    (hlow : ∀ i j, j < i → G.M i j = 0)
    (hSmooth : Smooth ((hopfSpec (CommRingCat.of k)).obj (op A)).X.hom)
    (hConn : ConnectedSpace ((hopfSpec (CommRingCat.of k)).obj (op A)).X.left) :
    GroupScheme.RelativeRoot.IsSplitUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A)) := by
  suffices key : ∀ (N : ℕ) (A : CommHopfAlgCat.{u} (CommRingCat.of k))
      (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜], IsGradedBialgebra 𝒜 →
      (∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
        a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) →
      ∀ G : GradedMatrixCoefficients 𝒜, (∀ i, G.M i i = 1) → (∀ i j, j < i → G.M i j = 0) →
      Smooth ((hopfSpec (CommRingCat.of k)).obj (op A)).X.hom →
      ConnectedSpace ((hopfSpec (CommRingCat.of k)).obj (op A)).X.left →
      Module.finrank k (epsDer k A) = N →
      GroupScheme.RelativeRoot.IsSplitUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A)) from
    key _ A 𝒜 h𝒜 h0 G hdiag hlow hSmooth hConn rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A 𝒜 _ h𝒜 h0 G hdiag hlow hSmooth hConn hN
  have hdom : IsDomain A := isDomain_of_hopfSpec A hSmooth hConn
  have hsm : Algebra.Smooth (CommRingCat.of k) A := (smooth_hopfSpec_iff A).1 hSmooth
  have : Algebra.FormallySmooth k A := inferInstanceAs (Algebra.FormallySmooth (CommRingCat.of k) A)
  have : Algebra.FiniteType k A := inferInstanceAs (Algebra.FiniteType (CommRingCat.of k) A)
  by_cases hA : ∃ a : A, a ∉ Set.range (algebraMap k A)
  swap
  · push Not at hA
    exact ⟨0, hasSplitSeries_zero_of_forall_mem_range A hA⟩
  obtain ⟨g, d, hd, hgd, hgp, ⟨s, hs⟩, hdrop⟩ := exists_splitDatum h𝒜 h0 G hdiag hlow hA
  have hgp' : Bialgebra.IsPrimitiveElem (CommRingCat.of k) g := hgp
  obtain ⟨hKs, hKc, -, hstep⟩ :=
    GroupScheme.HopfPrimitive.splitStep A hgp' s hs hSmooth hConn
  set J : Ideal A := Ideal.span {g} with hJ
  have hgJ : g ∈ J := Ideal.subset_span rfl
  have hJh : J.IsHomogeneous 𝒜 := Ideal.homogeneous_span 𝒜 {g} (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨d, hgd⟩)
  have : (J.restrictScalars k).IsCoideal :=
    (GroupScheme.HopfPrimitive.isHopfIdeal_span hgp').toIsCoideal
  let 𝒜' : ℤ → Submodule k (A ⧸ J) := quotGrade 𝒜 J (AddMonoidHom.id ℤ)
  let inst : GradedAlgebra 𝒜' :=
    quotGradedAlgebra hJh Function.injective_id fun i hi => absurd ⟨i, rfl⟩ hi
  have hB : IsGradedBialgebra 𝒜' := IsGradedBialgebra.quot h𝒜
  have hlt := hdrop J hgJ
  obtain ⟨n, hn⟩ := @ih _ (hN ▸ hlt) (GroupScheme.HopfPrimitive.quotient A hgp') 𝒜' inst hB
    (quot_h0 J h0) (G.quot J)
    (fun i => (congrArg (Ideal.Quotient.mk J) (hdiag i)).trans (map_one _))
    (fun i j h => (congrArg (Ideal.Quotient.mk J) (hlow i j h)).trans (map_zero _)) hKs hKc rfl
  exact ⟨n + 1, hstep n hn⟩

end Induction

end Langlands.Algebra.GradedHopf
