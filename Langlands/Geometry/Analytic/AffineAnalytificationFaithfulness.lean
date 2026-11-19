import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Faithfulness of affine analytification -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open _root_.CategoryTheory AffinoidAtlasPresentation AnalyticAffineSpace
open LocalizedFunctorialityComparison.OriginalStrongMaps SaturatedAtlasPresentation

private theorem exists_finite_quotient_not_mem
    (K : Type u) [Field K] {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] {a : A} (ha : a ≠ 0) :
    ∃ I : Ideal A, Module.Finite K (A ⧸ I) ∧ a ∉ I := by
  let J : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A A a)
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ J := h ▸ Submodule.mem_top
    exact ha (by simpa [J] using h1)
  obtain ⟨m, hm, hjm⟩ := Ideal.exists_le_maximal J hJ
  let : m.IsMaximal := hm
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hnot : ∃ n : ℕ, a ∉ m ^ n := by
    by_contra! h
    have hi : a ∈ (⨅ n : ℕ, m ^ n • ⊤ : Submodule A A) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
      exact h n
    obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff a).mp hi
    have hsub : 1 - (r : A) ∈ J := by
      change (1 - (r : A)) • a = 0
      rw [sub_smul, one_smul, hr, sub_self]
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ (by
      simpa only [sub_add_cancel] using m.add_mem (hjm hsub) r.property) isUnit_one)
  obtain ⟨n, hn⟩ := hnot
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  let hle : m ^ n ≤ m := Ideal.pow_le_self hn0
  let π : (A ⧸ m ^ n) →ₐ[K] A ⧸ m := Ideal.Quotient.factorₐ K hle
  refine ⟨m ^ n, ?_, hn⟩
  apply Module.finite_of_surjective_of_ker_le_nilradical π
    (Ideal.Quotient.factor_surjective hle) _ (IsNoetherian.noetherian _)
  intro b hb
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : b ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hb
  rw [mem_nilradical]
  exact ⟨n, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hb' n⟩

section CompleteField

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem operator_norm_add_le_max {E : Type v} [NormedAddCommGroup E]
    [NormedSpace K E] [IsUltrametricDist E] (f g : E →L[K] E) :
    ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (norm_nonneg f) (le_max_left _ _))
  intro x
  refine (IsUltrametricDist.norm_add_le_max (f x) (g x)).trans (max_le ?_ ?_)
  · exact (f.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  · exact (g.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))

private abbrev BasisCoordinates (R : Type v) [CommRing R] [Algebra K R] :=
  Fin (Module.finrank K R) → K

private def finiteRegularRepresentation (R : Type v) [CommRing R] [Algebra K R]
    [Module.Finite K R] :
    R →ₐ[K] (BasisCoordinates K R →L[K] BasisCoordinates K R) :=
  let e := (Module.finBasis K R).equivFun
  ((e.conjAlgEquiv K).trans (Module.End.toContinuousLinearMap (BasisCoordinates K R))).toAlgHom.comp
    (Algebra.lmul K R)

private theorem finiteRegularRepresentation_injective (R : Type v) [CommRing R] [Algebra K R]
    [Module.Finite K R] :
    Function.Injective (finiteRegularRepresentation K R) :=
  (Module.End.toContinuousLinearMap (BasisCoordinates K R)).injective.comp
    (((Module.finBasis K R).equivFun.conjAlgEquiv K).injective.comp Algebra.lmul_injective)

variable {A : Type v} [CommRing A] [Algebra K A]
  (P : FinitePolynomialPresentation K A)

omit [CompleteSpace K] in
/-- The product of the algebra maps to the polynomial-locus chart algebras. -/
def chartAlgebraProductMap : A →ₐ[K] (∀ m : ℕ, algebra K P m) :=
  AlgHom.pi (fun m => PolynomialLocus.algebraMap P (polyradius K P.arity m))

omit [CompleteSpace K] in
private theorem exists_chart_factorization {R : Type w}
    [NormedCommRing R] [NormedAlgebra K R] [CompleteSpace R] [IsUltrametricDist R]
    (hOne : ‖(1 : R)‖ ≤ 1) (φ : A →ₐ[K] R) :
    ∃ (m : ℕ) (φ' : BoundedAlgHom K (algebra K P m) R),
      φ'.toAlgHom.comp (PolynomialLocus.algebraMap P (polyradius K P.arity m)) = φ := by
  let b (i : Fin P.arity) := φ (P.map (MvPolynomial.X i))
  obtain ⟨m, hm⟩ := exists_radius_gt K (∑ i, ‖b i‖)
  have hb (i : Fin P.arity) : ‖b i‖ ≤ radius K m :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (b j)) (Finset.mem_univ i)).trans hm.le
  let r := polyradius K P.arity m
  have hb' : GeneralizedTateAlgebra.HasBoundedMonomials r R b :=
    ⟨1, one_pos, fun d => by
      rw [one_mul]
      exact GeneralizedTateAlgebra.monomialValue_norm_le_weight r R hOne b hb d⟩
  let ψ := GeneralizedTateAlgebra.evaluateHom r K R b hb'
  have hEval : ψ.toAlgHom.comp (GeneralizedTateAlgebra.polynomialMap r K) = φ.comp P.map := by
    apply MvPolynomial.algHom_ext
    intro i
    change ψ (MvPolynomial.aeval _ (MvPolynomial.X i)) = b i
    rw [MvPolynomial.aeval_X]
    exact GeneralizedTateAlgebra.evaluate_X r K R b i
  let φ' := PresentedAffinoidAlgebra.descendRelations K P.arity r (PolynomialLocus.relations P r)
    R ψ (by
      rintro _ ⟨p, hp, rfl⟩
      change (ψ.toAlgHom.comp (GeneralizedTateAlgebra.polynomialMap r K)) p = 0
      have hp' : P.map p = 0 := RingHom.mem_ker.mp hp
      rw [hEval, AlgHom.comp_apply, hp', map_zero])
  refine ⟨m, φ', ?_⟩
  ext a
  obtain ⟨p, rfl⟩ := P.surjective a
  change φ' (PolynomialLocus.algebraMap P r (P.map p)) = φ (P.map p)
  rw [PolynomialLocus.algebraMap_map]
  exact AlgHom.congr_fun hEval p

set_option backward.isDefEq.respectTransparency false in
private theorem eq_zero_of_chart_algebraMap_eq_zero {a : A}
    (h : ∀ m, PolynomialLocus.algebraMap P (polyradius K P.arity m) a = 0) : a = 0 := by
  by_contra ha
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  obtain ⟨I, hfin, haI⟩ := exists_finite_quotient_not_mem K ha
  let R := A ⧸ I
  let : Module.Finite K R := hfin
  let E := BasisCoordinates K R
  let ρ := finiteRegularRepresentation K R
  let : NormedCommRing R :=
    NormedCommRing.induced R (E →L[K] E) ρ (finiteRegularRepresentation_injective K R)
  let : NormedAlgebra K R := NormedAlgebra.induced K R (E →L[K] E) ρ
  let : CompleteSpace R := FiniteDimensional.complete K R
  let : IsUltrametricDist R :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      change ‖ρ (x + y)‖ ≤ max ‖ρ x‖ ‖ρ y‖
      rw [map_add]
      exact operator_norm_add_le_max K (ρ x) (ρ y)
  have hOne : ‖(1 : R)‖ ≤ 1 := by
    change ‖ρ 1‖ ≤ 1
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  obtain ⟨m, ψ, hψ⟩ := exists_chart_factorization K P hOne (Ideal.Quotient.mkₐ K I)
  have hq : (Ideal.Quotient.mk I) a = 0 := by
    change (Ideal.Quotient.mkₐ K I) a = 0
    rw [← hψ, AlgHom.comp_apply, h m, map_zero]
  exact haI (Ideal.Quotient.eq_zero_iff_mem.mp hq)

/-- The chart algebras jointly detect each element, including elements
supported on infinitesimal thickenings. -/
theorem chartAlgebraProductMap_injective : Function.Injective (chartAlgebraProductMap K P) := by
  intro a b h
  apply sub_eq_zero.mp
  apply eq_zero_of_chart_algebraMap_eq_zero K P
  intro m
  rw [map_sub, sub_eq_zero]
  exact congrFun h m

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)

set_option backward.isDefEq.respectTransparency false in
private theorem strongHom_injective :
    Function.Injective (fun f : A →ₐ[K] B =>
      (strongHom K P Q f : StrongHom (presentation K Q) (presentation K P))) := by
  intro f g h
  change strongHom K P Q f = strongHom K P Q g at h
  ext a
  apply chartAlgebraProductMap_injective K Q
  funext m
  let i : (presentation K Q).atlas.Index := representative K Q m
  let j := indexMap K P Q f i
  have hf := (atlasHom K P Q f).image_chart_subset i
  have hg : (strongHom K P Q g).baseMap ''
      Set.range ((presentation K Q).atlas.chart i) ⊆
      Set.range ((presentation K P).atlas.chart j) := by
    rw [← h]
    exact hf
  have hpb {F G : StrongHom (presentation K Q) (presentation K P)} (he : F = G)
      (hF : F.baseMap '' Set.range ((presentation K Q).atlas.chart i) ⊆
        Set.range ((presentation K P).atlas.chart j))
      (hG : G.baseMap '' Set.range ((presentation K Q).atlas.chart i) ⊆
        Set.range ((presentation K P).atlas.chart j)) :
      F.pullback i j hF = G.pullback i j hG := by
    cases he
    rfl
  have hc := (strongHom_pullback_algebraMap P Q f i j hf a).symm.trans
    ((congrArg (fun p : BoundedAlgHom K _ _ =>
      p (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a)) (hpb h hf hg)).trans
      (strongHom_pullback_algebraMap P Q g i j hg a))
  have hc' := congrArg (representativeEquiv K Q m) hc
  rw [representativeEquiv, equalRangeEquiv_algebraMap, equalRangeEquiv_algebraMap] at hc'
  exact hc'

set_option backward.isDefEq.respectTransparency false in
/-- Localized affine analytification is faithful on the algebra maps between
the polynomial presentations. -/
theorem localizedHom_injective :
    Function.Injective (localizedHom K P Q) := by
  intro f g h
  have hs : saturatedHom K P Q f = saturatedHom K P Q g :=
    localizationFunctor_map_injective h
  let F : CompatibleStrongHom (presentation K Q) (presentation K P) :=
    ⟨strongHom K P Q f,
      (strongHom K P Q f).hasLocallyCompatiblePullbacks_iff.mpr
        (strongHom_hasCoherentPullbacks K P Q f)⟩
  let G : CompatibleStrongHom (presentation K Q) (presentation K P) :=
    ⟨strongHom K P Q g,
      (strongHom K P Q g).hasLocallyCompatiblePullbacks_iff.mpr
        (strongHom_hasCoherentPullbacks K P Q g)⟩
  have hFG : F = G := CompatibleStrongHom.saturationExtension_injective hs
  exact strongHom_injective K P Q (congrArg CompatibleStrongHom.toStrongHom hFG)

/-- If the analytified map is an epimorphism, the original algebra map is injective. -/
theorem injective_of_epi_localizedHom (f : A →ₐ[K] B) [Epi (localizedHom K P Q f)] :
    Function.Injective f := by
  intro a b hab
  let R := MvPolynomial (Fin 1) K
  let T : FinitePolynomialPresentation K R := ⟨1, AlgHom.id K R, Function.surjective_id⟩
  let g : R →ₐ[K] A := MvPolynomial.aeval (fun _ => a)
  let h : R →ₐ[K] A := MvPolynomial.aeval (fun _ => b)
  have heq : f.comp g = f.comp h := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [g, h] using hab
  have hc : localizedHom K T P g = localizedHom K T P h := by
    apply (cancel_epi (localizedHom K P Q f)).mp
    rw [← (affineAnalytificationLocalizedFunctoriality K R A B T T P Q g f).2.2.2.1,
      ← (affineAnalytificationLocalizedFunctoriality K R A B T T P Q h f).2.2.2.1, heq]
  let t : Fin 1 := 0
  have hh := AlgHom.congr_fun (localizedHom_injective K T P hc) (MvPolynomial.X t)
  exact (MvPolynomial.aeval_X (fun _ : Fin 1 => a) t).symm.trans
    (hh.trans (MvPolynomial.aeval_X (fun _ : Fin 1 => b) t))

end CompleteField

end Langlands.Analytic.AffineAnalytification
