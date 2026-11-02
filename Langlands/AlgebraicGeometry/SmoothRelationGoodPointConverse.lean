import Langlands.AlgebraicGeometry.SmoothRelationGoodPointChart
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointFiniteGeneration
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointSimpleRoots

/-! # Good points from cotangent spanning in an affine chart -/

noncomputable section

universe u v

open CategoryTheory IsLocalRing TensorProduct

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

open _root_.AlgebraicGeometry

variable {U R : Scheme.{u}} {t s : R ⟶ U} {e : U ⟶ R}

/-- The local ring of an affine chart at an identity point is rational over the base chart. -/
lemma isRationalPoint_localizationAtPrime (hs : e ≫ s = 𝟙 U) (x : U)
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hpW : e x ∈ W) (hWs : W ≤ s ⁻¹ᵁ V) [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime]
    (hq : (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal = q) :
    IsRationalPoint Γ(U, V) (Localization.AtPrime q) := by
  subst hq
  have hxV : x ∈ V := mem_of_comp_eq_id e hs hWs hpW
  let := R.presheaf.algebra_section_stalk ⟨e x, hpW⟩
  have := hW.isLocalization_stalk ⟨e x, hpW⟩
  let φ := IsLocalization.algEquiv (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal.primeCompl
    (Localization.AtPrime (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal) (R.presheaf.stalk (e x))
  let : Algebra Γ(U, V) (R.presheaf.stalk (e x)) := (chartMap s hWs (e x) hpW).toAlgebra
  apply isRationalPoint_of_ringEquiv φ.toRingEquiv
  · intro a
    change φ _ = _
    rw [IsScalarTower.algebraMap_apply Γ(U, V) Γ(R, W), AlgEquiv.commutes, hσ]
    rfl
  · exact isRationalPoint_chartMap e hs x hV hWs hpW hxV

/-- Cotangent spanning at an identity point implies goodness for a locally finite type source. -/
theorem isGoodPoint_of_cotangentSpan_eq_top [LocallyOfFiniteType s]
    (ht : e ≫ t = 𝟙 U) (hs : e ≫ s = 𝟙 U) (x : U)
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hpW : e x ∈ W) (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime]
    (hq : (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal = q)
    (hspan : cotangentSpan
      ((algebraMap Γ(R, W) (Localization.AtPrime q)).comp (t.appLE V W hWt).hom) = ⊤) :
    IsGoodPoint t s e x := by
  have hft : Algebra.FiniteType Γ(U, V) Γ(R, W) := by
    rw [← RingHom.finiteType_algebraMap, hσ]
    exact s.finiteType_appLE hV hW hWs
  let θ := (algebraMap Γ(R, W) (Localization.AtPrime q)).comp (t.appLE V W hWt).hom
  have hqm : (maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap Γ(R, W) (Localization.AtPrime q)) = q :=
    Localization.AtPrime.under_maximalIdeal
  have hcomap :
      (maximalIdeal (Localization.AtPrime q)).comap θ =
        (maximalIdeal (Localization.AtPrime q)).comap
          (algebraMap Γ(U, V) (Localization.AtPrime q)) := by
    dsimp only [θ]
    rw [← Ideal.comap_comap,
      IsScalarTower.algebraMap_eq Γ(U, V) Γ(R, W), ← Ideal.comap_comap,
      hqm, hσ, ← hq]
    exact comap_appLE_eq_comap_appLE ht hs x hW hpW hWs hWt
  have heq := maximalIdeal_eq_of_cotangentSpan_eq_top_of_essFiniteType θ hcomap
    (isRationalPoint_localizationAtPrime hs x hV hW hpW hWs hσ q hq) hspan
  subst hq
  have hxV : x ∈ V := mem_of_comp_eq_id e hs hWs hpW
  let := R.presheaf.algebra_section_stalk ⟨e x, hpW⟩
  have := hW.isLocalization_stalk ⟨e x, hpW⟩
  let φ := IsLocalization.algEquiv (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal.primeCompl
    (Localization.AtPrime (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal) (R.presheaf.stalk (e x))
  let : Algebra Γ(U, V) (R.presheaf.stalk (e x)) := (chartMap s hWs (e x) hpW).toAlgebra
  have hφ : ∀ a, φ.toRingEquiv
      (algebraMap Γ(U, V) (Localization.AtPrime (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal) a) =
      algebraMap Γ(U, V) (R.presheaf.stalk (e x)) a := by
    intro a
    change φ _ = _
    rw [IsScalarTower.algebraMap_apply Γ(U, V) Γ(R, W), AlgEquiv.commutes, hσ]
    rfl
  have hφsymm : ∀ a, φ.toRingEquiv.symm (algebraMap Γ(U, V) (R.presheaf.stalk (e x)) a) =
      algebraMap Γ(U, V) (Localization.AtPrime (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal) a := by
    intro a
    apply φ.toRingEquiv.injective
    rw [RingEquiv.apply_symm_apply, hφ]
  have hθ : (φ.toRingEquiv.symm : _ →+*
        Localization.AtPrime (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal).comp
      (chartMap t hWt (e x) hpW) = θ := by
    ext a
    apply φ.toRingEquiv.injective
    change φ (φ.symm _) = φ (algebraMap Γ(R, W) _ ((t.appLE V W hWt).hom a))
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    rfl
  have heq' := maximalIdeal_eq_of_ringEquiv φ.toRingEquiv.symm hφsymm
    (chartMap t hWt (e x) hpW) (by rw [hθ]; exact heq)
  apply (isGoodPoint_iff_chartMap t s e x hV hpW hWs hWt).mpr
  rw [comap_maximalIdeal_chartMap_of_comp_eq_id e ht x hWt hpW hxV,
    ← comap_maximalIdeal_chartMap_of_comp_eq_id e hs x hWs hpW hxV]
  exact heq'

/-- The image-indexed residue span used by differential slicing also implies goodness. -/
theorem isGoodPoint_of_residueSpan_eq_top [LocallyOfFiniteType s]
    (ht : e ≫ t = 𝟙 U) (hs : e ≫ s = 𝟙 U) (x : U)
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hpW : e x ∈ W) (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime]
    (hq : (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal = q)
    (hspan : Submodule.span (ResidueField (Localization.AtPrime q))
      (Set.range (fun y : (t.appLE V W hWt).hom ''
          (q.comap (algebraMap Γ(U, V) Γ(R, W)) : Set Γ(U, V)) ↦
        (1 : ResidueField (Localization.AtPrime q)) ⊗ₜ[Localization.AtPrime q]
          KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q)
            (algebraMap Γ(R, W) (Localization.AtPrime q) y))) = ⊤) :
    IsGoodPoint t s e x := by
  apply isGoodPoint_of_cotangentSpan_eq_top ht hs x hV hW hpW hWs hWt hσ q hq
  have hp : (maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap Γ(U, V) (Localization.AtPrime q)) =
      q.comap (algebraMap Γ(U, V) Γ(R, W)) := by
    rw [IsScalarTower.algebraMap_eq Γ(U, V) Γ(R, W), ← Ideal.comap_comap]
    congr 1
    exact Localization.AtPrime.under_maximalIdeal
  rw [cotangentSpan, hp, ← hspan]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨(t.appLE V W hWt).hom g, g, hg, rfl⟩, rfl⟩
  · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- The intrinsic good-point condition is equivalent to the chart residue-span condition. -/
theorem isGoodPoint_iff_residueSpan_eq_top [LocallyOfFiniteType s]
    (ht : e ≫ t = 𝟙 U) (hs : e ≫ s = 𝟙 U) (x : U)
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hpW : e x ∈ W) (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime]
    (hq : (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal = q) :
    IsGoodPoint t s e x ↔
      Submodule.span (ResidueField (Localization.AtPrime q))
        (Set.range (fun y : (t.appLE V W hWt).hom ''
            (q.comap (algebraMap Γ(U, V) Γ(R, W)) : Set Γ(U, V)) ↦
          (1 : ResidueField (Localization.AtPrime q)) ⊗ₜ[Localization.AtPrime q]
            KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q)
              (algebraMap Γ(R, W) (Localization.AtPrime q) y))) = ⊤ :=
  ⟨residueSpan_eq_top_of_isGoodPoint ht hs x hV hW hpW hWs hWt hσ q hq,
    isGoodPoint_of_residueSpan_eq_top ht hs x hV hW hpW hWs hWt hσ q hq⟩

/-- Simple integer equations for spanning coordinates certify that the point is good. -/
theorem isGoodPoint_of_simpleIntegerRoots [LocallyOfFiniteType s]
    (ht : e ≫ t = 𝟙 U) (hs : e ≫ s = 𝟙 U) (x : U)
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hpW : e x ∈ W) (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime]
    (hq : (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal = q)
    {ι : Type v} (g : ι → Γ(U, V))
    (hspan : Submodule.span (ResidueField (Localization.AtPrime q)) (Set.range fun i ↦
      (1 : ResidueField (Localization.AtPrime q)) ⊗ₜ[Localization.AtPrime q]
        KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q)
          (algebraMap Γ(R, W) (Localization.AtPrime q) ((t.appLE V W hWt).hom (g i)))) = ⊤)
    (hsimple : ∀ i, ∃ P : Polynomial ℤ,
      Polynomial.aeval (g i) P ∈ q.comap (t.appLE V W hWt).hom ∧
      Polynomial.aeval (g i) P.derivative ∉ q.comap (t.appLE V W hWt).hom) :
    IsGoodPoint t s e x := by
  apply isGoodPoint_of_cotangentSpan_eq_top ht hs x hV hW hpW hWs hWt hσ q hq
  let θ := (algebraMap Γ(R, W) (Localization.AtPrime q)).comp (t.appLE V W hWt).hom
  have hqm : (maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap Γ(R, W) (Localization.AtPrime q)) = q :=
    Localization.AtPrime.under_maximalIdeal
  refine cotangentSpan_eq_top_of_simpleIntegerRoots θ g ?_ hspan ?_
  · dsimp only [θ]
    rw [← Ideal.comap_comap,
      IsScalarTower.algebraMap_eq Γ(U, V) Γ(R, W), ← Ideal.comap_comap,
      hqm, hσ, ← hq]
    exact comap_appLE_eq_comap_appLE ht hs x hW hpW hWs hWt
  · intro i
    obtain ⟨P, hP, hdP⟩ := hsimple i
    refine ⟨P, ?_, ?_⟩
    · change (t.appLE V W hWt).hom (Polynomial.aeval (g i) P) ∈
        (maximalIdeal (Localization.AtPrime q)).comap
          (algebraMap Γ(R, W) (Localization.AtPrime q))
      rwa [hqm]
    · change (t.appLE V W hWt).hom (Polynomial.aeval (g i) P.derivative) ∉
        (maximalIdeal (Localization.AtPrime q)).comap
          (algebraMap Γ(R, W) (Localization.AtPrime q))
      rwa [hqm]

/-- Actual simple integer equations for chart coordinates, together with intrinsic goodness. -/
structure SimpleIntegerGoodPointData (t s : R ⟶ U) (e : U ⟶ R) (x : U)
    {V : U.Opens} {W : R.Opens} (hWt : W ≤ t ⁻¹ᵁ V)
    (q : Ideal Γ(R, W)) {ι : Type v} (g : ι → Γ(U, V)) where
  polynomial : ι → Polynomial ℤ
  equation_mem : ∀ i, Polynomial.aeval (g i) (polynomial i) ∈
    q.comap (t.appLE V W hWt).hom
  derivative_not_mem : ∀ i, Polynomial.aeval (g i) (polynomial i).derivative ∉
    q.comap (t.appLE V W hWt).hom
  isGoodPoint : IsGoodPoint t s e x

/-- Choose simple integer equations and prove goodness from their spanning coordinates. -/
def simpleIntegerGoodPointData [LocallyOfFiniteType s]
    (ht : e ≫ t = 𝟙 U) (hs : e ≫ s = 𝟙 U) (x : U)
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hpW : e x ∈ W) (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime]
    (hq : (hW.primeIdealOf ⟨e x, hpW⟩).asIdeal = q)
    {ι : Type v} (g : ι → Γ(U, V))
    (hspan : Submodule.span (ResidueField (Localization.AtPrime q)) (Set.range fun i ↦
      (1 : ResidueField (Localization.AtPrime q)) ⊗ₜ[Localization.AtPrime q]
        KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q)
          (algebraMap Γ(R, W) (Localization.AtPrime q) ((t.appLE V W hWt).hom (g i)))) = ⊤)
    (hsimple : ∀ i, ∃ P : Polynomial ℤ,
      Polynomial.aeval (g i) P ∈ q.comap (t.appLE V W hWt).hom ∧
      Polynomial.aeval (g i) P.derivative ∉ q.comap (t.appLE V W hWt).hom) :
    SimpleIntegerGoodPointData t s e x hWt q g := by
  classical
  have hgood :=
    isGoodPoint_of_simpleIntegerRoots ht hs x hV hW hpW hWs hWt hσ q hq g hspan hsimple
  choose P hP hdP using hsimple
  exact ⟨P, hP, hdP, hgood⟩

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
