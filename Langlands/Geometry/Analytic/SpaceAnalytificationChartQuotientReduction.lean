import Langlands.Geometry.Analytic.SpaceChartQuotientAssembly
import Langlands.Geometry.Analytic.SpaceAnalytificationChartQuotientStatement
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedElementaryEtalePointStatement

/-! # Analytic quotients of étale chart families from elementary étale points

`ElemChart.ofPrime` chooses an elementary étale chart over the image of a prime of an
étale affine chart. These choices and the sheaf property of Hom presheaves on small
étale sites give the chart form of Conrad–Temkin, Theorem 4.2.2. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ChartQuotient

open SaturatedAtlasPresentation AffineAnalytification ExistenceReduction
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

/-- Choose an elementary étale chart at the image of `p`, with a prime above `p` and the
elementary prime in every finitely presented affine model of the overlap. -/
def ElemChart.ofPrime {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hElementary : SeparatedElementaryEtalePointStatement.{u}) (hX : IsSeparated X)
    {A : Type u} [CommRing A] [Algebra K A] (hA : Algebra.FiniteType K A)
    (x : RingPoints K X A) (hx : AlgebraicSpace.IsEtale (pointHom K x))
    (p : PrimeSpectrum A) :
    { E : ElemChart X // ∀ M : TestModel (pointHom K x) (pointHom K E.y),
      ∃ r : PrimeSpectrum M.C, PrimeSpectrum.comap M.f.toRingHom r = p ∧
        PrimeSpectrum.comap M.g.toRingHom r = E.q } := by
  apply Classical.choice
  obtain ⟨B, _, _, _, y, q, hy, hyx, hel⟩ := hElementary K X hX A hA x hx p
  let E : ElemChart X :=
    { B := CommAlgCat.of K B
      Q := FinitePolynomialPresentation.ofFiniteType K B
      y := y
      etale := hy
      q := q
      elem := hel }
  refine ⟨⟨E, fun M => ?_⟩⟩
  obtain ⟨r, hq, hp⟩ := hyx M.C M.g M.f M.isPullback.flip
  exact ⟨r, hp, hq⟩

/-- **Conrad–Temkin 4.2.2, chart form, from elementary étale points and the étale Hom
sheaf.** -/
theorem spaceAnalytificationChartQuotient_of
    (hElementary : SeparatedElementaryEtalePointStatement.{u})
    (hSheaf : EtaleHomSheafStatement.{u, u}) :
    SpaceAnalytificationChartQuotientStatement.{u} := by
  intro K _ _ _ X hX ι A _ _ P x hx
  let charts (j : CJ A) :=
    ElemChart.ofPrime hElementary hX
      (Algebra.FiniteType.of_surjective (P j.1).map (P j.1).surjective)
      (x j.1) (hx j.1) j.2
  let E : CJ A → ElemChart X := fun j => (charts j).val
  let O₁ : ∀ m : CM E, Set (Space K (E m.1).Q) := fun m =>
    Classical.choose (ElemChart.exists_trivial_open hX (E m.1) m.2.1 m.2.2)
  have hO₁ : ∀ m : CM E, IsOpen (O₁ m) ∧ m.2.1 ∈ O₁ m ∧
      ∀ (T : LocalizedCategory.{u, u, u} (K := K)) (α β : T ⟶ localized K (E m.1).Q),
        (∀ t, localizedSpaceFunctor.map α t ∈ O₁ m) →
        (∀ t, localizedSpaceFunctor.map β t ∈ O₁ m) →
        (pointModel hX (E m.1).Q (E m.1).Q (E m.1).y (E m.1).y).ARel (E m.1).Q (E m.1).Q α β →
          α = β := fun m =>
    Classical.choose_spec (ElemChart.exists_trivial_open hX (E m.1) m.2.1 m.2.2)
  let O : ∀ m : CM E, Set (Space K (E m.1).Q) := fun m =>
    O₁ m ∩ Set.range (baseMap K (E m.1).Q (Nj hX P x E m.1).R (Nj hX P x E m.1).g)
  have hO : ∀ m, IsOpen (O m) := by
    intro m
    refine (hO₁ m).1.inter ?_
    have h₁ := (etaleOpenMap K (localizedHom K (E m.1).Q (Nj hX P x E m.1).R
      (Nj hX P x E m.1).g) (etale_localizedHom _ _ _
        ((Nj hX P x E m.1).etale_g (hx m.1.1)))).isOpen_range
    rw [localizedSpaceFunctor_map_localizedHom] at h₁
    exact h₁
  have ha : ∀ j : CJ A, ∃ 𝔓 : PrimeSpectrum (Nj hX P x E j).C,
      PrimeSpectrum.comap ((Nj hX P x E j).f : A j.1 →+* (Nj hX P x E j).C) 𝔓 = j.2 ∧
        PrimeSpectrum.comap ((Nj hX P x E j).g : (E j).B →+* (Nj hX P x E j).C) 𝔓 =
          (E j).q :=
    fun j => (charts j).property (Nj hX P x E j)
  have hvO : ∀ m : CM E, m.2.1 ∈ O m := by
    intro m
    refine ⟨(hO₁ m).2.1, ?_⟩
    obtain ⟨𝔓, -, h𝔓⟩ := ha m.1
    obtain ⟨w, hw, -⟩ := exists_baseMap_eq_center K (E m.1).Q (Nj hX P x E m.1).R
      (Nj hX P x E m.1).g ((Nj hX P x E m.1).etale_g (hx m.1.1)) m.2.1 𝔓 (h𝔓.trans m.2.2.symm)
    exact ⟨w, hw⟩
  have htriv : ∀ (m : CM E) (T : LocalizedCategory.{u, u, u} (K := K))
      (α β : T ⟶ localized K (E m.1).Q),
      (∀ t, localizedSpaceFunctor.map α t ∈ O m) → (∀ t, localizedSpaceFunctor.map β t ∈ O m) →
      (Wm hX E (fun m : CM E => m.1) m m).ARel _ _ α β → α = β :=
    fun m T α β hα hβ h => (hO₁ m).2.2 T α β (fun t => (hα t).1) (fun t => (hβ t).1) h
  have hOr : ∀ m : CM E, O m ⊆
      Set.range (baseMap K (E m.1).Q (Nj hX P x E m.1).R (Nj hX P x E m.1).g) :=
    fun m => Set.inter_subset_right
  exact ⟨_, π hX hSheaf P x E O hO htriv hvO ha,
    etale_π hX hSheaf P x hx E O hO htriv hvO ha,
    π_surjective hX hSheaf P x E O hO htriv hvO ha hOr,
    fun i j B _ _ Q f g h => isPullback_π hX hSheaf P x E O hO htriv hvO ha Q f g h⟩

end Langlands.Analytic.SpaceAnalytification.ChartQuotient
