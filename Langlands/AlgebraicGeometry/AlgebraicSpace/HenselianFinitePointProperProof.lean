import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFinitePointProperStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyAdmissibleProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianFinitePointProper

/-!
# Finite maps of algebraic spaces are proper on rational points

Conrad's Corollary 5.12 (printed p.20): over a henselian valued field `K` that is
algebraically closed in its completion, a finite map `f : X → Y` between separated algebraic
spaces locally of finite type induces a proper map `X(K) → Y(K)` for the étale-chart
topologies.

The proof uses the ultrafilter criterion. If `f(x)` converges to `y` along an ultrafilter,
choose an affine étale chart `b : V → Y` through `y`; its point map is a local homeomorphism
near the chosen point. The base change `X ×_Y V → V` is a finite morphism of affine schemes,
which is proper on rational points (`HenselianFinitePointProper`). Lifting the ultrafilter
through the fibre product gives a limit point in `X(K)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest schemePointTopology schemePointTopology_eq_affine IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace HenselianFinitePointProperProof

/-- A separated algebraic space is quasi-separated. -/
theorem isQuasiSeparated_of_isSeparated {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : IsSeparated X) : IsQuasiSeparated X := by
  refine MorphismProperty.relative_monotone ?_ _ hX
  intro A B f hf
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((Over.forget S).map f) := hf
  exact (inferInstance : QuasiCompact ((Over.forget S).map f))

end HenselianFinitePointProperProof

open HenselianFinitePointProperProof in
/-- **Conrad's Corollary 5.12.** Over a henselian valued field algebraically closed in its
completion, a finite map of separated algebraic spaces locally of finite type is proper on
rational points. -/
theorem henselianFinitePointProper : HenselianFinitePointProperStatement.{u} := by
  intro K _ hK hcl X Y f hXs hXlft hYs hYlft hf
  have hX : IsQuasiSeparatedLocallyFiniteType K X := ⟨isQuasiSeparated_of_isSeparated hXs, hXlft⟩
  have hY : IsLocallySeparatedLocallyFiniteType K Y :=
    ⟨⟨isQuasiSeparated_of_isSeparated hYs, hYlft⟩, isLocallySeparated_of_isSeparated hYs⟩
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints K Y K) := etaleChartTopology K Y
  have : T2Space (RingPoints K Y K) := t2Space_etaleChartTopology hK hY.1 hYs
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨continuous_ringPointsMap hK hY.1 f, fun 𝒰 y h𝒰 => ?_⟩
  -- an affine étale chart through `y`, a local homeomorphism on points
  obtain ⟨V, b, hV, hb, v, hv⟩ :=
    RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement K Y hY.1.1 y
  have : LocallyOfFiniteType V.hom := locallyOfFiniteType_of_isEtale hYlft (hom b) hb
  have hVsp := isLocallySeparatedLocallyFiniteType_schemeToSpace V
  have hbe : IsEtaleMorphism b := fun _ _ hφ => IsEtale.comp hφ hb
  let : TopologicalSpace (RingPoints K ((schemeToSpace _).obj V) K) :=
    etaleChartTopology K ((schemeToSpace _).obj V)
  let : TopologicalSpace (RingPoint K V K) := schemePointTopology K V K
  have hloc := isLocalHomeomorph_ringPointsMap hK hVsp.1 hY b hbe
  let v' : RingPoints K ((schemeToSpace _).obj V) K := (schemeRingPointsEquiv K V K).symm v
  obtain ⟨e, hve, he⟩ := hloc v'
  have hey : e v' = y := by rw [← he]; exact hv
  have hyt : y ∈ e.target := hey ▸ e.map_source hve
  have hWmem : RingPoints.map f ⁻¹' e.target ∈ 𝒰 := h𝒰 (e.open_target.mem_nhds hyt)
  -- the base change of `f` along the chart
  let hr := hf.rep
  let P := hr.pullback (hom b)
  let g : P ⟶ V := hr.snd (hom b)
  let q : (schemeYoneda _).obj P ⟶ X.presheaf := hr.fst (hom b)
  have hsq : IsPullback q ((schemeYoneda _).map g) (hom f) (hom b) := hr.isPullback (hom b)
  have : _root_.AlgebraicGeometry.IsFinite g.left := hf.property_snd (hom b)
  have : IsAffine P.left := isAffine_of_isAffineHom g.left
  have : LocallyOfFiniteType P.hom := by
    rw [← Over.w g]
    infer_instance
  let : TopologicalSpace (RingPoint K P K) := schemePointTopology K P K
  -- lifts of the points over the chart
  have hlift : ∀ x : RingPoints K X K, RingPoints.map f x ∈ e.target →
      ∃ w : RingPoint K P K, schemePointsMap q w = x ∧
        (w ≫ g : RingPoint K V K) = (e.symm (RingPoints.map f x)).down := by
    intro x hx
    obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback hsq (ringTest K K) x
      (e.symm (RingPoints.map f x)) (by
        change RingPoints.map f x = RingPoints.map b (e.symm (RingPoints.map f x))
        rw [he]
        exact (e.right_inv hx).symm)
    exact ⟨p.down, hp₁, congrArg ULift.down hp₂⟩
  obtain ⟨x₁, hx₁⟩ := 𝒰.nonempty_of_mem hWmem
  have : Nonempty (RingPoint K P K) := ⟨(hlift x₁ hx₁).choose⟩
  choose! σ hσ₁ hσ₂ using hlift
  -- along the ultrafilter the lifts project to `v`
  have hsymm : @Tendsto (RingPoints K X K) (RingPoint K V K)
      (fun x => schemeRingPointsEquiv K V K (e.symm (RingPoints.map f x))) 𝒰 (𝓝 v) := by
    have h₁ : @Tendsto (RingPoints K X K) (RingPoints K ((schemeToSpace _).obj V) K)
        (fun x => e.symm (RingPoints.map f x)) 𝒰 (𝓝 v') := by
      have := (e.continuousAt_symm hyt).tendsto.comp h𝒰
      rwa [← hey, e.left_inv hve] at this
    have h₂ := (isHomeomorph_schemeRingPointsEquiv hK V hVsp.1).continuous.tendsto v'
    have h₃ := h₂.comp h₁
    rw [show schemeRingPointsEquiv K V K v' = v from Equiv.apply_symm_apply _ _] at h₃
    exact h₃
  have hgσ : @Tendsto (RingPoints K X K) (RingPoint K V K) (fun x => σ x ≫ g) 𝒰 (𝓝 v) :=
    hsymm.congr' (Filter.mem_of_superset hWmem fun x hx => (hσ₂ x hx).symm)
  -- the base change is proper on points
  have hgp : @IsProperMap (RingPoint K P K) (RingPoint K V K) (schemePointTopology K P K)
      (schemePointTopology K V K) (fun p => p ≫ g) := by
    have h := PointTopology.HenselianFinitePointProper.isProperMap_affineFinitePointMap hK hcl g
    rw [schemePointTopology_eq_affine, schemePointTopology_eq_affine]
    exact h
  obtain ⟨w₀, -, hw₀⟩ := hgp.ultrafilter_le_nhds_of_tendsto
    (𝒰 := Ultrafilter.map σ 𝒰) (y := v) hgσ
  -- the limit point
  have hq : Continuous (schemePointsMap q) :=
    continuous_schemePointsMap hK hX.exists_chart q
  refine ⟨schemePointsMap q w₀, ?_⟩
  have h₁ : Tendsto (fun x => schemePointsMap q (σ x)) 𝒰 (𝓝 (schemePointsMap q w₀)) :=
    (hq.tendsto w₀).comp hw₀
  have h₂ : Tendsto id (𝒰 : Filter (RingPoints K X K)) (𝓝 (schemePointsMap q w₀)) :=
    h₁.congr' (Filter.mem_of_superset hWmem fun x hx => hσ₁ x hx)
  exact h₂

end Langlands.AlgebraicGeometry.AlgebraicSpace
