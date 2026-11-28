import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedElementaryEtalePointStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformFieldPointChartsProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FieldPoints
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof
import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleThresholdInvariance

/-!
# Elementary étale points of separated algebraic spaces: proof

This file proves `SeparatedElementaryEtalePointStatement`, a ring-point form of Stacks Project,
Decent Algebraic Spaces, Lemma 68.11.4 (Tag 0BBP), for separated algebraic spaces over a field.

Let `x : Spec A → X` be the given étale point and `E` the étale equivalence relation
`R = Spec A ×_X Spec A ⇉ Spec A`; `R` is affine because `X` is separated. Following the proof
of Stacks Lemma 68.8.3 (Tag 0BBN), the prime `p` lies in a unique difference of consecutive
tuple threshold opens of `E`, say at index `n`: it is related to the first coordinate of a
distinct related `(n + 1)`-tuple, but not to that of any distinct related `(n + 2)`-tuple. The
chart is the affine quotient `V_n` of the distinct related `(n + 1)`-tuples by the symmetric
group, with its étale map to `X` induced by the first coordinate, written as `Spec B` with
`B` its ring of global sections; `B` is of finite type over `K` by descent of local finite type
along the finite étale surjective quotient map. The point `q` is the image of that tuple. The
two conditions are checked on points with values in algebraically closed fields.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap ringTestMap_comp
  ringTestMap_id AffineCoordinateRing affineSchemeOverIso affineCoordinate_finiteType_iff)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SeparatedElementaryEtalePoint

open UniformFieldPointCharts

set_option backward.isDefEq.respectTransparency false

/-- Every point of a scheme is the image of a point with values in an algebraically closed
field. -/
theorem exists_algClosed_point (Z : Scheme.{u}) (z : Z) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (ζ : Spec (CommRingCat.of Ω) ⟶ Z),
      ∀ w, ζ w = z := by
  let κ := Z.residueField z
  refine ⟨AlgebraicClosure κ, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ))) ≫
      Z.fromSpecResidueField z, fun w => ?_⟩
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

variable {S : Scheme.{u}}

/-- Lifting a pair of points with equal images through a represented pullback square. -/
theorem exists_lift_of_isPullback {P V₁ V₂ : Over S} {F : Presheaf S}
    {f₁ : P ⟶ V₁} {f₂ : P ⟶ V₂} {a₁ : (schemeYoneda S).obj V₁ ⟶ F}
    {a₂ : (schemeYoneda S).obj V₂ ⟶ F}
    (h : IsPullback ((schemeYoneda S).map f₁) ((schemeYoneda S).map f₂) a₁ a₂)
    {T : Over S} (x₁ : T ⟶ V₁) (x₂ : T ⟶ V₂)
    (w : (schemeYoneda S).map x₁ ≫ a₁ = (schemeYoneda S).map x₂ ≫ a₂) :
    ∃ ξ : T ⟶ P, ξ ≫ f₁ = x₁ ∧ ξ ≫ f₂ = x₂ := by
  obtain ⟨ξ, hξ⟩ := (schemeYoneda S).map_surjective (h.lift _ _ w)
  refine ⟨ξ, (schemeYoneda S).map_injective ?_, (schemeYoneda S).map_injective ?_⟩
  · rw [Functor.map_comp, hξ, h.lift_fst]
  · rw [Functor.map_comp, hξ, h.lift_snd]

/-- Points of a represented pullback are determined by their two projections. -/
theorem hom_ext_of_isPullback {P V₁ V₂ : Over S} {F : Presheaf S}
    {f₁ : P ⟶ V₁} {f₂ : P ⟶ V₂} {a₁ : (schemeYoneda S).obj V₁ ⟶ F}
    {a₂ : (schemeYoneda S).obj V₂ ⟶ F}
    (h : IsPullback ((schemeYoneda S).map f₁) ((schemeYoneda S).map f₂) a₁ a₂)
    {T : Over S} {ξ ξ' : T ⟶ P} (e₁ : ξ ≫ f₁ = ξ' ≫ f₁) (e₂ : ξ ≫ f₂ = ξ' ≫ f₂) :
    ξ = ξ' := by
  apply (schemeYoneda S).map_injective
  apply h.hom_ext
  · rw [← Functor.map_comp, ← Functor.map_comp, e₁]
  · rw [← Functor.map_comp, ← Functor.map_comp, e₂]

section Tuples

variable {K : Type u} [Field K] {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {U R : Over (Spec (CommRingCat.of K))} {t s : R ⟶ U}
  {a : (schemeYoneda _).obj U ⟶ X.presheaf}
  (h : IsPullback ((schemeYoneda _).map t) ((schemeYoneda _).map s) a a)
  (ht : Etale t.left) (hs : Etale s.left) [IsAffine R.left] [IsAffine U.left]

/-- Two points of `V_n` with values in an algebraically closed field, the first outside the
symmetric threshold open of `n + 2` coordinates, with the same image in `X` are equal. -/
theorem eq_of_comp_chart_eq (n : ℕ)
    (tM : (schemeYoneda _).obj (quot h ht hs n) ⟶ X.presheaf)
    (hcomp : (schemeYoneda _).map (quotMap h ht hs n) ≫ tM =
      (schemeYoneda _).map (projOver h ht hs n 0) ≫ a)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {σ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K)}
    (α β : Over.mk σ ⟶ quot h ht hs n)
    (hα : ∀ w, α.left w ∉ (rel h ht hs).tupleSymmetricThresholdOpen n (n + 1))
    (hαβ : (schemeYoneda _).map α ≫ tM = (schemeYoneda _).map β ≫ tM) : α = β := by
  let E := rel h ht hs
  obtain ⟨a₀, ha₀⟩ := LangWeil.SpaceFamily.exists_lift_of_surjective (E.tupleSymmetricMap n)
    α.left
  obtain ⟨b₀, hb₀⟩ := LangWeil.SpaceFamily.exists_lift_of_surjective (E.tupleSymmetricMap n)
    β.left
  have hq : (quotMap h ht hs n).left ≫ (quot h ht hs n).hom = (tupleOver h ht hs n).hom :=
    Over.w (quotMap h ht hs n)
  let aO : Over.mk σ ⟶ tupleOver h ht hs n := Over.homMk a₀ (by
    rw [← hq, ← Category.assoc]
    change (a₀ ≫ E.tupleSymmetricMap n) ≫ _ = σ
    rw [ha₀]
    exact Over.w α)
  let bO : Over.mk σ ⟶ tupleOver h ht hs n := Over.homMk b₀ (by
    rw [← hq, ← Category.assoc]
    change (b₀ ≫ E.tupleSymmetricMap n) ≫ _ = σ
    rw [hb₀]
    exact Over.w β)
  have haO : aO ≫ quotMap h ht hs n = α := Over.OverMorphism.ext ha₀
  have hbO : bO ≫ quotMap h ht hs n = β := Over.OverMorphism.ext hb₀
  obtain ⟨r, hrt, hrs⟩ := EtaleEquivalenceRelation.exists_lift_of_isPullback h
    (aO ≫ projOver h ht hs n 0) (bO ≫ projOver h ht hs n 0) (by
      rw [Functor.map_comp_assoc, Functor.map_comp_assoc, ← hcomp,
        ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, haO, hbO, hαβ])
  let f := E.tupleCrossLift n n a₀ b₀ r.left (congrArg CommaMorphism.left hrt)
    (congrArg CommaMorphism.left hrs)
  have hx : (f ≫ E.tupleCrossLeft n n ≫ E.tupleDistinctProjection n 0) default ∉
      E.tupleThresholdOpen (n + 1) := by
    rw [E.tupleCrossLift_left_assoc]
    intro hmem
    apply hα (default : Spec (CommRingCat.of Ω))
    rw [← ha₀, Scheme.Hom.comp_apply]
    exact (E.tupleSymmetricMap_mem_threshold_iff n (n + 1) _).mpr hmem
  have key := E.tupleCross_fieldPoint_symmetric_eq_of_not_threshold n Ω f hx
  rw [E.tupleCrossLift_left_assoc, E.tupleCrossLift_right_assoc] at key
  exact Over.OverMorphism.ext (ha₀.symm.trans (key.trans hb₀))

/-- Let `w'` be a distinct related tuple whose first coordinate is `s r` for a point `r` of the
relation scheme. In every represented fibre product `D` of `V_n ≅ W` and the chart `U` over `X`,
some point of `D` lies over the image of `w'` in `W` and over `t r` in `U`. -/
theorem exists_point_of_isPullback (n : ℕ)
    (tM : (schemeYoneda _).obj (quot h ht hs n) ⟶ X.presheaf)
    (hcomp : (schemeYoneda _).map (quotMap h ht hs n) ≫ tM =
      (schemeYoneda _).map (projOver h ht hs n 0) ≫ a)
    {W Dv : Over (Spec (CommRingCat.of K))} (e : quot h ht hs n ≅ W) (φ₁ : Dv ⟶ W)
    (φ₂ : Dv ⟶ U)
    (hpb : IsPullback ((schemeYoneda _).map φ₁) ((schemeYoneda _).map φ₂)
      ((schemeYoneda _).map e.inv ≫ tM) a)
    (w' : (rel h ht hs).tupleDistinctScheme n) (r : R.left)
    (hr : s.left r = (rel h ht hs).tupleDistinctProjection n 0 w') :
    ∃ P : Dv.left, φ₁.left P = e.hom.left ((rel h ht hs).tupleSymmetricMap n w') ∧
      φ₂.left P = t.left r := by
  let E := rel h ht hs
  obtain ⟨Ω, _, _, ρ₀, hρ₀⟩ := exists_algClosed_point R.left r
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (ρ₀ ≫ R.hom)
  let ρ : T ⟶ R := Over.homMk ρ₀ rfl
  have : LocallyQuasiFinite (E.tupleDistinctProjection n 0) :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  obtain ⟨ω, hω, hωpt⟩ := LangWeil.SpaceFamily.exists_lift_at_point
    (E.tupleDistinctProjection n 0) (ρ₀ ≫ s.left) w'
      (hr.symm.trans (congrArg s.left (hρ₀ (IsLocalRing.closedPoint Ω))).symm)
  let ωO : T ⟶ tupleOver h ht hs n := Over.homMk ω (by
    change ω ≫ E.tupleDistinctProjection n 0 ≫ U.hom = ρ₀ ≫ R.hom
    rw [← Category.assoc, hω, Category.assoc, Over.w s])
  have hωs : ωO ≫ projOver h ht hs n 0 = ρ ≫ s := Over.OverMorphism.ext hω
  obtain ⟨ξ, hξ₁, hξ₂⟩ := exists_lift_of_isPullback hpb (ωO ≫ quotMap h ht hs n ≫ e.hom)
    (ρ ≫ t) (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        ← Functor.map_comp_assoc (schemeYoneda _) e.hom, e.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, hcomp, ← Functor.map_comp_assoc, hωs,
        Functor.map_comp_assoc, ← h.w, Functor.map_comp_assoc])
  refine ⟨ξ.left (IsLocalRing.closedPoint Ω), ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hξ₁]
    change e.hom.left ((quotMap h ht hs n).left (ω _)) = _
    rw [hωpt]
    rfl
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hξ₂]
    change t.left (ρ₀ _) = _
    rw [hρ₀]

/-- Let `V_n ≅ Spec B` and let `q` be a point of `Spec B` whose image in `V_n` lies outside the
symmetric threshold open of `n + 2` coordinates. In every represented fibre product `Spec C` of
`Spec B` with itself over `X`, with projections given by `f g : B → C` and a diagonal
`μ : C → B`, a prime of `C` contracting to `q` along `f` is `μ⁻¹(q)`. -/
theorem eq_comap_of_isPullback (n : ℕ)
    (tM : (schemeYoneda _).obj (quot h ht hs n) ⟶ X.presheaf)
    (hcomp : (schemeYoneda _).map (quotMap h ht hs n) ≫ tM =
      (schemeYoneda _).map (projOver h ht hs n 0) ≫ a)
    {B : Type u} [CommRing B] [Algebra K B] (e : quot h ht hs n ≅ ringTest K B)
    (q : PrimeSpectrum B)
    (hq : e.inv.left q ∉ (rel h ht hs).tupleSymmetricThresholdOpen n (n + 1))
    (C : Type u) [CommRing C] [Algebra K C] (f g : B →ₐ[K] C)
    (hpb : IsPullback ((schemeYoneda _).map (ringTestMap K f))
      ((schemeYoneda _).map (ringTestMap K g))
      ((schemeYoneda _).map e.inv ≫ tM) ((schemeYoneda _).map e.inv ≫ tM))
    (μ : C →ₐ[K] B) (hf : μ.comp f = AlgHom.id K B) (hg : μ.comp g = AlgHom.id K B)
    (P : PrimeSpectrum C) (hPf : PrimeSpectrum.comap (f : B →+* C) P = q) :
    P = PrimeSpectrum.comap (μ : C →+* B) q := by
  obtain ⟨Ω, _, _, ξ₀, hξ₀⟩ := exists_algClosed_point (Spec (CommRingCat.of C)) P
  let ξ : Over.mk (ξ₀ ≫ (ringTest K C).hom) ⟶ ringTest K C := Over.homMk ξ₀ rfl
  let αB := ξ ≫ ringTestMap K f
  let βB := ξ ≫ ringTestMap K g
  have hαpt : ∀ w, αB.left w = q := fun w => by
    change PrimeSpectrum.comap (f : B →+* C) (ξ₀ w) = q
    rw [hξ₀]
    exact hPf
  have key : αB ≫ e.inv = βB ≫ e.inv := eq_of_comp_chart_eq h ht hs n tM hcomp _ _
    (fun w => by
      rw [Over.comp_left, Scheme.Hom.comp_apply, hαpt]
      exact hq)
    (by
      simp only [αB, βB, Functor.map_comp, Category.assoc]
      rw [hpb.w])
  have hαβ : αB = βB := by
    simpa using congrArg (· ≫ e.hom) key
  let δ := ringTestMap K μ
  have hδf : δ ≫ ringTestMap K f = 𝟙 _ := by
    rw [← ringTestMap_comp, hf, ringTestMap_id]
  have hδg : δ ≫ ringTestMap K g = 𝟙 _ := by
    rw [← ringTestMap_comp, hg, ringTestMap_id]
  have hξ : ξ = αB ≫ δ := hom_ext_of_isPullback hpb
    (by rw [Category.assoc, hδf, Category.comp_id])
    (by rw [Category.assoc, hδg, Category.comp_id, hαβ])
  have hpt := congrArg (fun φ => φ.left (IsLocalRing.closedPoint Ω)) hξ
  rw [← hξ₀ (IsLocalRing.closedPoint Ω)]
  refine hpt.trans ?_
  change PrimeSpectrum.comap (μ : C →+* B) (αB.left (IsLocalRing.closedPoint Ω)) = _
  rw [hαpt]

end Tuples

end SeparatedElementaryEtalePoint

open SeparatedElementaryEtalePoint UniformFieldPointCharts in
set_option backward.isDefEq.respectTransparency false in
/-- **Elementary étale points of separated algebraic spaces** (Stacks, Tag 0BBP, ring-point
form, for separated spaces). -/
theorem separatedElementaryEtalePoint : SeparatedElementaryEtalePointStatement.{u} := by
  intro K _ X hX A _ _ hA x hx p
  obtain ⟨R, t, s, hpb, ht, hs⟩ := exists_kernelPair hx
  have : IsAffine (ringTest K A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have : IsAffine R.left := isAffine_of_isPullback_of_closedDiagonal hX _ _ t s hpb
  let E := rel hpb ht hs
  obtain ⟨n, ⟨-, hpn, hpn1⟩, -⟩ := E.exists_unique_tupleDegreeLocus p
  obtain ⟨y₀, ⟨w', rfl⟩, r, hrs, hrt⟩ := (E.mem_pointSaturationOpen _ _).mp hpn
  obtain ⟨tM, htM, hcomp⟩ := exists_chart hpb ht hs hx n
  let V := quot hpb ht hs n
  let B := AffineCoordinateRing K V
  let e : V ≅ ringTest K B := affineSchemeOverIso K V
  have : LocallyOfFiniteType (ringTest K A).hom :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr hA)
  have hV : LocallyOfFiniteType V.hom := by
    apply locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp _ _ _
      (quotMap hpb ht hs n).left V.hom
    · exact inferInstanceAs (Surjective (E.tupleSymmetricMap n))
    · exact inferInstanceAs (Flat (E.tupleSymmetricMap n))
    · exact inferInstanceAs (LocallyOfFinitePresentation (E.tupleSymmetricMap n))
    · rw [Over.w (quotMap hpb ht hs n)]
      change LocallyOfFiniteType (E.tupleDistinctProjection n 0 ≫ (ringTest K A).hom)
      infer_instance
  have hB : Algebra.FiniteType K B := (affineCoordinate_finiteType_iff K V).mpr hV
  have hq' : E.tupleSymmetricMap n w' ∉ E.tupleSymmetricThresholdOpen n (n + 1) := fun hmem =>
    hpn1 (E.tupleThresholdOpen_invariant (n + 1) ⟨r, hrs, hrt⟩
      ((E.tupleSymmetricMap_mem_threshold_iff n (n + 1) w').mp hmem))
  refine ⟨B, inferInstance, inferInstance, hB,
    uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map e.inv ≫ tM),
    e.hom.left (E.tupleSymmetricMap n w'), ?_, ?_, ?_⟩
  · rw [Equiv.symm_apply_apply]
    exact IsEtale.iso_comp ((schemeYoneda _).mapIso e.symm) htM
  · intro D _ _ f g hD
    rw [Equiv.symm_apply_apply] at hD
    obtain ⟨P, h1, h2⟩ := exists_point_of_isPullback hpb ht hs n tM hcomp e _ _ hD w' r hrs
    exact ⟨P, h1, h2.trans hrt⟩
  · intro C _ _ f g hC μ hf hg P hPf _
    rw [Equiv.symm_apply_apply] at hC
    refine eq_comap_of_isPullback hpb ht hs n tM hcomp e _ ?_ C f g hC μ hf hg P hPf
    have he : e.inv.left (e.hom.left (E.tupleSymmetricMap n w')) = E.tupleSymmetricMap n w' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id]
      rfl
    rw [he]
    exact hq'

end Langlands.AlgebraicGeometry.AlgebraicSpace
