import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineDiagonal
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing

/-!
# Rational points of the Galois-twisted line

For `s ∈ K'` let `u_s` be the `K'`-point of the line with coordinate `s`, and `a(u_s)` its image
in the Galois-twisted line `X`. Viewed in `X_{K'}(K')`, these points depend continuously on `s`.
For `c ∈ K` nonzero, `a(u_c)` comes from a `K`-point: its two pullbacks to any scheme over
`Spec K' ⊗_K K'` are related by the relation, because the coordinate `c` is a unit. The point
`a(u_0)` does not come from a `K`-point: it would be invariant under the conjugation, which
would relate `u_0` to its conjugate, and over the field `K'` a relating point lies on one
of the two components of the relation, where either the conjugation is trivial or the coordinate
`0` is a unit. So the image of `X(K)` in `X_{K'}(K')` is not closed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Polynomial Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap ringTestMap_comp ringTestMap_left schemePointTopology
    schemePointTopology_eq_affine ringBaseChange ringPointBaseChangeEquiv
    schemeBaseChangeTopology_proof affineRingPointEquiv spectrumAlgebraPointHomeomorph AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

open RelationQuotient KernelPair HenselianIntegralPointsNotClosed

/-- The map `B → Γ(Spec B, ⊤)`. -/
abbrev unitSpec (B : Type u) [CommRing B] : B →+* Γ(Spec (CommRingCat.of B), ⊤) :=
  ofSpec (𝟙 (Spec (CommRingCat.of B)))

theorem ofSpec_specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ofSpec (Spec.map (CommRingCat.ofHom f)) = (unitSpec B).comp f := by
  have := ofSpec_comp (𝟙 (Spec (CommRingCat.of B))) f
  rwa [Category.id_comp] at this

theorem unitSpec_injective (B : Type u) [CommRing B] : Function.Injective (unitSpec B) := by
  intro a b h
  have e : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (unitSpec B c) = c := by
    intro c
    simp [unitSpec, ofSpec]
  rw [← e a, ← e b, h]

section Points

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

theorem ofSpec_ringTestMap {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) : ofSpec (ringTestMap K f).left = (unitSpec B).comp f.toRingHom :=
  ofSpec_specMap _

variable (K) in
/-- The `K'`-point of the line with coordinate `s`. -/
def linePt (s : K') : ringTest K K' ⟶ lineOver K K' :=
  ringTestMap K ((Polynomial.aeval s).restrictScalars K)

theorem ofSpec_linePt (s : K') :
    ofSpec (linePt K s).left = (unitSpec K').comp ((Polynomial.aeval s).restrictScalars K).toRingHom :=
  ofSpec_ringTestMap _

/-- Points of the line over `K`: on constants from `K` they are the structure map. -/
theorem ofSpec_left_algebraMap {T : Over (Spec (CommRingCat.of K))} (τ : T ⟶ lineOver K K')
    (k : K) : ofSpec τ.left (C (algebraMap K K' k)) = ofSpec T.hom k := by
  have e : (ofSpec τ.left).comp (algebraMap K K'[X]) = ofSpec T.hom := by
    rw [← ofSpec_comp]
    congr 1
    exact Over.w τ
  rw [← e, RingHom.comp_apply, Polynomial.algebraMap_apply]

/-- Over a ring with an injective map from `K'`, no point of the relation relates the point
with coordinate `0` to its conjugate. -/
theorem relation_false {Γ : Type*} [CommRing Γ] (φ : RelationRing K' →+* Γ) (ε : K' →+* Γ)
    (hε : Function.Injective ε)
    (ht : ∀ p, (φ.comp tStar) p = ε (D.σ (Polynomial.aeval (0 : K') p)))
    (hs : ∀ p, (φ.comp (sStar D)) p = ε (Polynomial.aeval (0 : K') p)) : False := by
  have hb := sameBase_of_hom D φ
  have hu := isUnit_pairUnit_of_hom D φ
  have he := pairIdem_isIdempotentElem D hb
  have hX : (φ.comp tStar) X = 0 := by
    rw [ht, aeval_X, map_zero, map_zero]
  rw [pairUnit, hX, mul_zero, add_zero] at hu
  have h1 : pairIdem D (φ.comp tStar) (φ.comp (sStar D)) = 1 := by
    obtain ⟨v, hv⟩ := hu
    have hvv : (v : Γ) * v = v := by rw [hv]; exact he
    have : (v : Γ) = 1 := by
      have := congrArg (· * (↑v⁻¹ : Γ)) hvv
      simpa [mul_assoc] using this
    rw [← hv, this]
  have hθ := splitIdem_mul_θ (D := D) (μ₁ := (φ.comp tStar).comp C)
    (μ₂ := (φ.comp (sStar D)).comp C) hb.1
  change pairIdem D (φ.comp tStar) (φ.comp (sStar D)) * _ = 0 at hθ
  rw [h1, one_mul, sub_eq_zero] at hθ
  have h3 : ((φ.comp (sStar D)).comp C) D.θ = ε D.θ := by
    change (φ.comp (sStar D)) (C D.θ) = _
    rw [hs, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  have h4 : ((φ.comp tStar).comp C) D.θ = ε (D.σ D.θ) := by
    change (φ.comp tStar) (C D.θ) = _
    rw [ht, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h3, h4] at hθ
  exact D.ne (hε hθ).symm

theorem ofSpec_linePt_apply (s : K') (p : K'[X]) :
    ofSpec (linePt K s).left p = unitSpec K' (Polynomial.aeval s p) := by
  rw [ofSpec_linePt]
  rfl

theorem ofSpec_conj_linePt_apply (s : K') (p : K'[X]) :
    ofSpec (ringTestMap K D.σ.toAlgHom ≫ linePt K s).left p =
      unitSpec K' (D.σ (Polynomial.aeval s p)) := by
  have hσ : ringTestMap K D.σ.toAlgHom ≫ linePt K s = ringTestMap K
      (D.σ.toAlgHom.comp ((Polynomial.aeval s).restrictScalars K)) := by
    rw [ringTestMap_comp]
    rfl
  rw [hσ, ofSpec_ringTestMap]
  rfl

/-- A `K'`-point coming from `K` is invariant under the conjugation. -/
theorem atlas_app_conj_of_changeRing {x : RingPoints K (space D) K} {s : K'}
    (hx : RingPoints.changeRing (Algebra.ofId K K') x =
      (atlas D).app (op (ringTest K K')) ⟨linePt K s⟩) :
    (atlas D).app (op (ringTest K K')) ⟨ringTestMap K D.σ.toAlgHom ≫ linePt K s⟩ =
      (atlas D).app (op (ringTest K K')) ⟨linePt K s⟩ := by
  have hπ : ringTestMap K D.σ.toAlgHom ≫ ringTestMap K (Algebra.ofId K K') =
      ringTestMap K (Algebra.ofId K K') := by
    rw [← ringTestMap_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [atlas_app_comp, ← hx]
  exact ((Functor.map_comp_apply _ _ _ _).symm.trans
    (congrArg (fun g : ringTest K K' ⟶ ringTest K K => (space D).presheaf.map g.op x) hπ))

theorem ofSpec_comp_tOver {T : Over (Spec (CommRingCat.of K))} (r : T ⟶ relOver D) :
    (ofSpec r.left).comp tStar = ofSpec (r ≫ tOver D).left :=
  (ofSpec_comp_tMap r.left).symm

theorem ofSpec_comp_sOver {T : Over (Spec (CommRingCat.of K))} (r : T ⟶ relOver D) :
    (ofSpec r.left).comp (sStar D) = ofSpec (r ≫ sOver D).left :=
  (ofSpec_comp_sMap D r.left).symm

/-- **The point with coordinate `0` does not descend.** -/
theorem changeRing_ne_zero (x : RingPoints K (space D) K) :
    RingPoints.changeRing (Algebra.ofId K K') x ≠
      (atlas D).app (op (ringTest K K')) ⟨linePt K 0⟩ := by
  intro hx
  have hinv := atlas_app_conj_of_changeRing D hx
  obtain ⟨r, hr₁, hr₂⟩ := EtaleEquivalenceRelation.exists_lift_of_isPullback (isPullback_atlas D)
    (ringTestMap K D.σ.toAlgHom ≫ linePt K 0) (linePt K 0) (map_comp_eq_of_app_eq (atlas D) hinv)
  have ht := ofSpec_comp_tOver D r
  have hs := ofSpec_comp_sOver D r
  rw [hr₁] at ht
  rw [hr₂] at hs
  exact relation_false D (ofSpec r.left) (unitSpec K') (unitSpec_injective K')
    (fun p => (RingHom.congr_fun ht p).trans (ofSpec_conj_linePt_apply D 0 p))
    (fun p => (RingHom.congr_fun hs p).trans (ofSpec_linePt_apply 0 p))

/-- An idempotent plus its complement times a unit is a unit. -/
theorem isUnit_idem_add {Γ : Type*} [CommRing Γ] {e v : Γ} (he : IsIdempotentElem e)
    (hv : IsUnit v) : IsUnit (e + (1 - e) * v) := by
  obtain ⟨w, rfl⟩ := hv
  refine IsUnit.of_mul_eq_one (e + (1 - e) * ↑w⁻¹) ?_
  have he' : e * e = e := he
  have hw : (w : Γ) * ↑w⁻¹ = 1 := w.mul_inv
  linear_combination (2 - (↑w⁻¹ : Γ) - (w : Γ)) * he' + (1 - e + (e * e - e)) * hw

/-- For `c ∈ K` nonzero, two pullbacks of the point with coordinate `c` that agree over `K`
are related. -/
theorem atlas_app_eq_of_comp_eq (c : K) (hc : c ≠ 0) {Z : Over (Spec (CommRingCat.of K))}
    (q₁ q₂ : Z ⟶ ringTest K K')
    (_h : q₁ ≫ ringTestMap K (Algebra.ofId K K') = q₂ ≫ ringTestMap K (Algebra.ofId K K')) :
    (atlas D).app (op Z) ⟨q₁ ≫ linePt K (algebraMap K K' c)⟩ =
      (atlas D).app (op Z) ⟨q₂ ≫ linePt K (algebraMap K K' c)⟩ := by
  let τ₁ : Z ⟶ lineOver K K' := q₁ ≫ linePt K (algebraMap K K' c)
  let τ₂ : Z ⟶ lineOver K K' := q₂ ≫ linePt K (algebraMap K K' c)
  have hX : ∀ q : Z ⟶ ringTest K K',
      ofSpec (q ≫ linePt K (algebraMap K K' c)).left X = ofSpec Z.hom c := by
    intro q
    rw [← ofSpec_left_algebraMap (q ≫ linePt K (algebraMap K K' c)) c]
    change ofSpec (q.left ≫ (linePt K (algebraMap K K' c)).left) X =
      ofSpec (q.left ≫ (linePt K (algebraMap K K' c)).left) (C (algebraMap K K' c))
    rw [ofSpec_precomp]
    refine congrArg q.left.appTop.hom ?_
    rw [ofSpec_linePt_apply, ofSpec_linePt_apply, aeval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hb : SameBase K (ofSpec τ₁.left) (ofSpec τ₂.left) :=
    ⟨fun k => (ofSpec_left_algebraMap τ₁ k).trans (ofSpec_left_algebraMap τ₂ k).symm,
      (hX q₁).trans (hX q₂).symm⟩
  have hu : IsUnit (pairUnit D (ofSpec τ₁.left) (ofSpec τ₂.left)) := by
    rw [pairUnit, hX q₁]
    exact isUnit_idem_add (pairIdem_isIdempotentElem D hb) ((IsUnit.mk0 c hc).map _)
  let φ := relHom D hb hu
  have hleft : toSpec φ ≫ tMap K' = τ₁.left := by
    apply ofSpec_injective
    rw [ofSpec_comp_tMap, ofSpec_toSpec, relHom_comp_tStar]
  let r : Z ⟶ relOver D := Over.homMk (toSpec φ) (by
    change toSpec φ ≫ tMap K' ≫ lineBase = Z.hom
    rw [← Category.assoc, hleft]
    exact Over.w τ₁)
  have hr₁ : r ≫ tOver D = τ₁ := by
    ext1
    exact hleft
  have hr₂ : r ≫ sOver D = τ₂ := by
    ext1
    apply ofSpec_injective
    change ofSpec (toSpec φ ≫ sMap D) = _
    rw [ofSpec_comp_sMap, ofSpec_toSpec, relHom_comp_sStar]
  change (atlas D).app (op Z) ⟨τ₁⟩ = (atlas D).app (op Z) ⟨τ₂⟩
  rw [← hr₁, ← hr₂]
  exact atlas_app_t_eq_s D r

theorem flat_ofId : Flat (ringTestMap K (Algebra.ofId K K')).left := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap K K')))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change (algebraMap K K').Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

theorem locallyOfFinitePresentation_ofId [Module.Finite K K'] :
    LocallyOfFinitePresentation (ringTestMap K (Algebra.ofId K K')).left := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K K')))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  change (algebraMap K K').FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

theorem surjective_ofId : Surjective (ringTestMap K (Algebra.ofId K K')).left :=
  ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- **For `c ∈ K` nonzero, the point with coordinate `c` descends to a `K`-point.** -/
theorem exists_changeRing_eq [Module.Finite K K'] (c : K) (hc : c ≠ 0) :
    ∃ x : RingPoints K (space D) K, RingPoints.changeRing (Algebra.ofId K K') x =
      (atlas D).app (op (ringTest K K')) ⟨linePt K (algebraMap K K' c)⟩ := by
  have := flat_ofId (K := K) (K' := K')
  have := locallyOfFinitePresentation_ofId (K := K) (K' := K')
  have := surjective_ofId (K := K) (K' := K')
  obtain ⟨x, hx, -⟩ := Presieve.isSheafFor_singleton.mp
    (ProductPointsDescent.isSheafFor_singleton (space D) (ringTestMap K (Algebra.ofId K K')))
    ((atlas D).app (op (ringTest K K')) ⟨linePt K (algebraMap K K' c)⟩) (fun q₁ q₂ h => by
      rw [← atlas_app_comp, ← atlas_app_comp]
      exact atlas_app_eq_of_comp_eq D c hc q₁ q₂ h)
  exact ⟨x, hx⟩

end Points

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
