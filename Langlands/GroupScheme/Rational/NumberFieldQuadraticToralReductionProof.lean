import Langlands.GroupScheme.Rational.NumberFieldQuadraticToralReductionStatement
import Langlands.GroupScheme.Rational.QuadraticToralComplexApproximation
import Langlands.GroupScheme.Rational.QuadraticRealToralValue
import Langlands.GroupScheme.Rational.QuadraticRealToralCoboundary

/-! # Toral reduction of quadratic cocycles over number fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology Langlands.Global.AdelicFunctoriality
open scoped NumberField.LiesOver InfiniteExtension CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

private theorem extend_open_family {A B : Type u} {X : B → Type u} [∀ b, TopologicalSpace (X b)]
    (j : A → B) (hj : Function.Injective j) (U : ∀ a, Set (X (j a)))
    (hU : ∀ a, IsOpen (U a)) (hUn : ∀ a, (U a).Nonempty) (hX : ∀ b, Nonempty (X b)) :
    ∃ V : ∀ b, Set (X b), (∀ b, IsOpen (V b) ∧ (V b).Nonempty) ∧ ∀ a, V (j a) = U a := by
  classical
  let V (b : B) : Set (X b) := if h : ∃ a, j a = b then h.choose_spec ▸ U h.choose else Set.univ
  have heq (a : A) : V (j a) = U a := by
    let h : ∃ x, j x = j a := ⟨a, rfl⟩
    change (if p : ∃ x, j x = j a then p.choose_spec ▸ U p.choose else Set.univ) = U a
    rw [dite_eq_left h]
    have hcongr (x y : A) (hx : x = y) (e : j x = j y) : e ▸ U x = U y := by
      subst y
      rfl
    exact hcongr _ _ (hj h.choose_spec) _
  refine ⟨V, fun b => ?_, heq⟩
  by_cases hb : ∃ a, j a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [heq]
    exact ⟨hU a, hUn a⟩
  · dsimp only [V]
    rw [dite_eq_right hb]
    exact ⟨isOpen_univ, Classical.choice (hX b), Set.mem_univ _⟩

private theorem exists_approximate_at_selected_complexPlaces
    (L : Type u) [Field L] [NumberField L]
    (H : GroupScheme (Spec (CommRingCat.of L))) [IsAffine H.X.left]
    (hH : IsConnectedReductive H) {R : Type u}
    (j : R → ComplexPlace L) (hj : Function.Injective j)
    (U : ∀ r, Set (RingPoint L H.X (j r).1.Completion))
    (hU : ∀ r, IsOpen (U r)) (hUn : ∀ r, (U r).Nonempty) :
    ∃ p : RingPoint L H.X L,
      ∀ r, p.changeRing (Algebra.ofId L (j r).1.Completion) ∈ U r := by
  have hone (q : ComplexPlace L) : Nonempty (RingPoint L H.X q.1.Completion) :=
    ⟨(1 : ringTest L q.1.Completion ⟶ H.X)⟩
  obtain ⟨V, hV, hVU⟩ := extend_open_family
    (X := fun q : ComplexPlace L => RingPoint L H.X q.1.Completion) j hj U hU hUn hone
  obtain ⟨p, hp⟩ := exists_approximate_complexPoints L H hH V (fun q => (hV q).1) (fun q => (hV q).2)
  exact ⟨p, fun r => hVU r ▸ hp (j r)⟩

private theorem exists_of_complexPoint_opens
    (L : Type u) [Field L] [NumberField L]
    (H : GroupScheme (Spec (CommRingCat.of L))) [IsAffine H.X.left]
    (hH : IsConnectedReductive H) {R A : Type u} (hR : Nonempty R)
    (j : R → ComplexPlace L) (hj : Function.Injective j)
    (e : A ≃ RingPoint L H.X L) (P : A → Prop) (Q : R → A → Prop)
    (h : ∀ r, ∃ U : Set (RingPoint L H.X (j r).1.Completion), IsOpen U ∧ U.Nonempty ∧
      ∀ f : A, (e f).changeRing (Algebra.ofId L (j r).1.Completion) ∈ U → P f ∧ Q r f) :
    ∃ f, P f ∧ ∀ r, Q r f := by
  classical
  choose U hU hUn hgood using h
  obtain ⟨p, hp⟩ := exists_approximate_at_selected_complexPlaces L H hH j hj U hU hUn
  let f := e.symm p
  have hf (r : R) : P f ∧ Q r f := by
    apply hgood r f
    rw [show e f = p from e.apply_symm_apply p]
    exact hp r
  exact ⟨f, (hf (Classical.choice hR)).1, fun r => (hf r).2⟩

private theorem exists_twist_with_local_squares
    {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (v : ∀ w : InfinitePlace F, InfinitePlacesAbove L w) (hdeg : Module.finrank F L = 2)
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (ξ : Cocycle G (ringTest F L))
    (hξ : ∀ w : InfinitePlace F, w.IsReal → (ξ.baseChangePullback (algebraBaseMap F w.Completion)).IsTrivial)
    (σ : L ≃ₐ[F] L) (hσ : σ ≠ 1) :
    ∃ f : G.affinePoints (CommAlgCat.of F L),
      HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap F L) G).symm
        (GaloisCocycle.value (ξ.twist f) σ)) ∧
      ∀ (w : InfinitePlace F) (hw : w.IsReal) (hv : (v w).1.IsComplex),
        HasInertSquare (v w) hdeg hw hv σ (ξ.twist f) := by
  classical
  let R := {w : InfinitePlace F // w.IsReal ∧ (v w).1.IsComplex}
  by_cases hR : Nonempty R
  swap
  · obtain ⟨f, hf⟩ := exists_regular_cochain hG ξ σ hσ
    exact ⟨f, hf, fun w hw hv => (hR ⟨⟨w, hw, hv⟩⟩).elim⟩
  let b := algebraBaseMap F L
  let H := (baseChange b).obj G
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let j (r : R) : ComplexPlace L := ⟨(v r.1).1, r.2.2⟩
  have hj : Function.Injective j := by
    intro r s h
    apply Subtype.ext
    have heq := congrArg Subtype.val h
    have hr : (j r).1.comap (algebraMap F L) = r.1 := InfinitePlace.LiesOver.comap_eq (v r.1).1 r.1
    have hs : (j s).1.comap (algebraMap F L) = s.1 := InfinitePlace.LiesOver.comap_eq (v s.1).1 s.1
    exact hr.symm.trans ((congrArg (fun x : InfinitePlace L => x.comap (algebraMap F L)) heq).trans hs)
  let A := G.affinePoints (CommAlgCat.of F L)
  let e : A ≃ RingPoint L H.X L := (affinePointsBaseChangeMulEquiv F L L G).toEquiv
  let P (f : A) := HasToralCentralizer ((baseChangeBasePointsEquiv b G).symm
    (GaloisCocycle.value (ξ.twist f) σ))
  let Q (r : R) (f : A) := HasInertSquare (v r.1) hdeg r.2.1 r.2.2 σ (ξ.twist f)
  have hopen (r : R) : ∃ U : Set (RingPoint L H.X (j r).1.Completion),
      IsOpen U ∧ U.Nonempty ∧
        ∀ f : A, (e f).changeRing (Algebra.ofId L (j r).1.Completion) ∈ U → P f ∧ Q r f :=
    exists_inert_cochainOpen (v r.1) hdeg r.2.1 r.2.2 σ hσ hG ξ (hξ r.1 r.2.1)
  obtain ⟨f, hP, hQ⟩ := exists_of_complexPoint_opens L H
    (connectedReductiveFieldExtensionStatement F L G hG) hR j hj e P Q hopen
  exact ⟨f, hP, fun w hw hv => hQ ⟨w, hw, hv⟩⟩

end QuadraticToralReduction

open QuadraticToralReduction in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- Every quadratic cocycle trivial at the real places has a cohomologous
representative in a maximal torus that is trivial on each real pullback. -/
theorem numberFieldQuadraticToralReduction : NumberFieldQuadraticToralReductionStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ hdeg ξ hξ
  classical
  let : NumberField L := NumberField.of_module_finite F L
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let v (w : InfinitePlace F) := Classical.choice (nonempty_infinitePlacesAbove (L := L) hdeg w)
  obtain ⟨σ, hσ, hσ₂, hσcases⟩ := quadratic_generator hdeg
  obtain ⟨f, hcent, hlocal⟩ := exists_twist_with_local_squares v hdeg hG ξ hξ σ hσ
  obtain ⟨S, j, hj, hjc⟩ := hcent
  obtain ⟨T, i, d, hi, hr, hmap⟩ := factor_of_quadratic_value (ξ.twist f) σ hσ₂ hσcases j hj hjc
  refine ⟨T, i, d, hi, ?_, ⟨f, hmap⟩⟩
  intro w hw
  change (d.baseChangePullback (algebraBaseMap F w.Completion)).IsTrivial
  rcases InfinitePlace.isReal_or_isComplex (v w).1 with hv | hv
  · obtain ⟨s⟩ := split_cover_section (v w) hw hv
    exact isTrivial_of_cover_section _ s
  · obtain ⟨s, hs, hτs⟩ := hlocal w hw hv
    exact isTrivial_toral_inert (v w) hdeg hw hv σ i hσ hi.2.1 (ξ.twist f) d (hr.trans hjc)
      (hmap (𝟙 _) (GaloisCocycle.arrow F L σ)) s hs hτs

end Langlands.GroupScheme
