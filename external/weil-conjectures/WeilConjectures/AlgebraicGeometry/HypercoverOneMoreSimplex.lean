/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SimplicialHomObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import WeilConjectures.AlgebraicGeometry.SemiRepresentableCoveringPermanence
import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
import WeilConjectures.AlgebraicGeometry.SimplicialHomObjectPushout
import WeilConjectures.AlgebraicGeometry.SimplicialHomStandardSimplex
import WeilConjectures.AlgebraicTopology.GlueSimplex

/-!
# Adding one simplex to a hypercover Hom object

Source: Stacks Project, Tag 01GM, Lemma `lemma-one-more-simplex`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

private theorem covering_of_split_epi {X : Scheme.{u}}
    {A B : FormalCoproduct.{w} X.Etale} (f : A ⟶ B) (g : B ⟶ A)
    (h : g ≫ f = 𝟙 B) : IsSemiRepresentableCovering f := by
  intro j
  apply (X.smallEtaleTopology).covering_of_eq_top
  rw [← Sieve.id_mem_iff_eq_top]
  obtain ⟨e, he⟩ := (FormalCoproduct.hom_ext_iff' _ _).mp h j
  let i : {i : A.I // f.f i = j} := ⟨g.f j, e⟩
  refine ⟨_, g.φ j, _, Presieve.ofArrows.mk i, ?_⟩
  simpa [i, Category.assoc] using he

private theorem covering_of_iso {X : Scheme.{u}}
    {A B : FormalCoproduct.{w} X.Etale} (e : A ≅ B) :
    IsSemiRepresentableCovering e.hom :=
  covering_of_split_epi e.hom e.inv e.inv_hom_id

private theorem covering_pullback {X : Scheme.{u}}
    {P A B C : FormalCoproduct.{w} X.Etale}
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (hsq : IsPullback fst snd f g) (hg : IsSemiRepresentableCovering g) :
    IsSemiRepresentableCovering fst := by
  rw [← hsq.isoPullback_hom_fst]
  exact (semiRepresentableCovering_comp_baseChange _
    (covering_of_iso hsq.isoPullback)).1 _
    ((semiRepresentableCovering_comp_baseChange g hg).2 f)

private def pullFamily {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S T : SSet.{t}}
    {H : FormalCoproduct.{w} X.Etale} (v : SimplicialHomFamily K T H) (f : S ⟶ T) :
    SimplicialHomFamily K S H :=
  ⟨fun n s ↦ v.val n (f.app _ s), by
    intro m n φ s
    rw [v.property]
    apply congrArg (v.val m)
    exact (congrArg (fun a ↦ a s) (f.naturality φ.op)).symm⟩

private noncomputable def liftFamily {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {H W : FormalCoproduct.{w} X.Etale} {u : SimplicialHomFamily K S H}
    (hu : (simplicialHomFamilyFunctor K S).IsRepresentedBy u)
    (f : SimplicialHomFamily K S W) : W ⟶ H :=
  (Equiv.ofBijective _ hu.map_bijective).symm f

private theorem liftFamily_val {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {H W : FormalCoproduct.{w} X.Etale} {u : SimplicialHomFamily K S H}
    (hu : (simplicialHomFamilyFunctor K S).IsRepresentedBy u)
    (f : SimplicialHomFamily K S W) (n : ℕ) (s : S.obj (op ⦋n⦌)) :
    liftFamily hu f ≫ u.val n s = f.val n s := by
  exact congrArg (fun a : SimplicialHomFamily K S W ↦ a.val n s)
    ((Equiv.ofBijective _ hu.map_bijective).apply_symm_apply f)

private theorem restriction_val {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    (A : S.Subcomplex) {H H' : FormalCoproduct.{w} X.Etale}
    (v : SimplicialHomFamily K S H) {u : SimplicialHomFamily K A.toSSet H'}
    (hu : (simplicialHomFamilyFunctor K A.toSSet).IsRepresentedBy u)
    (n : ℕ) (s : A.toSSet.obj (op ⦋n⦌)) :
    simplicialHomRestriction A v hu ≫ u.val n s = v.val n s.val :=
  liftFamily_val hu (v.restrict A) n s

private theorem oneSimplexPushout {V : SSet.{t}} (U : V.Subcomplex)
    (n : ℕ) (x : V.obj (op ⦋n⦌)) (hx : x ∉ U.obj (op ⦋n⦌))
    (hlower : ∀ i : ℕ, i < n → U.obj (op ⦋i⦌) = Set.univ)
    (hdegree : (Set.univ : Set (V.obj (op ⦋n⦌))) = U.obj (op ⦋n⦌) ∪ {x})
    (hhigher : ∀ (j : ℕ) (z : V.obj (op ⦋j⦌)),
      n < j → z ∉ U.obj (op ⦋j⦌) → z ∈ V.degenerate j) :
    ∃ b : (SSet.boundary n).toSSet ⟶ U.toSSet,
      IsPushout b (SSet.boundary n).ι U.ι (SSet.yonedaEquiv.symm x) := by
  let y : (⊤ : V.Subcomplex).toSSet.obj (op ⦋n⦌) := ⟨x, trivial⟩
  obtain ⟨b, _, hp⟩ := SSet.glue_simplex U ⊤ le_top y hx
    (fun i hi ↦ (hlower i hi).symm) hdegree
    (fun j hj z hz ↦ (SSet.Subcomplex.mem_degenerate_iff _ z).mpr
      (hhigher j z.val hj hz))
  refine ⟨b, hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (SSet.Subcomplex.topIso V) (by simp) (by simp) (by simp) ?_⟩
  simp only [SSet.yonedaEquiv_symm_comp, SSet.Subcomplex.topIso_hom]
  rfl

private theorem homFamily_exists {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t}) [S.Finite]
    (hfin : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌)))
    (hne : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))) :
    ∃ (H : FormalCoproduct.{w} X.Etale) (u : SimplicialHomFamily K S H),
      (simplicialHomFamilyFunctor K S).IsRepresentedBy u := by
  obtain ⟨H, a, ha, hh⟩ := exists_simplicial_hom_object X K S hfin hne
  let u : SimplicialHomFamily K S H := ⟨a, ha⟩
  refine ⟨H, u, ⟨?_⟩⟩
  intro W
  change Function.Bijective (fun g : W ⟶ H ↦ u.precomp g)
  rw [Function.bijective_iff_existsUnique]
  intro f
  obtain ⟨g, hg, huniq⟩ := hh W f.val f.property
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    funext n s
    exact hg n s
  · intro g' hg'
    apply huniq
    intro n s
    exact congrArg (fun a : SimplicialHomFamily K S W ↦ a.val n s) hg'

private theorem positive_case
    {X : Scheme.{u}} (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) (V : SSet.{t}) (U : V.Subcomplex)
    (hV : ∀ i : ℕ, Finite (V.obj (op ⦋i⦌)) ∧ Nonempty (V.obj (op ⦋i⦌)))
    (hU : ∀ i : ℕ, Finite (U.toSSet.obj (op ⦋i⦌)) ∧
      Nonempty (U.toSSet.obj (op ⦋i⦌))) [V.Finite] [U.toSSet.Finite]
    (n : ℕ) (x : V.obj (op ⦋n + 1⦌)) (hx : x ∉ U.obj (op ⦋n + 1⦌))
    (hlower : ∀ i : ℕ, i < n + 1 → U.obj (op ⦋i⦌) = Set.univ)
    (hdegree : (Set.univ : Set (V.obj (op ⦋n + 1⦌))) = U.obj (op ⦋n + 1⦌) ∪ {x})
    (hhigher : ∀ (j : ℕ) (z : V.obj (op ⦋j⦌)), n + 1 < j →
      z ∉ U.obj (op ⦋j⦌) → z ∈ V.degenerate j)
    {HV HU : FormalCoproduct.{w} X.Etale}
    (v : SimplicialHomFamily K V HV) (u : SimplicialHomFamily K U.toSSet HU)
    (hv : (simplicialHomFamilyFunctor K V).IsRepresentedBy v)
    (hu : (simplicialHomFamilyFunctor K U.toSSet).IsRepresentedBy u) :
    IsSemiRepresentableCovering (simplicialHomRestriction U v hu) := by
  obtain ⟨b, hpush⟩ := oneSimplexPushout U (n + 1) x hx hlower hdegree hhigher
  obtain ⟨hΔ, hΔfinite, _, ⟨c, hc, hcrep⟩, _⟩ :=
    simplicial_hom_standard_simplex.{u, w, t} K (n + 1)
  obtain ⟨hboundary, hboundaryfinite, hmatch⟩ := simplicial_hom_boundary_matching.{u, w, t} K n
  let : (Δ[n + 1] : SSet.{t}).Finite := hΔfinite
  let : (SSet.boundary.{t} (n + 1)).toSSet.Finite := hboundaryfinite
  obtain ⟨HA, a, harep⟩ := homFamily_exists K (SSet.boundary (n + 1)).toSSet
    (fun m ↦ (hboundary m).1) (fun m ↦ (hboundary m).2)
  obtain ⟨⟨θ, hθ, _⟩, ⟨ρ, hρ, _⟩, heq⟩ := hmatch HA a harep
  have hρcov : IsSemiRepresentableCovering ρ := by
    have he : ρ = semiRepresentableMatchingMap K (n + 1) ≫ θ.inv := by
      rw [← heq θ hθ ρ hρ]
      simp
    rw [he]
    exact (semiRepresentableCovering_comp_baseChange _ (hK (n + 1))).1 _
      (covering_of_iso θ.symm)
  let p : HU ⟶ HA := liftFamily harep (pullFamily u b)
  have hsq := simplicialHomObject_pushout_isPullback
    (fun m ↦ (hboundary m).1) (fun m ↦ (hboundary m).2)
    (fun m ↦ (hU m).1) (fun m ↦ (hU m).2)
    (fun m ↦ (hΔ m).1) (fun m ↦ (hΔ m).2)
    (fun m ↦ (hV m).1) (fun m ↦ (hV m).2)
    b (SSet.boundary (n + 1)).ι U.ι (SSet.yonedaEquiv.symm x) hpush
    a harep u c v hu hcrep hv
    (simplicialHomRestriction U v hu) (v.val (n + 1) x)
    (restriction_val U v hu)
    (by
      intro m s
      rw [hc]
      exact v.property m (n + 1) (SSet.stdSimplex.objEquiv s) x)
    p ρ (liftFamily_val harep (pullFamily u b))
    (by
      intro m s
      rw [hc]
      exact hρ m s)
  exact covering_pullback hsq hρcov

private theorem zero_case
    {X : Scheme.{u}} (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) (V : SSet.{t}) (U : V.Subcomplex)
    (hV : ∀ i : ℕ, Finite (V.obj (op ⦋i⦌)) ∧ Nonempty (V.obj (op ⦋i⦌)))
    (hU : ∀ i : ℕ, Finite (U.toSSet.obj (op ⦋i⦌)) ∧
      Nonempty (U.toSSet.obj (op ⦋i⦌))) [V.Finite] [U.toSSet.Finite]
    (x : V.obj (op ⦋0⦌)) (hx : x ∉ U.obj (op ⦋0⦌))
    (hdegree : (Set.univ : Set (V.obj (op ⦋0⦌))) = U.obj (op ⦋0⦌) ∪ {x})
    (hhigher : ∀ (j : ℕ) (z : V.obj (op ⦋j⦌)), 0 < j →
      z ∉ U.obj (op ⦋j⦌) → z ∈ V.degenerate j)
    {HV HU : FormalCoproduct.{w} X.Etale}
    (v : SimplicialHomFamily K V HV) (u : SimplicialHomFamily K U.toSSet HU)
    (hv : (simplicialHomFamilyFunctor K V).IsRepresentedBy v)
    (hu : (simplicialHomFamilyFunctor K U.toSSet).IsRepresentedBy u) :
    IsSemiRepresentableCovering (simplicialHomRestriction U v hu) := by
  obtain ⟨b, hpush⟩ := oneSimplexPushout U 0 x hx (by omega) hdegree hhigher
  obtain ⟨hΔ, hΔfinite, _, ⟨c, hc, hcrep⟩, _⟩ :=
    simplicial_hom_standard_simplex.{u, w, t} K 0
  let : (Δ[0] : SSet.{t}).Finite := hΔfinite
  have hempty : ∀ m : ℕ, IsEmpty ((SSet.boundary.{t} 0).toSSet.obj (op ⦋m⦌)) := by
    intro m
    rw [SSet.boundary_zero]
    exact ⟨fun s ↦ s.property⟩
  obtain ⟨hprod⟩ := simplicialHomObject_pushout_empty_isProduct hempty
    (fun m ↦ (hU m).1) (fun m ↦ (hU m).2)
    (fun m ↦ (hΔ m).1) (fun m ↦ (hΔ m).2)
    (fun m ↦ (hV m).1) (fun m ↦ (hV m).2)
    b (SSet.boundary 0).ι U.ι (SSet.yonedaEquiv.symm x) hpush
    u c v hu hcrep hv
    (simplicialHomRestriction U v hu) (v.val 0 x)
    (restriction_val U v hu)
    (by
      intro m s
      rw [hc]
      exact v.property m 0 (SSet.stdSimplex.objEquiv s) x)
  let ht : IsTerminal (semiRepresentableMatchingObject K 0) :=
    FormalCoproduct.isTerminalIncl (AlgebraicGeometry.Scheme.Etale.mk (𝟙 X))
      ((Over.mkIdTerminal (X := X)).isTerminalOfObj (AlgebraicGeometry.Scheme.Etale.forget X)
        (AlgebraicGeometry.Scheme.Etale.mk (𝟙 X)))
  exact covering_pullback (IsPullback.of_is_product' hprod ht) (hK 0)

/-- Restriction along the addition of one simplex is a covering of semi-representable
objects. Source: Stacks Project, Tag 01GM, Lemma `lemma-one-more-simplex`
(auxiliary; not a blueprint node).

Proof:
1. By lem-weil-pbc-simplicial-set-glue-simplex, the hypotheses exhibit `V` as the
pushout of `U` and `Δ[n]` along `∂Δ[n]`. At `n = 0` this is the coproduct with `Δ[0]`.
2. By lem-weil-pbc-simplicial-hom-object-standard-simplex, the simplex Hom object is
`K_n`, and for positive `n` the boundary Hom object is the matching object `M_n(K)`.
The universal families of def-weil-pbc-simplicial-hom-object identify these objects.
3. An isomorphism of formal coproducts has a bijective index map and isomorphisms on
components; it is thus a covering. By lem-weil-pbc-semi-representable-covering-permanence,
composing a covering with isomorphisms preserves coverings.
4. For `n > 0`, lem-weil-pbc-simplicial-hom-object-pushout turns the pushout into a
fibre square of Hom objects, whose top map is the restriction to `U`.
5. Under the identifications of step 2, the bottom map is the matching map `μ_n`:
their composites with each universal boundary component agree, hence they agree by
universality. It is a covering by def-weil-pbc-semi-representable-object and step 3.
6. Base change preserves coverings by lem-weil-pbc-semi-representable-covering-permanence.
The fibre product of lem-weil-pbc-semi-representable-finite-limits is isomorphic to the
Hom object in the square, and step 3 makes its projection to `Hom(U,K)_0` a covering.
7. For `n = 0`, lem-weil-pbc-simplicial-hom-object-pushout instead gives the product
`Hom(U,K)_0 × K_0`. The matching map `K_0 → {id_X}` is a covering by the hypercover
hypothesis. Regard this product as a fibre product over the terminal family, using
lem-weil-pbc-semi-representable-finite-limits; base change and step 3 give the result. -/
theorem isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex
    {X : Scheme.{u}} (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) (V : SSet.{t}) (U : V.Subcomplex)
    (hV : ∀ i : ℕ, Finite (V.obj (op ⦋i⦌)) ∧ Nonempty (V.obj (op ⦋i⦌)))
    (hU : ∀ i : ℕ, Finite (U.toSSet.obj (op ⦋i⦌)) ∧
      Nonempty (U.toSSet.obj (op ⦋i⦌)))
    [V.Finite] [U.toSSet.Finite]
    (n : ℕ) (x : V.obj (op ⦋n⦌)) (hx : x ∉ U.obj (op ⦋n⦌))
    (hlower : ∀ i : ℕ, i < n → U.obj (op ⦋i⦌) = Set.univ)
    (hdegree : (Set.univ : Set (V.obj (op ⦋n⦌))) = U.obj (op ⦋n⦌) ∪ {x})
    (hhigher : ∀ (j : ℕ) (z : V.obj (op ⦋j⦌)),
      n < j → z ∉ U.obj (op ⦋j⦌) → z ∈ V.degenerate j)
    {HV HU : FormalCoproduct.{w} X.Etale}
    (v : SimplicialHomFamily K V HV) (u : SimplicialHomFamily K U.toSSet HU)
    (hv : (simplicialHomFamilyFunctor K V).IsRepresentedBy v)
    (hu : (simplicialHomFamilyFunctor K U.toSSet).IsRepresentedBy u) :
    IsSemiRepresentableCovering (simplicialHomRestriction U v hu) := by
  cases n with
  | zero => exact zero_case K hK V U hV hU x hx hdegree hhigher v u hv hu
  | succ n => exact positive_case K hK V U hV hU n x hx hlower hdegree hhigher v u hv hu

end AlgebraicGeometry.Scheme
