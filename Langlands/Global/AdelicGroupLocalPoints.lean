import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.Adelic
import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.CoordinateCompactAssembly

/-! # Actual adelic group points at every place -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Filter
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]

/-- All places of the number field: archimedean places on the left and finite
places on the right. -/
abbrev Place := InfinitePlace F ⊕ FinitePlace F

/-- The actual completion at a place, as a commutative algebra over the field. -/
def placeCompletion : Place F → CommAlgCat.{u} (CommRingCat.of F)
  | .inl w => CommAlgCat.of F w.Completion
  | .inr v => CommAlgCat.of F (FiniteCompletion F v)

namespace placeCompletion

instance topologicalSpace : (i : Place F) → TopologicalSpace (placeCompletion F i)
  | .inl w => inferInstanceAs (TopologicalSpace w.Completion)
  | .inr v => inferInstanceAs (TopologicalSpace (v.adicCompletion F))

instance isTopologicalRing : (i : Place F) → IsTopologicalRing (placeCompletion F i)
  | .inl w => inferInstanceAs (IsTopologicalRing w.Completion)
  | .inr v => inferInstanceAs (IsTopologicalRing (v.adicCompletion F))

instance t2Space : (i : Place F) → T2Space (placeCompletion F i)
  | .inl w => inferInstanceAs (T2Space w.Completion)
  | .inr v => inferInstanceAs (T2Space (v.adicCompletion F))

end placeCompletion

/-- The coordinate projection from the actual adele ring to a completion. -/
def adeleProjection : (i : Place F) →
    AdeleRing (𝓞 F) F →ₐ[F] placeCompletion F i
  | .inl w =>
    { toFun a := a.1 w
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }
  | .inr v =>
    { toFun a := a.2 v
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }

@[simp] theorem adeleProjection_inl (w : InfinitePlace F) (a : AdeleRing (𝓞 F) F) :
    adeleProjection F (.inl w) a = a.1 w := rfl

@[simp] theorem adeleProjection_inr (v : FinitePlace F) (a : AdeleRing (𝓞 F) F) :
    adeleProjection F (.inr v) a = a.2 v := rfl

theorem continuous_adeleProjection : (i : Place F) → Continuous (adeleProjection F i)
  | .inl w => (continuous_apply w).comp continuous_fst
  | .inr v => (RestrictedProduct.continuous_eval v).comp continuous_snd

variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Actual group-scheme points over the completion at a place. -/
abbrev PlaceGroupPoints (i : Place F) :=
  G.affinePoints (placeCompletion F i)

namespace PlaceGroupPoints

/-- The existing regular-function evaluation topology at a completion. -/
instance topologicalSpace (i : Place F) : TopologicalSpace (PlaceGroupPoints F G i) :=
  G.affinePointsTopologicalSpace (placeCompletion F i)

instance isTopologicalGroup [IsAffine G.X.left] (i : Place F) :
    IsTopologicalGroup (PlaceGroupPoints F G i) :=
  G.affinePointsIsTopologicalGroup (placeCompletion F i)

instance t2Space [IsAffine G.X.left] (i : Place F) : T2Space (PlaceGroupPoints F G i) :=
  G.affinePointsT2Space (placeCompletion F i)

end PlaceGroupPoints

/-- Actual group-scheme points over the completion at a finite place. -/
abbrev FinitePlaceGroupPoints (v : FinitePlace F) :=
  G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))

namespace FinitePlaceGroupPoints

/-- The existing regular-function evaluation topology at a finite completion. -/
instance topologicalSpace (v : FinitePlace F) :
    TopologicalSpace (FinitePlaceGroupPoints F G v) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F (FiniteCompletion F v))

end FinitePlaceGroupPoints

namespace AdelicGroupPoints

/-- Projection of an actual adelic point to its point over one completion. -/
def atPlace (i : Place F) : AdelicGroupPoints F G →ₜ* PlaceGroupPoints F G i where
  toMonoidHom := G.affinePointMap (CommAlgCat.ofHom (adeleProjection F i))
  continuous_toFun := G.continuous_affinePointMap _ (continuous_adeleProjection F i)

@[simp] theorem atPlace_evaluation (i : Place F) (x : AdelicGroupPoints F G)
    (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (placeCompletion F i) (atPlace F G i x) a =
      adeleProjection F i
        (G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x a) :=
  G.affinePointEvaluation_map _ x a

/-- Actual adelic points of an affine group scheme are determined by their local
points. -/
theorem ext_atPlace [IsAffine G.X.left] {x y : AdelicGroupPoints F G}
    (h : ∀ i, atPlace F G i x = atPlace F G i y) : x = y := by
  apply G.affinePointEvaluation_injective
  funext a
  have h' (i : Place F) := congrArg
    (fun z => G.affinePointEvaluation (placeCompletion F i) z a) (h i)
  simp only [atPlace_evaluation] at h'
  refine Prod.ext (funext fun w => h' (.inl w)) (FiniteAdeleRing.ext _ fun v => h' (.inr v))

/-- Every regular-function value of an actual adelic point is integral at almost
every finite place. -/
theorem eventually_atPlace_evaluation_mem (x : AdelicGroupPoints F G)
    (a : Γ(G.X.left, ⊤)) :
    ∀ᶠ v : FinitePlace F in cofinite,
      G.affinePointEvaluation (placeCompletion F (.inr v)) (atPlace F G (.inr v) x) a ∈
        v.adicCompletionIntegers F := by
  simp only [atPlace_evaluation, adeleProjection_inr]
  exact (G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x a).2.2

/-- Projection of an actual adelic point to its point over a finite completion. -/
def atFinitePlace (v : FinitePlace F) :
    AdelicGroupPoints F G →ₜ* FinitePlaceGroupPoints F G v :=
  atPlace F G (.inr v)

/-- Projection of an actual adelic point to its point over an archimedean completion. -/
def atInfinitePlace (w : InfinitePlace F) :
    AdelicGroupPoints F G →ₜ* InfinitePlaceGroupPoints F G w :=
  atPlace F G (.inl w)

@[simp] theorem atFinitePlace_evaluation (v : FinitePlace F) (x : AdelicGroupPoints F G)
    (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) (atFinitePlace F G v x) a =
      (G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x a).2 v :=
  atPlace_evaluation F G (.inr v) x a

@[simp] theorem atInfinitePlace_evaluation (w : InfinitePlace F) (x : AdelicGroupPoints F G)
    (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F w.Completion) (atInfinitePlace F G w x) a =
      (G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x a).1 w :=
  atPlace_evaluation F G (.inl w) x a

/-- Local projections commute with the adelic map induced by a group-scheme
homomorphism. -/
theorem atPlace_map {H : GroupScheme (Spec (CommRingCat.of F))} (f : G ⟶ H)
    (i : Place F) (x : AdelicGroupPoints F G) :
    atPlace F H i (map F G H f x) =
      G.affinePointsTarget f (placeCompletion F i) (atPlace F G i x) :=
  DFunLike.congr_fun (G.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (adeleProjection F i))) x

/-- A property holding at almost every finite place holds at almost every place. -/
theorem eventually_place_of_finite {p : Place F → Prop}
    (h : ∀ᶠ v : FinitePlace F in cofinite, p (.inr v)) : ∀ᶠ i : Place F in cofinite, p i := by
  rw [eventually_cofinite] at h ⊢
  have hfin : {i : Place F | ¬ p i} ⊆
      Set.range (Sum.inl : InfinitePlace F → Place F) ∪ Sum.inr '' {v | ¬ p (.inr v)} := by
    rintro (w | v) hi
    · exact Or.inl ⟨w, rfl⟩
    · exact Or.inr ⟨v, hi, rfl⟩
  exact ((Set.finite_range _).union (h.image _)).subset hfin

section Glue

open Langlands.AlgebraicGeometry.PointTopology

variable [IsAffine G.X.left]

/-- Local coordinate-algebra homomorphisms whose finite-place values are integral
almost everywhere assemble into one homomorphism to the adele ring. -/
def glueAlgHom (φ : ∀ i : Place F, AffineCoordinateRing F G.X →ₐ[F] placeCompletion F i)
    (hφ : ∀ a, ∀ᶠ v : FinitePlace F in cofinite, φ (.inr v) a ∈ v.adicCompletionIntegers F) :
    AffineCoordinateRing F G.X →ₐ[F] AdeleRing (𝓞 F) F where
  toFun a := (fun w => φ (.inl w) a, ⟨fun v => φ (.inr v) a, hφ a⟩)
  map_one' := Prod.ext (funext fun w => map_one (φ (.inl w)))
    (FiniteAdeleRing.ext _ fun v => map_one (φ (.inr v)))
  map_mul' a b := Prod.ext (funext fun w => map_mul (φ (.inl w)) a b)
    (FiniteAdeleRing.ext _ fun v => map_mul (φ (.inr v)) a b)
  map_zero' := Prod.ext (funext fun w => map_zero (φ (.inl w)))
    (FiniteAdeleRing.ext _ fun v => map_zero (φ (.inr v)))
  map_add' a b := Prod.ext (funext fun w => map_add (φ (.inl w)) a b)
    (FiniteAdeleRing.ext _ fun v => map_add (φ (.inr v)) a b)
  commutes' c := Prod.ext (funext fun w => (φ (.inl w)).commutes c)
    (FiniteAdeleRing.ext _ fun v => (φ (.inr v)).commutes c)

/-- Every regular-function value of a local point family is integral at almost
every finite place. -/
def IsAdelicFamily (x : ∀ i, PlaceGroupPoints F G i) : Prop :=
  ∀ a : Γ(G.X.left, ⊤), ∀ᶠ v : FinitePlace F in cofinite,
    G.affinePointEvaluation (placeCompletion F (.inr v)) (x (.inr v)) a ∈
      v.adicCompletionIntegers F

/-- The actual adelic point with prescribed local points, for a family whose
regular-function values are integral at almost every finite place. -/
def glue (x : ∀ i, PlaceGroupPoints F G i) (hx : IsAdelicFamily F G x) :
    AdelicGroupPoints F G :=
  (affineSchemePointEquiv F G.X (AdeleRing (𝓞 F) F)).symm
    (AlgPoint.ofAlgHom (glueAlgHom F G
      (fun i => (affineSchemePointEquiv F G.X (placeCompletion F i) (x i)).toAlgHom)
      (fun a => (hx a).mono fun v hv => by
        rwa [AlgPoint.toAlgHom_apply, G.affineSchemePointEquiv_evaluation])))

theorem glue_evaluation (x : ∀ i, PlaceGroupPoints F G i) (hx : IsAdelicFamily F G x)
    (a : Γ(G.X.left, ⊤)) (i : Place F) :
    adeleProjection F i
        (G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (glue F G x hx) a) =
      G.affinePointEvaluation (placeCompletion F i) (x i) a := by
  rw [← G.affineSchemePointEquiv_evaluation, ← G.affineSchemePointEquiv_evaluation]
  change adeleProjection F i ((affineSchemePointEquiv F G.X (AdeleRing (𝓞 F) F))
    ((affineSchemePointEquiv F G.X (AdeleRing (𝓞 F) F)).symm _) a) = _
  rw [Equiv.apply_symm_apply]
  cases i <;> rfl

@[simp] theorem atPlace_glue (x : ∀ i, PlaceGroupPoints F G i) (hx : IsAdelicFamily F G x)
    (i : Place F) : atPlace F G i (glue F G x hx) = x i := by
  apply G.affinePointEvaluation_injective (placeCompletion F i)
  funext a
  change G.affinePointEvaluation (placeCompletion F i) (atPlace F G i (glue F G x hx)) a = _
  rw [atPlace_evaluation, glue_evaluation]

omit [IsAffine G.X.left] in
/-- A local family agreeing with the local points of one adelic point at almost
every finite place has almost-everywhere integral values. -/
theorem isAdelicFamily_of_eventually_eq (x : ∀ i, PlaceGroupPoints F G i)
    (y : AdelicGroupPoints F G)
    (h : ∀ᶠ v : FinitePlace F in cofinite, x (.inr v) = atPlace F G (.inr v) y) :
    IsAdelicFamily F G x := fun a =>
  (h.and (eventually_atPlace_evaluation_mem F G y a)).mono fun _ hv => hv.1 ▸ hv.2

/-- Local families equal to the identity at almost every place come from actual
adelic points. -/
theorem exists_atPlace_eq_of_eventually_one (q : ∀ i, PlaceGroupPoints F G i)
    (hq : ∀ᶠ i in cofinite, q i = 1) :
    ∃ b : AdelicGroupPoints F G, ∀ i, atPlace F G i b = q i := by
  have hfin : ∀ᶠ v : FinitePlace F in cofinite, q (.inr v) = atPlace F G (.inr v) 1 :=
    (Sum.inr_injective.tendsto_cofinite.eventually hq).mono fun _ hv => by rw [hv, map_one]
  exact ⟨glue F G q (isAdelicFamily_of_eventually_eq F G q 1 hfin), atPlace_glue F G q _⟩

end Glue

section CompactLift

variable [IsAffine G.X.left]

/-- Uniform almost-everywhere integrality of all regular functions on specified
local subgroups: for each regular function, at almost every finite place, its
values on the whole local subgroup are integral. -/
def IsUniformlyIntegral (K : ∀ i, Subgroup (PlaceGroupPoints F G i)) : Prop :=
  ∀ a : Γ(G.X.left, ⊤), ∀ᶠ v : FinitePlace F in cofinite, ∀ k ∈ K (.inr v),
    G.affinePointEvaluation (placeCompletion F (.inr v)) k a ∈ v.adicCompletionIntegers F

variable {F G}

omit [IsAffine G.X.left] in
theorem IsUniformlyIntegral.isAdelicFamily {K : ∀ i, Subgroup (PlaceGroupPoints F G i)}
    (hK : IsUniformlyIntegral F G K) (k : ∀ i, K i) :
    IsAdelicFamily F G (fun i => k i) := fun a =>
  (hK a).mono fun v hv => hv _ (k (.inr v)).property

omit [IsAffine G.X.left] in
/-- Uniform integrality is unchanged by replacing finitely many local subgroups. -/
theorem IsUniformlyIntegral.of_eventuallyEq {K K' : ∀ i, Subgroup (PlaceGroupPoints F G i)}
    (hK : IsUniformlyIntegral F G K) (h : ∀ᶠ i in cofinite, K' i = K i) :
    IsUniformlyIntegral F G K' := fun a =>
  ((Sum.inr_injective.tendsto_cofinite.eventually h).and (hK a)).mono fun _ hv => by
    rw [hv.1]
    exact hv.2

/-- A uniformly integral family of local subgroups has a continuous adelic lift
of its full product. -/
def IsUniformlyIntegral.compactProductLift {K : ∀ i, Subgroup (PlaceGroupPoints F G i)}
    (hK : IsUniformlyIntegral F G K) :
    CoordinateCompactAssembly.CompactProductLift
      (fun i => (atPlace F G i : AdelicGroupPoints F G →* PlaceGroupPoints F G i)) K where
  lift k := glue F G (fun i => k i) (hK.isAdelicFamily k)
  continuous_lift := by
    refine (G.continuous_affinePoints_iff _ _).mpr fun a => ?_
    set g : (∀ i, K i) → AdeleRing (𝓞 F) F := fun k =>
      G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F))
        (glue F G (fun i => k i) (hK.isAdelicFamily k)) a with hg
    have hloc (i : Place F) :
        Continuous fun k : ∀ i, K i => adeleProjection F i (g k) := by
      have hgi : (fun k : ∀ i, K i => adeleProjection F i (g k)) = fun k =>
          G.affinePointEvaluation (placeCompletion F i) (k i : PlaceGroupPoints F G i) a :=
        funext fun k => glue_evaluation F G (fun i => k i) (hK.isAdelicFamily k) a i
      rw [hgi]
      exact (G.continuous_affinePointEvaluation (placeCompletion F i) a).comp
        (continuous_subtype_val.comp (continuous_apply i))
    have hfst : Continuous fun k => (g k).1 :=
      continuous_pi fun w => hloc (.inl w)
    obtain ⟨S, hS, hSK⟩ : ∃ S : Set (FinitePlace F), cofinite ≤ 𝓟 S ∧
        ∀ v ∈ S, ∀ k ∈ K (.inr v),
          G.affinePointEvaluation (placeCompletion F (.inr v)) k a ∈
            v.adicCompletionIntegers F :=
      ⟨_, le_principal_iff.mpr (hK a), fun _ hv => hv⟩
    let h : (∀ i, K i) →
        Πʳ v : FinitePlace F, [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 S] :=
      fun k => ⟨fun v => (g k).2 v, eventually_principal.mpr fun v hv => by
        have := glue_evaluation F G (fun i => k i) (hK.isAdelicFamily k) a (.inr v)
        rw [adeleProjection_inr] at this
        change (g k).2 v ∈ _
        rw [hg, this]
        exact hSK v hv _ (k (.inr v)).property⟩
    have hh : Continuous h :=
      RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun v => hloc (.inr v)
    have hsnd : Continuous fun k => (g k).2 :=
      (RestrictedProduct.continuous_inclusion hS).comp hh
    exact hfst.prodMk hsnd
  eval_lift k i := atPlace_glue F G (fun i => k i) _ i

end CompactLift

section FiniteAdelic

variable [IsAffine G.X.left]

/-- The point of an actual adelic point at a finite place factors through its
finite-adelic point and the restricted-product coordinate evaluation. -/
theorem atFinitePlace_eq_finite (v : FinitePlace F) (x : AdelicGroupPoints F G) :
    atFinitePlace F G v x =
      G.affinePointMap
        (CommAlgCat.ofHom
          ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
             commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v))
        (finite F G x) := by
  apply G.affinePointEvaluation_injective
  funext a
  refine (atFinitePlace_evaluation F G v x a).trans ?_
  refine Eq.trans ?_ (G.affinePointEvaluation_map _ _ a).symm
  exact congrArg (fun b : FiniteAdeleRing (𝓞 F) F => b v)
    (G.affinePointEvaluation_map (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F)
      (FiniteAdeleRing (𝓞 F) F))) x a).symm

/-- If every finite-adelic point lies in the finite-place members of a local
family at almost every finite place, then every actual adelic point lies in the
family at almost every place. -/
theorem eventually_atPlace_mem_of_finite {K : ∀ i, Subgroup (PlaceGroupPoints F G i)}
    (h : ∀ x : FiniteAdelicGroupPoints F G, ∀ᶠ v : FinitePlace F in cofinite,
      G.affinePointMap
        (CommAlgCat.ofHom
          ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
             commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v)) x ∈ K (.inr v))
    (x : AdelicGroupPoints F G) : ∀ᶠ i in cofinite, atPlace F G i x ∈ K i :=
  eventually_place_of_finite F ((h (finite F G x)).mono fun v hv => by
    rw [← atFinitePlace_eq_finite] at hv
    exact hv)

end FiniteAdelic

end AdelicGroupPoints

end Langlands.Global
