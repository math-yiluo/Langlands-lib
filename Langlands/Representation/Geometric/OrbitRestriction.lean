import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.Topology.LocallyClosed

/-! Actual restriction to a coset orbit and the adjacent support-step kernel. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV uW

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]

/-- Restrict a smooth covariant function along `q ↦ w⁻¹ q`.
The ambient uniform stabilizer pulls back to an open subgroup of `Q`. -/
def smoothOrbitRestriction (P Q : Subgroup G) (w : G)
    (σ : Representation R P V) (f : Induction.SmoothFunctions P σ) :
    Induction.SmoothFunctions (orbitStabilizer P Q w)
      (σ.comp (stabilizerToInducing P Q w)) := by
  refine ⟨⟨(fun q => Induction.eval P σ f (w⁻¹ * (q : G))), ?_⟩, ?_⟩
  · intro q x
    have h := Induction.eval_covariant P σ f (stabilizerToInducing P Q w q)
      (w⁻¹ * (x : G))
    simpa only [stabilizerToInducing_apply, MonoidHom.comp_apply,
      Subgroup.coe_mul, Subgroup.subtype_apply, mul_assoc, mul_inv_cancel_left] using h
  · obtain ⟨K, hK⟩ := f.property
    refine ⟨K.comap Q.subtype continuous_subtype_val, ?_⟩
    intro k
    apply Subtype.ext
    funext x
    have h := congrArg (fun F : Induction.EquivariantFunctions P σ =>
      F.val (w⁻¹ * (x : G))) (hK ⟨((k : Q) : G), k.property⟩)
    change Induction.eval P σ f ((w⁻¹ * (x : G)) * ((k : Q) : G)) =
      Induction.eval P σ f (w⁻¹ * (x : G)) at h
    change Induction.eval P σ f (w⁻¹ * ((x : G) * ((k : Q) : G))) =
      Induction.eval P σ f (w⁻¹ * (x : G))
    simpa only [mul_assoc] using h

omit [IsTopologicalGroup G] in
@[simp]
theorem smoothOrbitRestriction_eval (P Q : Subgroup G) (w : G)
    (σ : Representation R P V) (f : Induction.SmoothFunctions P σ) (q : Q) :
    Induction.eval (orbitStabilizer P Q w) (σ.comp (stabilizerToInducing P Q w))
      (smoothOrbitRestriction P Q w σ f) q =
    Induction.eval P σ f (w⁻¹ * (q : G)) := rfl

/-- The actual restriction is a linear `Q`-intertwiner. -/
def smoothOrbitRestrictionMap (P Q : Subgroup G) (w : G)
    (σ : Representation R P V) :
    Representation.IntertwiningMap ((Induction.smoothInduced P σ).comp Q.subtype)
      (Induction.smoothInduced (orbitStabilizer P Q w)
        (σ.comp (stabilizerToInducing P Q w))) where
  toLinearMap :=
    { toFun := smoothOrbitRestriction P Q w σ
      map_add' := by intro f g; rfl
      map_smul' := by intro a f; rfl }
  isIntertwining' q := by
    ext f x
    change Induction.eval P σ f ((w⁻¹ * (x : G)) * (q : G)) =
      Induction.eval P σ f (w⁻¹ * ((x : G) * (q : G)))
    rw [mul_assoc]

/-- Restriction commutes pointwise with every inducing intertwiner. -/
theorem smoothOrbitRestriction_natural (P Q : Subgroup G) (w : G)
    {σ : Representation R P V} {τ : Representation R P W}
    (T : σ.IntertwiningMap τ) (f : Induction.SmoothFunctions P σ) (q : Q) :
    Induction.eval (orbitStabilizer P Q w) (τ.comp (stabilizerToInducing P Q w))
      (smoothOrbitRestriction P Q w τ (Induction.smoothInducedMap P T f)) q =
    T (Induction.eval (orbitStabilizer P Q w) (σ.comp (stabilizerToInducing P Q w))
      (smoothOrbitRestriction P Q w σ f) q) := rfl

omit [IsTopologicalGroup G] in
/-- Zero values of a covariant function are constant on its left cosets. -/
theorem eval_eq_zero_of_quotientMap_eq (P : Subgroup G) (σ : Representation R P V)
    (f : Induction.SmoothFunctions P σ) {x y : G}
    (hxy : Induction.quotientMap P x = Induction.quotientMap P y)
    (hy : Induction.eval P σ f y = 0) : Induction.eval P σ f x = 0 := by
  by_contra hx
  have hs : Induction.quotientMap P y ∈
      Induction.quotientSupport P (Induction.eval P σ f) :=
    hxy ▸ ⟨x, hx, rfl⟩
  have hy' : y ∈ Function.support (Induction.eval P σ f) := by
    rw [← Induction.quotientMap_preimage_quotientSupport P σ f]
    exact hs
  exact hy' hy

namespace OrderedDoubleCosets

variable {P Q : Subgroup G} {n : ℕ}

omit [IsTopologicalGroup G] in
/-- The new orbit is exactly the difference of consecutive open initial unions. -/
theorem initialOrbits_succ_diff (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    s.initialOrbits i.succ \ s.initialOrbits i.castSucc =
      cosetOrbit P Q (s.representative i) := by
  ext x
  constructor
  · rintro ⟨⟨j, hj, hx⟩, hprev⟩
    have hji : j = i := by
      apply Fin.ext
      have hn : ¬ j.val < i.val := fun h => hprev ⟨j, h, hx⟩
      have hj' : j.val < i.val + 1 := hj
      omega
    simpa only [hji] using hx
  · intro hx
    refine ⟨⟨i, Nat.lt_succ_self _, hx⟩, ?_⟩
    rintro ⟨j, hj, hxj⟩
    have hji : j ≠ i := fun h => by subst j; exact (Nat.lt_irrefl i.val) hj
    exact Set.disjoint_left.mp (s.disjoint hji) hxj hx

omit [IsTopologicalGroup G] in
/-- The new orbit is contained in the next support open set. -/
theorem cosetOrbit_subset_initialOrbits_succ (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    cosetOrbit P Q (s.representative i) ⊆ s.initialOrbits i.succ :=
  fun _ hx => ⟨i, Nat.lt_succ_self _, hx⟩

omit [IsTopologicalGroup G] in
/-- Each specified orbit is locally closed, without any extra ordering choice. -/
theorem cosetOrbit_isLocallyClosed (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    IsLocallyClosed (cosetOrbit P Q (s.representative i)) := by
  rw [← s.initialOrbits_succ_diff i]
  exact ⟨_, _, s.initial_open i.succ, (s.initial_open i.castSucc).isClosed_compl, rfl⟩

omit [IsTopologicalGroup G] in
/-- The orbit is closed as a subspace of the next initial union. -/
theorem cosetOrbit_isClosed_in_next (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    IsClosed ((fun x : s.initialOrbits i.succ =>
      (x : Induction.LeftQuotient P)) ⁻¹' cosetOrbit P Q (s.representative i)) := by
  have heq : ((fun x : s.initialOrbits i.succ => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q (s.representative i)) =
      ((fun x : s.initialOrbits i.succ => (x : Induction.LeftQuotient P)) ⁻¹'
        s.initialOrbits i.castSucc)ᶜ := by
    rw [← s.initialOrbits_succ_diff i]
    ext x
    exact and_iff_right x.property
  rw [heq]
  exact ((s.initial_open i.castSucc).preimage continuous_subtype_val).isClosed_compl

omit [IsTopologicalGroup G] in
/-- On the actual upper support step, restriction vanishes precisely when the
function already belongs to the preceding support step. -/
theorem orbitRestriction_zero_iff_lowerSupport (s : OrderedDoubleCosets P Q n)
    (i : Fin n) (σ : Representation R P V) (f : Induction.SmoothFunctions P σ)
    (hf : ∀ x : G, Induction.eval P σ f x ≠ 0 →
      Induction.quotientMap P x ∈ s.initialOrbits i.succ) :
    (∀ q : Q, Induction.eval P σ f ((s.representative i)⁻¹ * (q : G)) = 0) ↔
      ∀ x : G, Induction.eval P σ f x ≠ 0 →
        Induction.quotientMap P x ∈ s.initialOrbits i.castSucc := by
  constructor
  · intro hzero x hx
    by_contra hprev
    have horb : Induction.quotientMap P x ∈ cosetOrbit P Q (s.representative i) := by
      rw [← s.initialOrbits_succ_diff i]
      exact ⟨hf x hx, hprev⟩
    obtain ⟨q, hq⟩ := horb
    exact hx (eval_eq_zero_of_quotientMap_eq P σ f hq.symm (hzero q))
  · intro hprev q
    by_contra hq
    have horb : Induction.quotientMap P ((s.representative i)⁻¹ * (q : G)) ∈
        cosetOrbit P Q (s.representative i) := ⟨q, rfl⟩
    rw [← s.initialOrbits_succ_diff i] at horb
    exact horb.2 (hprev _ hq)

end OrderedDoubleCosets
end Langlands.Geometric
