import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.Strata
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement

/-!
# The uniform Lang–Weil estimate for a separated algebraic space over a scheme

Let `X` be a separated algebraic space with an affine étale chart `a : U → X` (a `SepChart`),
`M` a quasi-compact scheme locally of finite type over `ℤ`, `g : X → M` a morphism and
`π : U → M` a surjective smooth map of relative dimension `d` with `a ≫ g = π`, such that the
points of every fibre of `g` over a field point of `M` form a connected space. Assuming the
uniform Lang–Weil estimate for families of schemes and the uniform upper bound for point counts
in families, the number of `κ`-points of `X` over a `κ`-point of `M` differs from `(#κ) ^ d` by
at most `C (#κ) ^ (d - 1/2)`, with one constant `C`.

The points of `M` are stratified by the largest `k` below the tuple-length bound for which they
lie in the (open) image of `p_k : V_k → M`. The stratum of degree `k` is a locally closed
subscheme `S_k` of `M`, over which the base change of `p_k` is a family with geometrically
irreducible fibres of pure dimension `d`. Over a `κ`-point `m` of `M` in the stratum of degree
`k`, the `κ`-points of `X` are the points of the exact-degree schemes `D_n` over `m` for
`n ≤ k`; those of `D_k` are the points of `V_k` over `m`, counted by the Lang–Weil estimate for
the family over `S_k`, and those of `D_n` for `n < k` lie in fibres of dimension less than `d`,
bounded by the uniform upper bound.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry (EtaleEquivalenceRelation)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

set_option backward.isDefEq.respectTransparency false

/-- A scheme locally of finite type over the integers is locally Noetherian. -/
theorem isLocallyNoetherian_of_locallyOfFiniteType (M : Scheme.{u})
    [LocallyOfFiniteType (specULiftZIsTerminal.from M)] : IsLocallyNoetherian M := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from M)

/-- An element of `WithBot ℕ∞` below `0` is `⊥`. -/
theorem eq_bot_of_lt_zero {x : WithBot ℕ∞} (h : x < ((0 : ℕ) : WithBot ℕ∞)) : x = ⊥ := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe a =>
    exfalso
    have h' : a < 0 := by exact_mod_cast h
    simp at h'

/-- An element of `WithBot ℕ∞` below a natural number `d` is at most `d - 1`. -/
theorem le_coe_pred_of_lt {x : WithBot ℕ∞} {d : ℕ} (h : x < (d : WithBot ℕ∞)) :
    x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) < d := by exact_mod_cast h
      exact absurd h' (not_lt.mpr le_top)
    | coe a =>
      have h' : a < d := by exact_mod_cast h
      have h'' : a ≤ d - 1 := by omega
      have h3 : (a : ℕ∞) ≤ ((d - 1 : ℕ) : ℕ∞) := by exact_mod_cast h''
      exact WithBot.coe_le_coe.mpr h3

/-- A topological space of dimension below `0` is empty. -/
theorem isEmpty_of_topologicalKrullDim_lt_zero {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T < ((0 : ℕ) : WithBot ℕ∞)) : IsEmpty T := by
  have hbot := eq_bot_of_lt_zero h
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff] at hbot
  exact ⟨fun t => hbot.elim ⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

namespace SepChart

variable {c : SepChart.{u}} {M : Scheme.{u}}
  {g : c.X.presheaf ⟶ (schemeYoneda S0).obj (toOver M)}

/-- The image of `p_n` is open: it is the image under the smooth map `π` of the image of the
étale first coordinate of distinct tuples. -/
theorem isOpen_range_p (π : c.U.left ⟶ M) [Smooth π]
    (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π)) (n : ℕ) :
    IsOpen (Set.range (c.p g n)) := by
  have h := symmetricMap_p π ha n
  have hrange : Set.range (c.p g n) = π '' Set.range (c.E.tupleDistinctProjection n 0) := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := (c.E.tupleSymmetricMap n).surjective v
      have := congrArg (fun φ => φ w) h
      simp only [Scheme.Hom.comp_apply] at this
      exact ⟨_, ⟨w, rfl⟩, this.symm⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      have := congrArg (fun φ => φ w) h
      simp only [Scheme.Hom.comp_apply] at this
      exact ⟨_, this⟩
  rw [hrange]
  exact π.isOpenMap _ (c.E.tupleDistinctProjection n 0).isOpenMap.isOpen_range

/-- Every point of `M` lies in the image of some `p_n` with `n` below the tuple-length bound,
when `π` is surjective. -/
theorem exists_mem_range_p (π : c.U.left ⟶ M) (hπ : Function.Surjective π)
    (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π)) (y : M) :
    ∃ n < c.N, y ∈ Set.range (c.p g n) := by
  obtain ⟨x, rfl⟩ := hπ y
  let K := c.U.left.residueField x
  let Ω := AlgebraicClosure K
  let ξ : Spec (CommRingCat.of Ω) ⟶ c.U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ c.U.left.fromSpecResidueField x
  have hξ : ξ (IsLocalRing.closedPoint Ω) = x := c.U.left.fromSpecResidueField_apply x _
  obtain ⟨n, hn, v, -, hv⟩ := c.exists_ptE_eq (c.ptA ξ)
  have hM : v ≫ c.p g n = ξ ≫ π := by
    apply eq_of_map_toOverHom_eq
    rw [← ptE_g, hv, ptA, Category.assoc, ha, ← Functor.map_comp]
    rfl
  refine ⟨n, hn, v (IsLocalRing.closedPoint Ω), ?_⟩
  have := congrArg (fun φ => φ (IsLocalRing.closedPoint Ω)) hM
  simp only [Scheme.Hom.comp_apply] at this
  rw [this, hξ]

/-- Every point of `M` lies in a stratum of degree below the tuple-length bound, when `π` is
surjective. -/
theorem exists_inStratum (π : c.U.left ⟶ M) (hπ : Function.Surjective π)
    (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π)) (y : M) :
    ∃ k < c.N, c.InStratum g k y := by
  classical
  let S := (Finset.range c.N).filter (fun n => y ∈ Set.range (c.p g n))
  obtain ⟨n, hn, hy⟩ := exists_mem_range_p π hπ ha y
  have hS : S.Nonempty := ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hy⟩⟩
  have hk := Finset.max'_mem S hS
  rw [Finset.mem_filter, Finset.mem_range] at hk
  refine ⟨S.max' hS, hk.1, hk.2, fun m hkm hmN hym => ?_⟩
  have := S.le_max' m (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmN, hym⟩)
  omega

variable (c g) (hopen : ∀ n, IsOpen (Set.range (c.p g n)))

/-- The closed set of points of `M` in no image of `p_n` for `k < n` below the tuple-length
bound. -/
def stratumClosed (k : ℕ) : Closeds M :=
  ⟨⋂ n ∈ {n | k < n ∧ n < c.N}, (Set.range (c.p g n))ᶜ,
    isClosed_biInter fun n _ => (hopen n).isClosed_compl⟩

theorem mem_stratumClosed {k : ℕ} {y : M} :
    y ∈ stratumClosed c g hopen k ↔ ∀ n, k < n → n < c.N → y ∉ Set.range (c.p g n) := by
  change y ∈ ⋂ n ∈ {n | k < n ∧ n < c.N}, (Set.range (c.p g n))ᶜ ↔ _
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff, and_imp]

/-- The reduced closed subscheme on `stratumClosed k`. -/
abbrev stratumZ (k : ℕ) : Scheme.IdealSheafData M :=
  Scheme.IdealSheafData.vanishingIdeal (stratumClosed c g hopen k)

/-- The open subset of the reduced closed subscheme on `stratumClosed k` lying over the image of
`p_k`. -/
def stratumOpen (k : ℕ) : (stratumZ c g hopen k).subscheme.Opens :=
  (stratumZ c g hopen k).subschemeι ⁻¹ᵁ ⟨Set.range (c.p g k), hopen k⟩

/-- The stratum of degree `k`, a locally closed subscheme of `M`. -/
abbrev stratum (k : ℕ) : Scheme.{u} := (stratumOpen c g hopen k).toScheme

/-- The immersion of the stratum of degree `k` into `M`. -/
def stratumι (k : ℕ) : stratum c g hopen k ⟶ M :=
  (stratumOpen c g hopen k).ι ≫ (stratumZ c g hopen k).subschemeι

instance (k : ℕ) : IsPreimmersion (stratumι c g hopen k) := by
  unfold stratumι; infer_instance

instance (k : ℕ) : LocallyOfFiniteType (stratumι c g hopen k) := by
  unfold stratumι; infer_instance

variable {c g hopen}

/-- The points of the stratum of degree `k` map into the stratum of degree `k`. -/
theorem inStratum_stratumι {k : ℕ} (x : stratum c g hopen k) :
    c.InStratum g k (stratumι c g hopen k x) := by
  refine ⟨?_, (mem_stratumClosed c g hopen).mp ?_⟩
  · have hx : (stratumOpen c g hopen k).ι x ∈ stratumOpen c g hopen k := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact hx
  · have hx : stratumι c g hopen k x ∈ Set.range (stratumZ c g hopen k).subschemeι :=
      ⟨_, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx

/-- A field point of `M` in the stratum of degree `k` factors through the stratum. -/
theorem exists_lift_stratumι {k : ℕ} {κ : Type u} [Field κ]
    (m : Spec (CommRingCat.of κ) ⟶ M) (hm : c.InStratum g k (m (IsLocalRing.closedPoint κ))) :
    ∃ m' : Spec (CommRingCat.of κ) ⟶ stratum c g hopen k, m' ≫ stratumι c g hopen k = m := by
  have hker : (stratumZ c g hopen k).subschemeι.ker ≤ m.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    refine (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).2 m ?_
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    subst hx
    exact (mem_stratumClosed c g hopen).mpr hm.2
  let mZ := IsClosedImmersion.lift _ m hker
  have hmZ : mZ ≫ (stratumZ c g hopen k).subschemeι = m := IsClosedImmersion.lift_fac _ _ _
  have hrange : Set.range mZ ⊆ Set.range (stratumOpen c g hopen k).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    subst hx
    show (stratumZ c g hopen k).subschemeι (mZ (IsLocalRing.closedPoint κ)) ∈
      Set.range (c.p g k)
    have := congrArg (fun φ => φ (IsLocalRing.closedPoint κ)) hmZ
    simp only [Scheme.Hom.comp_apply] at this
    rw [this]
    exact hm.1
  exact ⟨IsOpenImmersion.lift _ mZ hrange, by
    rw [stratumι, ← Category.assoc, IsOpenImmersion.lift_fac, hmZ]⟩

/-- The stratum of degree `k` is quasi-compact when `M` is Noetherian. -/
theorem compactSpace_stratum [IsNoetherian M] (k : ℕ) : CompactSpace (stratum c g hopen k) := by
  have hemb := (stratumι c g hopen k).isEmbedding
  rw [← isCompact_univ_iff, hemb.isCompact_iff, Set.image_univ]
  exact NoetherianSpace.isCompact _

/-- The stratum of degree `k` is locally of finite type over the integers. -/
theorem locallyOfFiniteType_stratum [LocallyOfFiniteType (specULiftZIsTerminal.from M)]
    (k : ℕ) : LocallyOfFiniteType (specULiftZIsTerminal.from (stratum c g hopen k)) := by
  rw [show specULiftZIsTerminal.from (stratum c g hopen k) =
      stratumι c g hopen k ≫ specULiftZIsTerminal.from M from specULiftZIsTerminal.hom_ext _ _]
  infer_instance

/-- The `κ`-points of the base change of `p_k` to the stratum over a lift `m'` of `m` are the
`κ`-points of `V_k` over `m`. -/
def stratumFamilyEquiv {k : ℕ} {κ : Type u} [Field κ] (m : Spec (CommRingCat.of κ) ⟶ M)
    (m' : Spec (CommRingCat.of κ) ⟶ stratum c g hopen k) (hm' : m' ≫ stratumι c g hopen k = m) :
    {x : Spec (CommRingCat.of κ) ⟶ pullback (c.p g k) (stratumι c g hopen k) //
        x ≫ pullback.snd _ _ = m'} ≃
      {v : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricScheme k // v ≫ c.p g k = m} where
  toFun x := ⟨x.1 ≫ pullback.fst _ _, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, hm']⟩
  invFun v := ⟨pullback.lift v.1 m' (by rw [v.2, hm']), pullback.lift_snd _ _ _⟩
  left_inv x := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_snd, x.2]))
  right_inv v := Subtype.ext (pullback.lift_fst _ _ _)

/-- The base change of `p_k` to the stratum of degree `k` has geometrically irreducible
fibres. -/
theorem geometricallyIrreducible_stratumFamily
    (hirr : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ M),
      @IrreducibleSpace (Points (fib g s)) (pointTopology _)) (k : ℕ) :
    GeometricallyIrreducible (pullback.snd (c.p g k) (stratumι c g hopen k)) := by
  constructor
  intro K _ y Z fst snd h
  have h' := h.paste_horiz (IsPullback.of_hasPullback (c.p g k) (stratumι c g hopen k))
  have hs : c.InStratum g k ((y ≫ stratumι c g hopen k) (IsLocalRing.closedPoint K)) := by
    rw [Scheme.Hom.comp_apply]
    exact inStratum_stratumι _
  have hirrP := irreducibleSpace_pullback_p (y ≫ stratumι c g hopen k) hs (hirr K _)
  exact (Homeomorph.irreducibleSpace_iff h'.isoPullback.hom.homeomorph).mpr hirrP

variable [LocallyOfFiniteType (specULiftZIsTerminal.from M)] [CompactSpace M]

/-- **The top degree.** On the stratum of degree `k`, the numbers of `κ`-points of `V_k` over
`κ`-points of `M` satisfy the uniform Lang–Weil estimate. -/
theorem exists_bound_top (hopen : ∀ n, IsOpen (Set.range (c.p g n)))
    (hFLW : FamilyLangWeilStatement.{u}) (π : c.U.left ⟶ M) {d : ℕ}
    [SmoothOfRelativeDimension d π] (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π))
    (hirr : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ M),
      @IrreducibleSpace (Points (fib g s)) (pointTopology _)) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] (m : Spec (CommRingCat.of κ) ⟶ M),
      c.InStratum g k (m (IsLocalRing.closedPoint κ)) →
      |(Nat.card {v : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricScheme k //
          v ≫ c.p g k = m} : ℝ) - (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
  have : IsLocallyNoetherian M := isLocallyNoetherian_of_locallyOfFiniteType M
  have : IsNoetherian M := {}
  have hP : PureFibreDimensionMorphismProperty d
      (pullback.snd (c.p g k) (stratumι c g hopen k)) :=
    MorphismProperty.pullback_snd _ _ (pureFibreDimension_p π ha k)
  obtain ⟨C, hC, hb⟩ := hFLW d (stratum c g hopen k)
    (pullback (c.p g k) (stratumι c g hopen k)) (pullback.snd _ _)
    (locallyOfFiniteType_stratum k) (compactSpace_stratum k) hP.1 inferInstance
    (geometricallyIrreducible_stratumFamily hirr k) (fun s => hP.2 s)
  refine ⟨C, hC, fun κ _ _ m hm => ?_⟩
  obtain ⟨m', hm'⟩ := exists_lift_stratumι m hm
  rw [← Nat.card_congr (stratumFamilyEquiv m m' hm')]
  exact hb κ m'

/-- **The lower degrees.** For `n < k`, the numbers of `κ`-points of the exact-degree scheme
`D_n` over `κ`-points of `M` in the stratum of degree `k` are at most `C (#κ) ^ (d - 1/2)`. -/
theorem exists_bound_lower (hFPU : FamilyPointUpperBoundStatement.{u}) (π : c.U.left ⟶ M)
    {d : ℕ} [SmoothOfRelativeDimension d π] (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π))
    (hirr : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ M),
      @IrreducibleSpace (Points (fib g s)) (pointTopology _)) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] (m : Spec (CommRingCat.of κ) ⟶ M)
      (k : ℕ), n < k → c.InStratum g k (m (IsLocalRing.closedPoint κ)) →
      (Nat.card {x : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricDegreeScheme n //
          x ≫ c.E.tupleSymmetricDegreeι n ≫ c.p g n = m} : ℝ) ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
  have : IsLocallyNoetherian M := isLocallyNoetherian_of_locallyOfFiniteType M
  have hpfd := pureFibreDimension_p π ha (g := g) (d := d) n
  have : LocallyOfFiniteType (c.p g n) := hpfd.1
  obtain ⟨C, hC, hb⟩ := hFPU M (c.E.tupleSymmetricDegreeScheme n)
    (c.E.tupleSymmetricDegreeι n ≫ c.p g n) ‹_› ‹_› inferInstance inferInstance
  refine ⟨C, hC, fun κ _ _ m k hnk hm => ?_⟩
  have hq : (1 : ℝ) ≤ Nat.card κ := by
    have : 0 < Nat.card κ := Nat.card_pos
    exact_mod_cast this
  have hdim := topologicalKrullDim_fiber_lt hnk hm (hirr _ _) hpfd
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hempty := isEmpty_of_topologicalKrullDim_lt_zero hdim
    have : IsEmpty {x : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricDegreeScheme n //
        x ≫ c.E.tupleSymmetricDegreeι n ≫ c.p g n = m} := ⟨fun x => by
      have hx : (c.E.tupleSymmetricDegreeι n ≫ c.p g n) (x.1 (IsLocalRing.closedPoint κ)) =
          m (IsLocalRing.closedPoint κ) := by
        have := congrArg (fun φ => φ (IsLocalRing.closedPoint κ)) x.2
        simpa only [Scheme.Hom.comp_apply] using this
      have hmem : x.1 (IsLocalRing.closedPoint κ) ∈
          Set.range ((c.E.tupleSymmetricDegreeι n ≫ c.p g n).fiberι
            (m (IsLocalRing.closedPoint κ))) := by
        rw [Scheme.Hom.range_fiberι]
        exact hx
      obtain ⟨z, -⟩ := hmem
      exact hempty.elim z⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  · have h1 := hb κ m (d - 1) (le_coe_pred_of_lt hdim)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hq
    rw [Nat.cast_sub hd]
    push_cast
    linarith

end SepChart

open SepChart in
/-- **The uniform Lang–Weil estimate over a scheme.** Let `X` be a separated algebraic space
with an affine étale chart `a : U → X`, `M` a quasi-compact scheme locally of finite type over
`ℤ`, `g : X → M` and `π : U → M` surjective and smooth of relative dimension `d` with
`a ≫ g = π`, such that the points of the fibre of `g` over every field point of `M` form a
connected space. Assuming the uniform Lang–Weil estimate and the uniform upper bound for point
counts in families of schemes, there is `C > 0` such that for every finite field `κ` and every
`κ`-point `m` of `M`, the number `N_m` of `κ`-points of `X` over `m` satisfies
`|N_m - (#κ) ^ d| ≤ C (#κ) ^ (d - 1/2)`. -/
theorem uniformLangWeil_schemeBase (hFLW : FamilyLangWeilStatement.{u})
    (hFPU : FamilyPointUpperBoundStatement.{u}) (c : SepChart.{u}) {M : Scheme.{u}}
    [LocallyOfFiniteType (specULiftZIsTerminal.from M)] [CompactSpace M]
    (g : c.X.presheaf ⟶ (schemeYoneda S0).obj (toOver M)) (π : c.U.left ⟶ M) {d : ℕ}
    [hπd : SmoothOfRelativeDimension d π] (hπ : Function.Surjective π)
    (ha : c.a ≫ g = (schemeYoneda S0).map (overHom π))
    (hconn : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ M),
      @ConnectedSpace (Points (fib g s)) (pointTopology _)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] (m : Spec (CommRingCat.of κ) ⟶ M),
      |(Nat.card (c.fibrePoints g κ m) : ℝ) - (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
  have : Smooth π := hπd.smooth
  have hirr : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ M),
      @IrreducibleSpace (Points (fib g s)) (pointTopology _) := fun K _ s =>
    irreducibleSpace_points_fib g s c.a π ha c.etale_a c.surj_a (hconn K s)
  have hopen := isOpen_range_p π ha
  choose C hC hCb using fun k : Fin c.N => exists_bound_top hopen hFLW π (d := d) ha hirr k
  choose C' hC' hC'b using fun n : Fin c.N => exists_bound_lower hFPU π (d := d) ha hirr n
  have hCsum : 0 ≤ ∑ k, C k := Finset.sum_nonneg fun k _ => (hC k).le
  have hC'sum : 0 ≤ ∑ n, C' n := Finset.sum_nonneg fun n _ => (hC' n).le
  refine ⟨1 + ∑ k, C k + ∑ n, C' n, by linarith, fun κ _ _ m => ?_⟩
  have hq : (1 : ℝ) ≤ Nat.card κ := by
    have : 0 < Nat.card κ := Nat.card_pos
    exact_mod_cast this
  have hQ : 0 ≤ (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg (by linarith) _
  obtain ⟨k, hkN, hk⟩ := exists_inStratum π hπ ha (m (IsLocalRing.closedPoint κ))
  have hfin : ∀ n, Finite (Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricScheme n) := fun n => by
    have : LocallyOfFiniteType (c.p g n) := (pureFibreDimension_p π ha (g := g) (d := d) n).1
    have : LocallyOfFiniteType (specULiftZIsTerminal.from (c.E.tupleSymmetricScheme n)) := by
      rw [show specULiftZIsTerminal.from (c.E.tupleSymmetricScheme n) =
          c.p g n ≫ specULiftZIsTerminal.from M from specULiftZIsTerminal.hom_ext _ _]
      infer_instance
    exact finite_hom_of_isAffine _ κ
  rw [card_fibrePoints κ m hfin]
  let a : Fin c.N → ℕ := fun n =>
    Nat.card {x : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricDegreeScheme n //
      x ≫ c.E.tupleSymmetricDegreeι n ≫ c.p g n = m}
  change |((∑ n, a n : ℕ) : ℝ) - _| ≤ _
  have hzero : ∀ n : Fin c.N, k < (n : ℕ) → a n = 0 := by
    intro n hn
    refine Nat.card_eq_zero.mpr (Or.inl ⟨fun x => ?_⟩)
    apply hk.2 n hn n.2
    refine ⟨(x.1 ≫ c.E.tupleSymmetricDegreeι n) (IsLocalRing.closedPoint κ), ?_⟩
    have := congrArg (fun φ => φ (IsLocalRing.closedPoint κ)) x.2
    simp only [Scheme.Hom.comp_apply] at this ⊢
    exact this
  have htop : a ⟨k, hkN⟩ = Nat.card {v : Spec (CommRingCat.of κ) ⟶ c.E.tupleSymmetricScheme k //
      v ≫ c.p g k = m} := by
    refine Nat.card_congr ((degreePointsEquiv κ m k).trans
      (Equiv.subtypeEquivRight fun v => ⟨And.right, fun h => ⟨?_, h⟩⟩))
    refine not_mem_threshold_of_inStratum hk ?_
    have := congrArg (fun φ => φ (IsLocalRing.closedPoint κ)) h
    simpa only [Scheme.Hom.comp_apply] using this
  have hpt : ∀ n : Fin c.N, (a n : ℝ) = (if n = ⟨k, hkN⟩ then (a n : ℝ) else 0) +
      (if (n : ℕ) < k then (a n : ℝ) else 0) := by
    intro n
    by_cases h1 : n = ⟨k, hkN⟩
    · subst h1
      simp
    · have h1' : (n : ℕ) ≠ k := fun h => h1 (Fin.ext h)
      by_cases h2 : (n : ℕ) < k
      · simp [h1, h2]
      · have : a n = 0 := hzero n (by omega)
        simp [h1, h2, this]
  have hsplit : ((∑ n, a n : ℕ) : ℝ) =
      (a ⟨k, hkN⟩ : ℝ) + ∑ n : Fin c.N, (if (n : ℕ) < k then (a n : ℝ) else 0) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun n _ => hpt n), Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  have h1 := hCb ⟨k, hkN⟩ κ m hk
  rw [← htop] at h1
  have h2 : ∑ n : Fin c.N, (if (n : ℕ) < k then (a n : ℝ) else 0) ≤
      ∑ n : Fin c.N, C' n * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
    refine Finset.sum_le_sum fun n _ => ?_
    split_ifs with h
    · exact hC'b n κ m k h hk
    · exact mul_nonneg (hC' n).le hQ
  have h3 : 0 ≤ ∑ n : Fin c.N, (if (n : ℕ) < k then (a n : ℝ) else 0) :=
    Finset.sum_nonneg fun n _ => by split_ifs <;> positivity
  have hCk : C ⟨k, hkN⟩ ≤ ∑ k, C k :=
    Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ _)
  rw [hsplit, ← Finset.sum_mul] at *
  rw [show (a ⟨k, hkN⟩ : ℝ) + ∑ n : Fin c.N, (if (n : ℕ) < k then (a n : ℝ) else 0) -
      (Nat.card κ : ℝ) ^ d = ((a ⟨k, hkN⟩ : ℝ) - (Nat.card κ : ℝ) ^ d) +
        ∑ n : Fin c.N, (if (n : ℕ) < k then (a n : ℝ) else 0) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg h3]
  nlinarith [mul_le_mul_of_nonneg_right hCk hQ]

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
