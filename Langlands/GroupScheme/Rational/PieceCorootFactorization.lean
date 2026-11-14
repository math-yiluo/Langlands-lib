import Langlands.GroupScheme.Rational.LinkedRootOppositePairs
import Langlands.Geometry.Building.QuasiSplitMultipliableOpposite

/-! # Piece factorizations with explicit coroot torus factors

Over a field `k` with a split pinning `p` of `G`, the rank-one Gauss decomposition and the
piece factorization of the Library (module `Geometry.Building.QuasiSplitMultipliableFactorization`)
are refined: the torus factor `τ` lies in the image of a coroot. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

/-- Conjugating by an ordered product whose factors other than the `l`-th commute with `x` and
with its conjugate by the `l`-th factor amounts to conjugating by the `l`-th factor. -/
theorem list_ofFn_prod_conj {M : Type*} [Group M] : ∀ {r : ℕ} (L : Fin r → M) (l : Fin r)
    (x : M), (∀ m, m ≠ l → Commute (L m) x) →
    (∀ m, m ≠ l → Commute (L m) (L l * x * (L l)⁻¹)) →
    (List.ofFn L).prod * x * ((List.ofFn L).prod)⁻¹ = L l * x * (L l)⁻¹
  | 0, _, l, _, _, _ => l.elim0
  | r + 1, L, l, x, hx, hy => by
    rw [List.ofFn_succ, List.prod_cons]
    cases l using Fin.cases with
    | zero =>
      have hrest : Commute (List.ofFn fun i : Fin r => L i.succ).prod x := by
        apply Commute.list_prod_left
        intro y hy'
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hy'
        exact hx i.succ (Fin.succ_ne_zero i)
      calc L 0 * (List.ofFn fun i : Fin r => L i.succ).prod * x *
            (L 0 * (List.ofFn fun i : Fin r => L i.succ).prod)⁻¹
          = L 0 * ((List.ofFn fun i : Fin r => L i.succ).prod * x) *
            ((List.ofFn fun i : Fin r => L i.succ).prod)⁻¹ * (L 0)⁻¹ := by group
        _ = L 0 * x * (L 0)⁻¹ := by rw [hrest.eq]; group
    | succ l' =>
      have ih := list_ofFn_prod_conj (fun i : Fin r => L i.succ) l' x
        (fun m hm => hx m.succ (fun h => hm (Fin.succ_injective _ h)))
        (fun m hm => hy m.succ (fun h => hm (Fin.succ_injective _ h)))
      have h0 : Commute (L 0) (L l'.succ * x * (L l'.succ)⁻¹) :=
        hy 0 (Fin.succ_ne_zero l').symm
      calc L 0 * (List.ofFn fun i : Fin r => L i.succ).prod * x *
            (L 0 * (List.ofFn fun i : Fin r => L i.succ).prod)⁻¹
          = L 0 * ((List.ofFn fun i : Fin r => L i.succ).prod * x *
            ((List.ofFn fun i : Fin r => L i.succ).prod)⁻¹) * (L 0)⁻¹ := by group
        _ = L 0 * (L l'.succ * x * (L l'.succ)⁻¹) * (L 0)⁻¹ := by rw [ih]
        _ = L l'.succ * x * (L l'.succ)⁻¹ := by rw [h0.eq]; group

namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

local instance pieceCorootFactorizationMono : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

/-- **Rank-one Gauss decomposition with a coroot factor.** For `f ∈ U_s` and `X ∈ U_{-s}`,
either `f X = X' τ f'` with `X' ∈ U_{-s}`, `τ` in the image of the coroot of `s` and
`f' ∈ U_s`, or `f X = B ν` with `B ∈ U_{-s}` and `ν` normalizing the torus with
`ν(-s) = s`. -/
theorem gauss_decomposition_coroot (s : p.rootIndex) {f X : rationalPoints G}
    (hf : f ∈ rootGroupPoints p.inclusion (p.rootDatum.root s))
    (hX : X ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s)) :
    (∃ X' ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s),
        ∃ τ ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
          (p.rootDatum.coroot s)).range,
        ∃ f' ∈ rootGroupPoints p.inclusion (p.rootDatum.root s), f * X = X' * τ * f') ∨
      (∃ B ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s), ∃ ν : normalizerPoints p.inclusion,
        f * X = B * ν ∧ weylAction p.inclusion ν (-p.rootDatum.root s) = p.rootDatum.root s) := by
  have hT := p.isSplitTorus
  have hE := splitPinnedOppositeFactorPairs k G p
  have hs : p.rootDatum.root s ∈ relativeRoots p.inclusion := p.root_mem_relativeRoots s
  by_cases hf1 : f = 1
  · left
    exact ⟨X, hX, 1, ⟨1, map_one _⟩, 1, Subgroup.one_mem _, by simp [hf1]⟩
  obtain ⟨pr, hpr⟩ := hE (p.rootDatum.root s) hs f hf hf1
  have hpr1 : pr.1 ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s) := hpr.1
  have hpr2 : pr.2 ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s) := hpr.2.1
  set μf : normalizerPoints p.inclusion := ⟨pr.1 * f * pr.2, hpr.2.2⟩ with hμf
  have hflip : weylAction p.inclusion μf (p.rootDatum.root s) = -p.rootDatum.root s :=
    hpr.weylAction_eq_neg p.inclusion hT hs.1 hf hf1
  have hflip' : weylAction p.inclusion μf (-p.rootDatum.root s) = p.rootDatum.root s := by
    rw [map_neg, hflip, neg_neg]
  set Z := pr.2⁻¹ * X with hZ
  have hZmem : Z ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hpr2) hX
  have hfX : f * X = pr.1⁻¹ * (μf : rationalPoints G) * Z := by
    rw [hZ, hμf]; group
  by_cases hZ1 : Z = 1
  · right
    refine ⟨pr.1⁻¹, Subgroup.inv_mem _ hpr1, μf, ?_, hflip'⟩
    rw [hfX, hZ1, mul_one]
  left
  have hW : (μf : rationalPoints G) * Z * (μf : rationalPoints G)⁻¹ ∈
      rootGroupPoints p.inclusion (p.rootDatum.root s) := by
    have h := conj_mem_rootGroupPoints μf hZmem
    rwa [hflip'] at h
  have hW1 : (μf : rationalPoints G) * Z * (μf : rationalPoints G)⁻¹ ≠ 1 := by
    intro h
    apply hZ1
    have := congrArg (fun y => (μf : rationalPoints G)⁻¹ * y * (μf : rationalPoints G)) h
    simpa [mul_assoc] using this
  obtain ⟨qr, hqr⟩ := hE (p.rootDatum.root s) hs _ hW hW1
  have hqr1 : qr.1 ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s) := hqr.1
  have hqr2 : qr.2 ∈ rootGroupPoints p.inclusion (-p.rootDatum.root s) := hqr.2.1
  have hf' : (μf : rationalPoints G)⁻¹ * qr.2⁻¹ * (μf : rationalPoints G) ∈
      rootGroupPoints p.inclusion (p.rootDatum.root s) := by
    apply inv_conj_mem_rootGroupPoints p.inclusion μf
    rw [hflip]
    exact Subgroup.inv_mem _ hqr2
  have hτ := p.oppositeProduct_mul_mem_range s hW hW1 hf hf1 hqr hpr
  refine ⟨pr.1⁻¹ * qr.1⁻¹, Subgroup.mul_mem _ (Subgroup.inv_mem _ hpr1)
    (Subgroup.inv_mem _ hqr1), _, hτ, _, hf', ?_⟩
  have hμv : (μf : rationalPoints G) = pr.1 * f * pr.2 := rfl
  rw [hfX]
  simp only [hμv]
  group

section Piece

variable [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {f : S ⟶ p.torus} {a : characterLattice S}
  (hline : RestrictsToMultipliableLine f p.rootDatum a) {lp lq lm : p.rootIndex}
  (hp : f ≫ p.rootDatum.root lp = a) (hq : f ≫ p.rootDatum.root lq = a) (hpq : lp ≠ lq)
  (hm : p.rootDatum.root lm = p.rootDatum.root lp + p.rootDatum.root lq)

include hline hp hq hpq hm in
/-- **Piece factorization with a coroot factor.** As the Library's `piece_factorization`,
with the torus factor `τ` of the first case in the image of the coroot of `-p`. -/
theorem piece_factorization_coroot {Xq Xm Xp : rationalPoints G}
    (hXq : Xq ∈ rootGroupPoints p.inclusion (p.rootDatum.root lq))
    (hXm : Xm ∈ rootGroupPoints p.inclusion (p.rootDatum.root lm))
    (hXm1 : Xm ≠ 1) (hXp : Xp ∈ rootGroupPoints p.inclusion (p.rootDatum.root lp))
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root lm) Xm pr) :
    (∃ e ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lq),
        ∃ τ ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
          (p.rootDatum.coroot (p.rootDatum.reflectionPerm lp lp))).range,
        ∃ f' ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lp),
        ∃ c ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lq),
        Xq * Xm * Xp = (pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * e) *
          ((pr.1 * Xm * pr.2) * τ) * (f' * c * pr.2⁻¹)) ∨
      (∃ e ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lq),
        ∃ ν : normalizerPoints p.inclusion,
        ∃ c ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lq),
        Xq * Xm * Xp = (pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * e) * (ν : rationalPoints G) *
          (c * pr.2⁻¹) ∧
        weylAction p.inclusion ν (p.rootDatum.root lp) = p.rootDatum.root lq) := by
  have hT := p.isSplitTorus
  have hjc : IsClosedSubgroup p.inclusion := p.isMaximalTorus.2.1
  have hP := p.isRootDatum
  have hE := splitPinnedOppositeFactorPairs k G p
  obtain ⟨hwp, hwq⟩ := piece_weylAction_m p.inclusion hT hjc hP hline hp hq hpq hm hXm hXm1 hpr
  set mu : normalizerPoints p.inclusion := ⟨pr.1 * Xm * pr.2, hpr.2.2⟩ with hμ
  have hmuv : (mu : rationalPoints G) = pr.1 * Xm * pr.2 := rfl
  have hY' : pr.2⁻¹ ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lm) :=
    Subgroup.inv_mem _ hpr.2.1
  have hm' : p.rootDatum.root lm = p.rootDatum.root lq + p.rootDatum.root lp := by
    rw [hm, add_comm]
  set c := Xp⁻¹ * pr.2⁻¹ * Xp * pr.2 with hc
  have hcmem : c ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lq) := by
    have h := piece_commutator_mem_neg_m_q p.inclusion hT hE hP hline hq hp (Ne.symm hpq) hm' hY'
      (Subgroup.inv_mem _ hXp)
    have heq : c = (pr.2⁻¹ * Xp⁻¹ * pr.2⁻¹⁻¹ * Xp⁻¹⁻¹)⁻¹ := by rw [hc]; group
    rw [heq]
    exact Subgroup.inv_mem _ h
  set fq := (mu : rationalPoints G)⁻¹ * Xq * (mu : rationalPoints G) with hfq
  have hfqmem : fq ∈ rootGroupPoints p.inclusion (-p.rootDatum.root lp) := by
    apply inv_conj_mem_rootGroupPoints p.inclusion mu
    rw [map_neg, hwp, neg_neg]
    exact hXq
  have hkey : Xq * Xm * Xp = pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * (mu : rationalPoints G) *
      (fq * Xp) * c * pr.2⁻¹ := by
    rw [hfq, hc, hmuv]; group
  have hrs : p.rootDatum.root (p.rootDatum.reflectionPerm lp lp) = -p.rootDatum.root lp :=
    root_reflectionPerm_self lp
  have hfq' : fq ∈ rootGroupPoints p.inclusion
      (p.rootDatum.root (p.rootDatum.reflectionPerm lp lp)) := by
    rw [hrs]; exact hfqmem
  have hXp' : Xp ∈ rootGroupPoints p.inclusion
      (-p.rootDatum.root (p.rootDatum.reflectionPerm lp lp)) := by
    rw [hrs, neg_neg]; exact hXp
  rcases p.gauss_decomposition_coroot (p.rootDatum.reflectionPerm lp lp) hfq' hXp' with
    ⟨X', hX', τ, hτ, f', hf', hgauss⟩ | ⟨B, hB, ν, hgauss, hν⟩
  · left
    rw [hrs, neg_neg] at hX'
    rw [hrs] at hf'
    have he : (mu : rationalPoints G) * X' * (mu : rationalPoints G)⁻¹ ∈
        rootGroupPoints p.inclusion (-p.rootDatum.root lq) := by
      have h := conj_mem_rootGroupPoints mu hX'
      rwa [hwp] at h
    refine ⟨_, he, τ, hτ, f', hf', c, hcmem, ?_⟩
    rw [hkey, hgauss, ← hmuv]
    group
  · right
    rw [hrs, neg_neg] at hB hν
    have he : (mu : rationalPoints G) * B * (mu : rationalPoints G)⁻¹ ∈
        rootGroupPoints p.inclusion (-p.rootDatum.root lq) := by
      have h := conj_mem_rootGroupPoints mu hB
      rwa [hwp] at h
    refine ⟨_, he, mu * ν, c, hcmem, ?_, ?_⟩
    · rw [hkey, hgauss, Subgroup.coe_mul]
      group
    · rw [map_mul, LinearEquiv.mul_apply, hν, map_neg, hwp, neg_neg]

end Piece

section Pieces

variable [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {f : S ⟶ p.torus} {a : characterLattice S}
  (hline : RestrictsToMultipliableLine f p.rootDatum a)

include hline in
/-- **The opposite product of a product of piece triples.** Let `g = ∏ₗ X_l Z_l Y_l` be a
nontrivial point of the restricted root group of `a`, in piece coordinates with every
`Z_l ≠ 1`, and let `g' g g''` normalize both the torus and `groupHom f ≫ p.inclusion`, with
`g', g''` in the restricted root group of `-a`. For any opposite pairs `pr l` of the `Z_l`,
`g' g g'' = ∏ₗ (pr l).1 Z_l (pr l).2 τ_l` with each `τ_l` in the image of the coroot of `-p_l`. -/
theorem oppositeProduct_eq_prod (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ p.inclusion).hom.hom.left]
    (F : PieceFamily f p.rootDatum a) (ha0 : a ≠ 0)
    {X Z Y : Fin F.r → rationalPoints G}
    (hX : ∀ l, X l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lq l)))
    (hZ : ∀ l, Z l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lm l)))
    (hY : ∀ l, Y l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lp l)))
    (hZ1 : ∀ l, Z l ≠ 1)
    (hg : F.tripleProd X Z Y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) a)
    (hg1 : F.tripleProd X Z Y ≠ 1) {g' g'' : rationalPoints G}
    (hg' : g' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a))
    (hg'' : g'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a))
    (hN : g' * F.tripleProd X Z Y * g'' ∈ normalizerPoints p.inclusion)
    (hN' : g' * F.tripleProd X Z Y * g'' ∈
      normalizerPoints (CommGroupScheme.groupHom f ≫ p.inclusion))
    {pr : Fin F.r → rationalPoints G × rationalPoints G}
    (hpr : ∀ l, RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root (F.lm l))
      (Z l) (pr l)) :
    ∃ τ : Fin F.r → rationalPoints G,
      (∀ l, τ l ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
        (p.rootDatum.coroot (p.rootDatum.reflectionPerm (F.lp l) (F.lp l)))).range) ∧
      g' * F.tripleProd X Z Y * g'' =
        (List.ofFn fun l => (pr l).1 * Z l * (pr l).2 * τ l).prod := by
  classical
  have hT := p.isSplitTorus
  have hP := p.isRootDatum
  have hE := splitPinnedOppositeFactorPairs k G p
  -- uniform piece factorizations
  have huni : ∀ l, ∃ e ∈ rootGroupPoints p.inclusion (-p.rootDatum.root (F.lq l)),
      ∃ N' : normalizerPoints p.inclusion,
      ∃ f' ∈ rootGroupPoints p.inclusion (-p.rootDatum.root (F.lp l)),
      ∃ c ∈ rootGroupPoints p.inclusion (-p.rootDatum.root (F.lq l)),
      X l * Z l * Y l = ((pr l).1⁻¹ * ((pr l).1 * X l * (pr l).1⁻¹ * (X l)⁻¹) * e) *
        (N' : rationalPoints G) * (f' * c * (pr l).2⁻¹) ∧
      ((∃ τ ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
          (p.rootDatum.coroot (p.rootDatum.reflectionPerm (F.lp l) (F.lp l)))).range,
          (N' : rationalPoints G) = (pr l).1 * Z l * (pr l).2 * τ) ∨
        weylAction p.inclusion N' (p.rootDatum.root (F.lp l)) = p.rootDatum.root (F.lq l)) := by
    intro l
    obtain ⟨hp, hq, hpq, hm⟩ := F.piece l
    rcases p.piece_factorization_coroot hline hp hq hpq hm (hX l) (hZ l) (hZ1 l) (hY l) (hpr l)
      with ⟨e, he, τ, hτ, f', hf', c, hc, h⟩ | ⟨e, he, ν, c, hc, h, hν⟩
    · have hτN : τ ∈ normalizerPoints p.inclusion := by
        obtain ⟨t, rfl⟩ := hτ
        exact SplitPinning.NormalizedRootParametrization.cocharacterPoint_mem_normalizerPoints
          (p := p) _ t
      exact ⟨e, he, ⟨(pr l).1 * Z l * (pr l).2 * τ, Subgroup.mul_mem _ (hpr l).2.2 hτN⟩,
        f', hf', c, hc, h, Or.inl ⟨τ, hτ, rfl⟩⟩
    · refine ⟨e, he, ν, 1, Subgroup.one_mem _, c, hc, ?_, Or.inr hν⟩
      rw [one_mul]
      exact h
  choose e he N' f' hf' c hc hfac hcase using huni
  set d : Fin F.r → rationalPoints G :=
    fun l => (pr l).1 * X l * (pr l).1⁻¹ * (X l)⁻¹ with hd
  set L : Fin F.r → rationalPoints G := fun l => (pr l).1⁻¹ * d l * e l with hL
  set R : Fin F.r → rationalPoints G := fun l => f' l * c l * (pr l).2⁻¹ with hR
  have hdmem : ∀ l, d l ∈ rootGroupPoints p.inclusion (-p.rootDatum.root (F.lp l)) := fun l =>
    piece_commutator_mem_neg_m_q p.inclusion hT hE hP hline (F.piece l).1 (F.piece l).2.1
      (F.piece l).2.2.1 (F.piece l).2.2.2 (hpr l).1 (hX l)
  have pr_mem : ∀ l (χ : characterLattice p.torus),
      (χ = p.rootDatum.root (F.lp l) ∨ χ = p.rootDatum.root (F.lq l) ∨
        χ = p.rootDatum.root (F.lm l) ∨ χ = -p.rootDatum.root (F.lp l) ∨
        χ = -p.rootDatum.root (F.lq l) ∨ χ = -p.rootDatum.root (F.lm l)) →
      ∀ y ∈ rootGroupPoints p.inclusion χ,
        y ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := by
    intro l χ hχ y hy
    apply mem_pieceGroup_of_mem p.inclusion _ hy
    rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pieceRoots]
  have hLG : ∀ l, L l ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (pr_mem l _ (by tauto) _ (hpr l).1)) (pr_mem l _ (by tauto) _ (hdmem l)))
      (pr_mem l _ (by tauto) _ (he l))
  have hRG : ∀ l, R l ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (pr_mem l _ (by tauto) _ (hf' l))
      (pr_mem l _ (by tauto) _ (hc l))) (Subgroup.inv_mem _ (pr_mem l _ (by tauto) _ (hpr l).2.1))
  have hhG : ∀ l, X l * Z l * Y l ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) :=
    fun l => Subgroup.mul_mem _ (Subgroup.mul_mem _ (pr_mem l _ (by tauto) _ (hX l))
      (pr_mem l _ (by tauto) _ (hZ l))) (pr_mem l _ (by tauto) _ (hY l))
  have hNG : ∀ l, (N' l : rationalPoints G) ∈
      pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := by
    intro l
    have h : (N' l : rationalPoints G) = (L l)⁻¹ * (X l * Z l * Y l) * (R l)⁻¹ := by
      rw [hfac l]; simp only [hL, hR, hd]; group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLG l)) (hhG l))
      (Subgroup.inv_mem _ (hRG l))
  have hcomm : ∀ l m, l ≠ m → ∀ {u v : rationalPoints G},
      u ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) →
      v ∈ pieceGroup p.inclusion p.rootDatum (F.lp m) (F.lq m) (F.lm m) → Commute u v := by
    intro l m hlm u v hu hv
    exact commute_of_mem_pieceGroup p.inclusion
      (pieces_commute p.inclusion hT hP hline (F.piece l) (F.piece m) (F.disjoint l m hlm)) hu hv
  have hprod : F.tripleProd X Z Y = (List.ofFn L).prod *
      (List.ofFn fun l => (N' l : rationalPoints G)).prod * (List.ofFn R).prod := by
    unfold PieceFamily.tripleProd
    rw [← list_ofFn_prod_mul_mul L (fun l => (N' l : rationalPoints G)) R]
    · congr 1
      apply List.ofFn_inj.mpr
      funext l
      exact hfac l
    · intro l m hlm
      exact ⟨hcomm l m hlm (hNG l) (hLG m), hcomm l m hlm (hRG l) (hLG m),
        hcomm l m hlm (hRG l) (hNG m)⟩
  have hrest : ∀ (χ : characterLattice p.torus) (n : ℕ), 0 < n → χ ∈ relativeRoots p.inclusion →
      f ≫ χ = n • (-a) → ∀ y ∈ rootGroupPoints p.inclusion χ,
        y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a) := by
    intro χ n hn hχ hfχ y hy
    exact rootGroupPoints_le_comp p.inclusion hT hE hS (neg_ne_zero.mpr ha0) hχ hn hfχ hy
  have hnegroot : ∀ i : p.rootIndex, -p.rootDatum.root i ∈ relativeRoots p.inclusion := fun i =>
    neg_mem_relativeRoots_of_isRootDatumOf p.inclusion hP (p.root_mem_relativeRoots i)
  have hfp : ∀ l, f ≫ (-p.rootDatum.root (F.lp l)) = 1 • (-a) := fun l => by
    rw [Preadditive.comp_neg, (F.piece l).1, one_smul]
  have hfq : ∀ l, f ≫ (-p.rootDatum.root (F.lq l)) = 1 • (-a) := fun l => by
    rw [Preadditive.comp_neg, (F.piece l).2.1, one_smul]
  have hfm : ∀ l, f ≫ (-p.rootDatum.root (F.lm l)) = 2 • (-a) := fun l => by
    rw [Preadditive.comp_neg, (F.piece l).2.2.2, Preadditive.comp_add, (F.piece l).1,
      (F.piece l).2.1, smul_neg, two_nsmul]
  have hLS : ∀ l, L l ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (hrest _ 2 two_pos (hnegroot _) (hfm l) _ (hpr l).1))
      (hrest _ 1 one_pos (hnegroot _) (hfp l) _ (hdmem l)))
      (hrest _ 1 one_pos (hnegroot _) (hfq l) _ (he l))
  have hRS : ∀ l, R l ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hrest _ 1 one_pos (hnegroot _) (hfp l) _ (hf' l))
      (hrest _ 1 one_pos (hnegroot _) (hfq l) _ (hc l)))
      (Subgroup.inv_mem _ (hrest _ 2 two_pos (hnegroot _) (hfm l) _ (hpr l).2.1))
  have hLpS : (List.ofFn L).prod ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a) := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hy
    exact hLS l
  have hRpS : (List.ofFn R).prod ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a) := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hy
    exact hRS l
  have hNeq : ((List.ofFn L).prod)⁻¹ * F.tripleProd X Z Y * ((List.ofFn R).prod)⁻¹ =
      (List.ofFn fun l => (N' l : rationalPoints G)).prod := by
    rw [hprod]; group
  have hNprod : ((List.ofFn L).prod)⁻¹ * F.tripleProd X Z Y * ((List.ofFn R).prod)⁻¹ ∈
      normalizerPoints p.inclusion := by
    rw [hNeq]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hy
    exact (N' l).prop
  obtain ⟨-, hnEq⟩ := eq_of_mul_mul_mem_normalizer p.inclusion hS f ha0 hg hg1 hg' hg'' hN hN'
    (Subgroup.inv_mem _ hLpS) (Subgroup.inv_mem _ hRpS) hNprod
  have hn : g' * F.tripleProd X Z Y * g'' =
      (List.ofFn fun l => (N' l : rationalPoints G)).prod := by
    rw [← hnEq, hNeq]
  -- every piece is in the first case
  have hfirst : ∀ l, ∃ τ ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
      (p.rootDatum.coroot (p.rootDatum.reflectionPerm (F.lp l) (F.lp l)))).range,
      (N' l : rationalPoints G) = (pr l).1 * Z l * (pr l).2 * τ := by
    intro l
    refine (hcase l).resolve_right fun hν => ?_
    let x := (p.linkedRootParametrization (F.lp l)).xpPoint 1
    have hx : x ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lp l)) :=
      (p.linkedRootParametrization (F.lp l)).xpPoint_mem 1
    have hx1 : x ≠ 1 := (p.linkedRootParametrization (F.lp l)).xpPoint_ne_one one_ne_zero
    have hxG := pr_mem l _ (by tauto) _ hx
    have hconjG : (N' l : rationalPoints G) * x * (N' l : rationalPoints G)⁻¹ ∈
        pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hNG l) hxG) (Subgroup.inv_mem _ (hNG l))
    have hconj := list_ofFn_prod_conj (fun l => (N' l : rationalPoints G)) l x
      (fun m hm => hcomm m l hm (hNG m) hxG) (fun m hm => hcomm m l hm (hNG m) hconjG)
    rw [← hn] at hconj
    -- the conjugate lies in the restricted root groups of `a` and of `-a`
    have hfa : f ≫ p.rootDatum.root (F.lp l) = 1 • a := by rw [(F.piece l).1, one_smul]
    have hfqa : f ≫ p.rootDatum.root (F.lq l) = 1 • a := by rw [(F.piece l).2.1, one_smul]
    have hxa : x ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) a :=
      rootGroupPoints_le_comp p.inclusion hT hE hS ha0 (p.root_mem_relativeRoots _) one_pos hfa hx
    have hpos : (N' l : rationalPoints G) * x * (N' l : rationalPoints G)⁻¹ ∈
        rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) a := by
      have h := conj_mem_rootGroupPoints (N' l) hx
      rw [hν] at h
      exact rootGroupPoints_le_comp p.inclusion hT hE hS ha0 (p.root_mem_relativeRoots _) one_pos
        hfqa h
    have hopp : RelativeRoot.IsOppositeFactorPair (CommGroupScheme.groupHom f ≫ p.inclusion) a
        (F.tripleProd X Z Y) (g', g'') := ⟨hg', hg'', hN'⟩
    have hflip := hopp.weylAction_eq_neg (CommGroupScheme.groupHom f ≫ p.inclusion) hS ha0 hg hg1
    have hneg : g' * F.tripleProd X Z Y * g'' * x * (g' * F.tripleProd X Z Y * g'')⁻¹ ∈
        rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a) := by
      have h := conj_mem_rootGroupPoints (⟨g' * F.tripleProd X Z Y * g'', hN'⟩ :
        normalizerPoints (CommGroupScheme.groupHom f ≫ p.inclusion)) hxa
      rw [hflip] at h
      exact h
    rw [hconj] at hneg
    have h1 := RelativeRoot.eq_one_of_mem_subgroup_of_mem_opposite
      (CommGroupScheme.groupHom f ≫ p.inclusion) hS ha0 hpos hneg
    apply hx1
    have h2 := congrArg (fun y => (N' l : rationalPoints G)⁻¹ * y * (N' l : rationalPoints G)) h1
    simpa [mul_assoc] using h2
  choose τ hτ hNτ using hfirst
  refine ⟨τ, hτ, ?_⟩
  rw [hn]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  exact hNτ l

end Pieces

end SplitPinning

end Langlands.GroupScheme
