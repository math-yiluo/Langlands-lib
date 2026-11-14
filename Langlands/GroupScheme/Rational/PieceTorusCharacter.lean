import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Rational.PieceCorootFactorization
import Langlands.GroupScheme.HomConjugacy

/-! # Characters of torus parts of opposite-pair products

Over a split pinning, character values of cocharacter points and of conjugates of torus points
by normalizer points. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

local instance pieceTorusCharacterMono : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

/-- Evaluation of a character of the pinned torus on its rational points. -/
def charEval (χ : characterLattice p.torus) : rationalPoints p.torus.toGrp →* kˣ :=
  rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm χ)

/-- The rational point `ν(t)` of the pinned torus. -/
abbrev torusCocharacterPoint (ν : cocharacterLattice p.torus) : kˣ →* rationalPoints p.torus.toGrp :=
  CocharacterUniformizer.cocharacterPoints k p.torus ν

theorem charEval_torusCocharacterPoint (χ : characterLattice p.torus)
    (ν : cocharacterLattice p.torus) (t : kˣ) :
    p.charEval χ (p.torusCocharacterPoint ν t) = t ^ latticePairing p.torus χ ν := by
  unfold charEval torusCocharacterPoint
  rw [rationalCharacterEval_apply]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))
    (((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
      (CommGroupScheme.groupHom ν).hom.hom) ≫
      (CommGroupScheme.groupHom χ).hom.hom) = _
  rw [Category.assoc]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
      (CommGroupScheme.groupHom (ν ≫ χ)).hom.hom) = _
  conv_lhs => rw [← (gmEndEquiv k).symm_apply_apply (ν ≫ χ)]
  rw [gmEndEquiv_symm_comp, map_zpow, MulEquiv.apply_symm_apply, latticePairing_apply]

/-- Characters are compatible with endomorphisms of the torus. -/
theorem charEval_map (φ : p.torus ⟶ p.torus) (χ : characterLattice p.torus)
    (x : rationalPoints p.torus.toGrp) :
    p.charEval χ (rationalPoints.map (CommGroupScheme.groupHom φ) x) = p.charEval (φ ≫ χ) x := by
  unfold charEval
  rw [rationalCharacterEval_apply, rationalCharacterEval_apply]
  rfl

/-- The coroot point map into `G` is the image of the torus cocharacter point. -/
theorem cocharacterPoint_eq_map (ν : cocharacterLattice p.torus) (t : kˣ) :
    LinkedRootParametrization.cocharacterPoint p.inclusion ν t =
      rationalPoints.map p.inclusion (p.torusCocharacterPoint ν t) :=
  rfl

/-- Conjugating a torus point by a normalizer point applies the normalizing automorphism. -/
theorem conj_map_inclusion (n : normalizerPoints p.inclusion) (x : rationalPoints p.torus.toGrp) :
    (n : rationalPoints G) * rationalPoints.map p.inclusion x * (n : rationalPoints G)⁻¹ =
      rationalPoints.map p.inclusion (rationalPoints.map
        (CommGroupScheme.groupHom (normalizingAut p.inclusion n).hom) x) := by
  have h := isNormalizingPoint_normalizingAut p.inclusion n
  have h' := congrArg (fun φ : p.torus.toGrp ⟶ G => x ≫ φ.hom.hom) h
  simp only [Grp.comp_hom_hom, ← Category.assoc] at h'
  rw [comp_innerIso_hom, constantPoint_self] at h'
  rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply]
  exact h'

/-- If `n₀` acts on characters by the reflection in the root `m`, the normalizing automorphism
acts on a character `ω` by the same reflection. -/
theorem normalizingAut_hom_comp {m : p.rootIndex} (n₀ : normalizerPoints p.inclusion)
    (hn₀ : ∀ χ, weylAction p.inclusion n₀ χ =
      χ - p.rootDatum.toLinearMap χ (p.rootDatum.coroot m) • p.rootDatum.root m)
    (ω : characterLattice p.torus) :
    (normalizingAut p.inclusion n₀).hom ≫ ω =
      ω - p.rootDatum.toLinearMap ω (p.rootDatum.coroot m) • p.rootDatum.root m := by
  set ψ := (normalizingAut p.inclusion n₀).hom ≫ ω with hψ
  have h1 : weylAction p.inclusion n₀ ψ = ω := by
    rw [weylAction_apply, hψ, Iso.inv_hom_id_assoc]
  rw [hn₀] at h1
  have h2 := congrArg (fun χ => p.rootDatum.toLinearMap χ (p.rootDatum.coroot m)) h1
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    p.rootDatum.root_coroot_eq_pairing, p.rootDatum.pairing_same, smul_eq_mul] at h2
  have h3 : ψ = ω + p.rootDatum.toLinearMap ψ (p.rootDatum.coroot m) • p.rootDatum.root m := by
    rw [← h1]; abel
  have h4 : p.rootDatum.toLinearMap ψ (p.rootDatum.coroot m) =
      -p.rootDatum.toLinearMap ω (p.rootDatum.coroot m) := by
    linear_combination -h2
  rw [h3, h4, neg_smul, ← sub_eq_add_neg]

end SplitPinning

end Langlands.GroupScheme

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

local instance pieceTorusCharacterMono' : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

/-- The coroot of `reflectionPerm i i` is the negative of the coroot of `i`. -/
theorem coroot_reflectionPerm_self (i : p.rootIndex) :
    p.rootDatum.coroot (p.rootDatum.reflectionPerm i i) = -p.rootDatum.coroot i := by
  rw [p.rootDatum.coroot_reflectionPerm, p.rootDatum.coreflection_apply_self]

/-- Coroot points lie in the subgroup generated by the two opposite root groups. -/
theorem cocharacterPoint_mem_closure (s : p.rootIndex) (v : kˣ) :
    LinkedRootParametrization.cocharacterPoint p.inclusion (p.rootDatum.coroot s) v ∈
      Subgroup.closure
        ((rootGroupPoints p.inclusion (p.rootDatum.root s) : Set (rationalPoints G)) ∪
          rootGroupPoints p.inclusion (-p.rootDatum.root s)) := by
  let X := p.linkedRootParametrization s
  have h := (X.pinnedData).h_eq_word v
  change LinkedRootParametrization.cocharacterPoint p.inclusion (p.rootDatum.coroot s) v = _ at h
  rw [h]
  have hp : ∀ c, X.xpPoint c ∈ Subgroup.closure
      ((rootGroupPoints p.inclusion (p.rootDatum.root s) : Set (rationalPoints G)) ∪
        rootGroupPoints p.inclusion (-p.rootDatum.root s)) := fun c =>
    Subgroup.subset_closure (Or.inl (X.xpPoint_mem c))
  have hm : ∀ c, X.xmPoint c ∈ Subgroup.closure
      ((rootGroupPoints p.inclusion (p.rootDatum.root s) : Set (rationalPoints G)) ∪
        rootGroupPoints p.inclusion (-p.rootDatum.root s)) := fun c =>
    Subgroup.subset_closure (Or.inr (X.xmPoint_mem c))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hm _))
    (hp _)) (hm _)) (Subgroup.inv_mem _ (hp _))

/-- **The torus part of a piece.** For a normalizer point `n₀` acting by the reflection in
`m`, a unit `w` and `τ` in the image of the coroot of `s`, the element
`m^∨(w) · n₀ τ n₀⁻¹` is the image of a torus point `x`. Every character `ω` with
`⟨s_m ω, s^∨⟩ = 0` takes the value `w^⟨ω, m^∨⟩` at `x`. -/
theorem exists_piece_torusPart {m s : p.rootIndex} (n₀ : normalizerPoints p.inclusion)
    (hn₀ : ∀ χ, weylAction p.inclusion n₀ χ =
      χ - p.rootDatum.toLinearMap χ (p.rootDatum.coroot m) • p.rootDatum.root m)
    (w : kˣ) {τ : rationalPoints G}
    (hτ : τ ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
      (p.rootDatum.coroot s)).range) :
    ∃ x : rationalPoints p.torus.toGrp,
      LinkedRootParametrization.cocharacterPoint p.inclusion (p.rootDatum.coroot m) w *
          ((n₀ : rationalPoints G) * τ * (n₀ : rationalPoints G)⁻¹) =
        rationalPoints.map p.inclusion x ∧
      ∀ ω : characterLattice p.torus,
        p.rootDatum.toLinearMap
            (ω - p.rootDatum.toLinearMap ω (p.rootDatum.coroot m) • p.rootDatum.root m)
            (p.rootDatum.coroot s) = 0 →
          p.charEval ω x = w ^ p.rootDatum.toLinearMap ω (p.rootDatum.coroot m) := by
  obtain ⟨v, rfl⟩ := hτ
  refine ⟨p.torusCocharacterPoint (p.rootDatum.coroot m) w *
    rationalPoints.map (CommGroupScheme.groupHom (normalizingAut p.inclusion n₀).hom)
      (p.torusCocharacterPoint (p.rootDatum.coroot s) v), ?_, ?_⟩
  · rw [p.cocharacterPoint_eq_map, p.cocharacterPoint_eq_map, p.conj_map_inclusion, map_mul]
  · intro ω hω
    rw [map_mul, p.charEval_torusCocharacterPoint, p.charEval_map,
      p.normalizingAut_hom_comp n₀ hn₀, p.charEval_torusCocharacterPoint,
      ← p.isRootDatum.1, hω, zpow_zero, mul_one]

section Pieces

variable [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {f : S ⟶ p.torus} {a : characterLattice S}
  (hline : RestrictsToMultipliableLine f p.rootDatum a)

/-- Quotient of two ordered products of pairwise commuting families. -/
theorem list_ofFn_prod_mul_inv {M : Type*} [Group M] {r : ℕ} (A B : Fin r → M)
    (hB : ∀ l m, l ≠ m → Commute (B l) (B m)) (hAB : ∀ l m, l ≠ m → Commute (B l) (A m)) :
    (List.ofFn A).prod * ((List.ofFn B).prod)⁻¹ = (List.ofFn fun l => A l * (B l)⁻¹).prod := by
  rw [list_ofFn_prod_inv_of_commute B hB]
  have h := list_ofFn_prod_mul_mul A (fun l => (B l)⁻¹) (fun _ => (1 : M)) (fun l m hlm =>
    ⟨(hAB l m hlm).inv_left, Commute.one_left _, Commute.one_left _⟩)
  simp only [mul_one, List.ofFn_const, List.prod_replicate, one_pow] at h
  exact h.symm

include hline in
/-- **Torus part of a ratio of opposite products.** Let `x_m l` be root parametrizations of the
roots `m_l` of a piece family `F`. Compare the opposite product `n` of
`g = ∏ₗ X_l x_{m_l}(w_l) Y_l` with the opposite product `n₀` of `g₀ = ∏ₗ x_{m_l}(1)`. Then
`n n₀⁻¹` is the image of a torus point `x`, and every character `ω` orthogonal to all coroots
`q_l^∨` satisfies `ω(x) = ∏ₗ w_l^⟨ω, p_l^∨⟩`. -/
theorem exists_oppositeProducts_torusPart (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ p.inclusion).hom.hom.left]
    (F : PieceFamily f p.rootDatum a) (ha0 : a ≠ 0)
    (xm : ∀ l, p.RootParametrization (F.lm l)) (w : Fin F.r → kˣ)
    {X Y : Fin F.r → rationalPoints G}
    (hX : ∀ l, X l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lq l)))
    (hY : ∀ l, Y l ∈ rootGroupPoints p.inclusion (p.rootDatum.root (F.lp l)))
    (hg : F.tripleProd X (fun l => (xm l).rationalPoint (w l)) Y ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) a)
    (hg1 : F.tripleProd X (fun l => (xm l).rationalPoint (w l)) Y ≠ 1)
    {g' g'' : rationalPoints G}
    (hg' : g' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a))
    (hg'' : g'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a))
    (hN : g' * F.tripleProd X (fun l => (xm l).rationalPoint (w l)) Y * g'' ∈
      normalizerPoints p.inclusion)
    (hN' : g' * F.tripleProd X (fun l => (xm l).rationalPoint (w l)) Y * g'' ∈
      normalizerPoints (CommGroupScheme.groupHom f ≫ p.inclusion))
    (hg₀ : F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1) ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) a)
    (hg₀1 : F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1) ≠ 1)
    {g₀' g₀'' : rationalPoints G}
    (hg₀' : g₀' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a))
    (hg₀'' : g₀'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ p.inclusion) (-a))
    (hN₀ : g₀' * F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1) *
      g₀'' ∈ normalizerPoints p.inclusion)
    (hN₀' : g₀' * F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1) *
      g₀'' ∈ normalizerPoints (CommGroupScheme.groupHom f ≫ p.inclusion)) :
    ∃ x : rationalPoints p.torus.toGrp,
      g' * F.tripleProd X (fun l => (xm l).rationalPoint (w l)) Y * g'' *
          (g₀' * F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1) *
            g₀'')⁻¹ = rationalPoints.map p.inclusion x ∧
      ∀ ω : characterLattice p.torus,
        (∀ l, p.rootDatum.toLinearMap ω (p.rootDatum.coroot (F.lq l)) = 0) →
          p.charEval ω x =
            ∏ l, (w l) ^ p.rootDatum.toLinearMap ω (p.rootDatum.coroot (F.lp l)) := by
  classical
  have hT := p.isSplitTorus
  have hjc : IsClosedSubgroup p.inclusion := p.isMaximalTorus.2.1
  have hP := p.isRootDatum
  have hE := splitPinnedOppositeFactorPairs k G p
  have hZ : ∀ l, (xm l).rationalPoint (w l) ∈ rootGroupPoints p.inclusion
      (p.rootDatum.root (F.lm l)) := fun l => (xm l).rationalPoint_mem _
  have hZ1 : ∀ l, (xm l).rationalPoint (w l) ≠ 1 := fun l =>
    (xm l).rationalPoint_ne_one (w l).ne_zero
  have hZ₀ : ∀ l, (xm l).rationalPoint 1 ∈ rootGroupPoints p.inclusion
      (p.rootDatum.root (F.lm l)) := fun l => (xm l).rationalPoint_mem _
  have hZ₀1 : ∀ l, (xm l).rationalPoint 1 ≠ 1 := fun l =>
    (xm l).rationalPoint_ne_one one_ne_zero
  choose pr hpr using fun l => hE (p.rootDatum.root (F.lm l)) (p.root_mem_relativeRoots _) _
    (hZ l) (hZ1 l)
  choose pr₀ hpr₀ using fun l => hE (p.rootDatum.root (F.lm l)) (p.root_mem_relativeRoots _) _
    (hZ₀ l) (hZ₀1 l)
  obtain ⟨τ, hτ, hn⟩ := p.oppositeProduct_eq_prod hline hS F ha0 hX hZ hY hZ1 hg hg1 hg' hg''
    hN hN' hpr
  obtain ⟨τ₀, hτ₀, hn₀⟩ := p.oppositeProduct_eq_prod hline hS F ha0
    (fun _ => Subgroup.one_mem _) hZ₀ (fun _ => Subgroup.one_mem _) hZ₀1 hg₀ hg₀1 hg₀' hg₀''
    hN₀ hN₀' hpr₀
  rw [hn, hn₀]
  -- piece-group memberships
  have pr_mem : ∀ l (χ : characterLattice p.torus), χ ∈ pieceRoots p.rootDatum (F.lp l)
      (F.lq l) (F.lm l) → ∀ y ∈ rootGroupPoints p.inclusion χ,
        y ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) :=
    fun l χ hχ y hy => mem_pieceGroup_of_mem p.inclusion hχ hy
  have hτG : ∀ l {t : rationalPoints G}, t ∈ (LinkedRootParametrization.cocharacterPoint
      p.inclusion (p.rootDatum.coroot (p.rootDatum.reflectionPerm (F.lp l) (F.lp l)))).range →
      t ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := by
    intro l t ht
    obtain ⟨v, rfl⟩ := ht
    have hc := p.cocharacterPoint_mem_closure (p.rootDatum.reflectionPerm (F.lp l) (F.lp l)) v
    rw [root_reflectionPerm_self, neg_neg] at hc
    refine (Subgroup.closure_le _).mpr ?_ hc
    rintro y (hy | hy)
    · exact pr_mem l _ (by simp [pieceRoots]) y hy
    · exact pr_mem l _ (by simp [pieceRoots]) y hy
  have hAG : ∀ l, (pr l).1 * (xm l).rationalPoint (w l) * (pr l).2 * τ l ∈
      pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (pr_mem l _ (by simp [pieceRoots]) _ (hpr l).1)
      (pr_mem l _ (by simp [pieceRoots]) _ (hZ l)))
      (pr_mem l _ (by simp [pieceRoots]) _ (hpr l).2.1)) (hτG l (hτ l))
  have hBG : ∀ l, (pr₀ l).1 * (xm l).rationalPoint 1 * (pr₀ l).2 * τ₀ l ∈
      pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (pr_mem l _ (by simp [pieceRoots]) _ (hpr₀ l).1)
      (pr_mem l _ (by simp [pieceRoots]) _ (hZ₀ l)))
      (pr_mem l _ (by simp [pieceRoots]) _ (hpr₀ l).2.1)) (hτG l (hτ₀ l))
  have hcomm : ∀ l m, l ≠ m → ∀ {u v : rationalPoints G},
      u ∈ pieceGroup p.inclusion p.rootDatum (F.lp l) (F.lq l) (F.lm l) →
      v ∈ pieceGroup p.inclusion p.rootDatum (F.lp m) (F.lq m) (F.lm m) → Commute u v := by
    intro l m hlm u v hu hv
    exact commute_of_mem_pieceGroup p.inclusion
      (pieces_commute p.inclusion hT hP hline (F.piece l) (F.piece m) (F.disjoint l m hlm)) hu hv
  rw [list_ofFn_prod_mul_inv _ _ (fun l m hlm => hcomm l m hlm (hBG l) (hBG m))
    (fun l m hlm => hcomm l m hlm (hBG l) (hAG m))]
  -- the torus part of each piece
  have hpiece : ∀ l, ∃ x : rationalPoints p.torus.toGrp,
      (pr l).1 * (xm l).rationalPoint (w l) * (pr l).2 * τ l *
          ((pr₀ l).1 * (xm l).rationalPoint 1 * (pr₀ l).2 * τ₀ l)⁻¹ =
        rationalPoints.map p.inclusion x ∧
      ∀ ω : characterLattice p.torus,
        p.rootDatum.toLinearMap ω (p.rootDatum.coroot (F.lq l)) = 0 →
          p.charEval ω x = (w l) ^ p.rootDatum.toLinearMap ω (p.rootDatum.coroot (F.lp l)) := by
    intro l
    obtain ⟨hp, hq, hpq, hm⟩ := F.piece l
    obtain ⟨-, -, -, -, hm1, -, -, -, -⟩ := piece_pairings hline hp hq hpq hm
    have hcm := piece_coroot_m hline hp hq hpq hm
    have hwa := weylAction_oppositeFactorPair_eq p.inclusion hT hjc hP (F.lm l) (hZ₀ l)
      (hZ₀1 l) (hpr₀ l)
    have hτ' : τ l * (τ₀ l)⁻¹ ∈ (LinkedRootParametrization.cocharacterPoint p.inclusion
        (p.rootDatum.coroot (p.rootDatum.reflectionPerm (F.lp l) (F.lp l)))).range :=
      Subgroup.mul_mem _ (hτ l) (Subgroup.inv_mem _ (hτ₀ l))
    obtain ⟨x, hx, hxω⟩ := p.exists_piece_torusPart
      (⟨(pr₀ l).1 * (xm l).rationalPoint 1 * (pr₀ l).2, (hpr₀ l).2.2⟩ :
        normalizerPoints p.inclusion) hwa (w l) hτ'
    refine ⟨x, ?_, ?_⟩
    · rw [← hx, ← RootParametrization.oppositeProduct_mul_inv p (xm l) (w l) (hpr l) (hpr₀ l)]
      group
    · intro ω hω
      have hωm : p.rootDatum.toLinearMap ω (p.rootDatum.coroot (F.lm l)) =
          p.rootDatum.toLinearMap ω (p.rootDatum.coroot (F.lp l)) := by
        rw [hcm, map_add, hω, add_zero]
      rw [hxω ω ?_, hωm]
      rw [p.coroot_reflectionPerm_self, map_neg, map_sub, map_zsmul, LinearMap.sub_apply,
        LinearMap.smul_apply, hm1, hωm, smul_eq_mul, mul_one, sub_self, neg_zero]
  choose x hx hxω using hpiece
  refine ⟨(List.ofFn x).prod, ?_, ?_⟩
  · rw [map_list_prod, List.map_ofFn]
    congr 1
    apply List.ofFn_inj.mpr
    funext l
    exact hx l
  · intro ω hω
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun l _ => hxω l ω (hω l)

end Pieces

end SplitPinning

end Langlands.GroupScheme
