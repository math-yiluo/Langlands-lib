import Langlands.GroupScheme.Rational.SimpleRootFiberPinning
import Langlands.GroupScheme.Rational.OrthogonalOrbitRootCoordinates
import Langlands.GroupScheme.Rational.LinkedRootOppositePairs
import Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement

/-! # Orbit products over a simple relative root fiber from the split product statement -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LinkedRootParametrization

open LocalSplitCell RankOneRootCellRelation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {r : p.rootIndex}
  (X : LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r))

/-- Every rational point of the negative root subgroup is a value of `x₋`. -/
theorem exists_xmPoint_eq {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) : ∃ c : k, X.xmPoint c = g := by
  obtain ⟨c, hc⟩ := LocalSplitCell.exists_rootPoint_eq (α := p.rootDatum.root r)
    X.negative_represents (g := g) hg
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom c, ?_⟩
  rw [← hc, xmPoint]
  have hsec : secMap k ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom c) = c := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom c = c
    rw [Iso.hom_inv_id]
    rfl
  rw [hsec]
  rfl

/-- `x₋` is injective on rational points. -/
theorem xmPoint_injective : Function.Injective X.xmPoint := by
  intro c c' h
  have : Mono X.negative.hom.hom := X.negative_represents.1
  have h' := (cancel_mono X.negative.hom.hom).mp h
  exact (secMap k).injective (gpt_injective h')

/-- `x₊` is injective on rational points. -/
theorem xpPoint_injective : Function.Injective X.xpPoint := by
  intro c c' h
  have : Mono X.positive.hom.hom := X.positive_represents.1
  have h' := (cancel_mono X.positive.hom.hom).mp h
  exact (secMap k).injective (gpt_injective h')

end LinkedRootParametrization

namespace SplitPinning

section ListProducts

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance simpleRootFiberProductsIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (x : p.NormalizedSimpleRootParametrizations)
    (O : Set p.base.support)
    (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b)
    [Fintype O] {n : ℕ} (e : O ≃ Fin n)

open Classical in
/-- The members of `O` listed along an enumeration. -/
theorem univ_eq_toFinset_ofFn :
    (Finset.univ : Finset O) = (List.ofFn fun r => e.symm r).toFinset := by
  ext t
  simp only [Finset.mem_univ, List.mem_toFinset, true_iff]
  exact List.mem_ofFn.mpr ⟨e t, by simp⟩

/-- The positive orbit product is the ordered product along any enumeration of `O`. -/
theorem orbitXp_eq_prod_ofFn (c : p.base.support → K) :
    orbitXp k K p x O hO c =
      (List.ofFn fun r => (rankData x (e.symm r)).xp (c (e.symm r))).prod := by
  classical
  rw [orbitXp, Langlands.Algebra.RankOneRelation.prodHom, Subgroup.noncommPiCoprod_apply,
    Finset.noncommProd_congr (univ_eq_toFinset_ofFn k K p O e) (fun _ _ => rfl),
    Finset.noncommProd_toFinset _ _ _ (List.nodup_ofFn.mpr e.symm.injective), List.map_ofFn]
  rfl

/-- The negative orbit product is the ordered product along any enumeration of `O`. -/
theorem orbitXm_eq_prod_ofFn (c : p.base.support → K) :
    orbitXm k K p x O hO c =
      (List.ofFn fun r => (rankData x (e.symm r)).xm (c (e.symm r))).prod := by
  classical
  rw [orbitXm, Langlands.Algebra.RankOneRelation.prodHom, Subgroup.noncommPiCoprod_apply,
    Finset.noncommProd_congr (univ_eq_toFinset_ofFn k K p O e) (fun _ _ => rfl),
    Finset.noncommProd_toFinset _ _ _ (List.nodup_ofFn.mpr e.symm.injective), List.map_ofFn]
  rfl

end ListProducts

end SplitPinning

namespace SimpleRootFiber

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange bK) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange bK) j
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f

local instance simpleRootFiberProductsIsAffineHomK : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bK)
  infer_instance

variable {J : Type u} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
  (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  [P.IsReduced]
  (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
  [FiniteDimensional k K]
  (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
  (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
  [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
  (hR : HasRelativeRootSystem (CommGroupScheme.groupHom f ≫ j))
  [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)]

local notation "Dₚ" => fiberPinning k K f j hP hf hcent hT ν hν hGK hi
local notation "Oₐ" => fiberSet k K f j hP hf hcent hT ν hν hGK hi a

/-- The roots of the fiber, enumerated along `Fintype.equivFin`. -/
def fiberRootEnum (t : Fin (Fintype.card Oₐ)) : characterLattice T_K :=
  (Dₚ).pinning.rootDatum.root ((Fintype.equivFin Oₐ).symm t).1

omit [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left] in
/-- Distinct members of the fiber have distinct roots. -/
theorem fiberRootEnum_injective :
    Function.Injective (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a)) := by
  intro r r' h
  apply (Fintype.equivFin Oₐ).symm.injective
  apply Subtype.ext
  apply Subtype.ext
  exact (Dₚ).pinning.rootDatum.root.injective h

include ha h2a hR in
/-- The fiber roots are exactly the roots of `T_K` restricting to a positive multiple of `a`. -/
theorem mem_range_fiberRootEnum_iff (χ : characterLattice T_K) :
    χ ∈ Set.range (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a)) ↔
      (χ ∈ roots j_K ∧ ∃ m : ℕ, 0 < m ∧ f_K ≫ χ = m • characterLattice.baseChange bK S a) := by
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨root_mem_roots k K j hP _, 1, one_pos, ?_⟩
    rw [one_nsmul]
    exact (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a _).mp
      ((Fintype.equivFin Oₐ).symm r).2
  · rintro ⟨hχ, m, hm, hfχ⟩
    obtain ⟨idx, rfl⟩ : χ ∈ Set.range P.root := by
      rw [hP.2.1]
      exact hχ
    have hres : restrictCharacter k K f hf.1.1 (P.root idx) = m • a := by
      rw [restrictCharacter_eq_iff, map_nsmul]
      exact hfχ
    have hm1 := eq_one_of_restrictCharacter_eq_nsmul k K f j hP hf hcent hT hR ha.1.1 h2a idx hres
    subst hm1
    rw [one_nsmul] at hres
    obtain ⟨t, ht, rfl⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha idx hres
    refine ⟨Fintype.equivFin Oₐ ⟨t, ht⟩, ?_⟩
    simp only [fiberRootEnum, Equiv.symm_apply_apply]
    rfl

include ha h2a hR in
/-- The negatives of the fiber roots are exactly the roots of `T_K` restricting to a positive
multiple of `-a`. -/
theorem mem_range_neg_fiberRootEnum_iff (χ : characterLattice T_K) :
    χ ∈ Set.range (fun r => -fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r) ↔
      (χ ∈ roots j_K ∧
        ∃ m : ℕ, 0 < m ∧ f_K ≫ χ = m • characterLattice.baseChange bK S (-a)) := by
  constructor
  · rintro ⟨r, rfl⟩
    have hfr := (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a _).mp
      ((Fintype.equivFin Oₐ).symm r).2
    refine ⟨hP.neg_mem_roots (root_mem_roots k K j hP _), 1, one_pos, ?_⟩
    rw [one_nsmul, map_neg, ← hfr]
    exact Preadditive.comp_neg _ _
  · rintro ⟨hχ, m, hm, hfχ⟩
    obtain ⟨r, hr⟩ := (mem_range_fiberRootEnum_iff k K f j hP hf hcent hT ν hν hGK hi
      ha h2a hR (-χ)).mpr ⟨hP.neg_mem_roots hχ, m, hm, by
        rw [Preadditive.comp_neg, hfχ, map_neg, smul_neg, neg_neg]⟩
    exact ⟨r, by simp [hr]⟩

section Products

variable (hProd : Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement.{u})

local notation "hOₐ" => fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a
local notation "eₐ" => Fintype.equivFin (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)

omit [LocallyOfFiniteType G.X.hom] [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  [Finite J] [P.IsReduced] [FiniteDimensional k K]
  [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
  [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)] in
include hf in
/-- A simple relative root stays nonzero after base change. -/
theorem baseChange_ne_zero_of_simple {b : characterLattice S}
    (hb : b ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν) :
    characterLattice.baseChange bK S b ≠ 0 := by
  intro h
  apply hb.1.1.1
  apply (characterLattice.baseChangeEquiv bK S hf.1.1).injective
  rw [AddEquiv.map_zero]
  exact h

include ha h2a hR hProd in
/-- The split product statement for the fiber roots of `a`. -/
theorem fiberProduct_pos :
    (∀ g : rationalPoints (G_K),
      g ∈ Langlands.Geometry.Building.rootGroupPoints (S := S_K)
        ((GroupScheme.baseChange bK).map (CommGroupScheme.groupHom f ≫ j))
        (characterLattice.baseChange bK S a) ↔
      ∃ y : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
          (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r),
        g = (List.ofFn fun r => (y r : rationalPoints (G_K))).prod) ∧
    ∀ y y' : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
        (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r),
      (List.ofFn fun r => (y r : rationalPoints (G_K))).prod =
          (List.ofFn fun r => (y' r : rationalPoints (G_K))).prod → y = y' :=
  by
    have hSK : IsSplitTorus ((CommGroupScheme.baseChange bK).obj S).toGrp :=
      hf.1.1.baseChange bK
    have h := hProd K (G_K) hGK (S_K) (T_K) j_K f_K hT hi hSK
      (characterLattice.baseChange bK S a)
      (baseChange_ne_zero_of_simple k K f j hf ν ha) (Fintype.card Oₐ)
      (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a))
      (fiberRootEnum_injective k K f j hP hf hcent hT ν hν hGK hi)
      (mem_range_fiberRootEnum_iff k K f j hP hf hcent hT ν hν hGK hi ha h2a hR)
    rw [Functor.map_comp]
    exact h

include ha h2a hR hProd in
/-- The split product statement for the negatives of the fiber roots of `a`. -/
theorem fiberProduct_neg :
    (∀ g : rationalPoints (G_K),
      g ∈ Langlands.Geometry.Building.rootGroupPoints (S := S_K)
        ((GroupScheme.baseChange bK).map (CommGroupScheme.groupHom f ≫ j))
        (characterLattice.baseChange bK S (-a)) ↔
      ∃ y : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
          (-fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r),
        g = (List.ofFn fun r => (y r : rationalPoints (G_K))).prod) ∧
    ∀ y y' : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints (S := T_K) j_K
        (-fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r),
      (List.ofFn fun r => (y r : rationalPoints (G_K))).prod =
          (List.ofFn fun r => (y' r : rationalPoints (G_K))).prod → y = y' :=
  by
    have hSK : IsSplitTorus ((CommGroupScheme.baseChange bK).obj S).toGrp :=
      hf.1.1.baseChange bK
    have hne : characterLattice.baseChange bK S (-a) ≠ 0 := by
      rw [map_neg, neg_ne_zero]
      exact baseChange_ne_zero_of_simple k K f j hf ν ha
    have h := hProd K (G_K) hGK (S_K) (T_K) j_K f_K hT hi hSK
      (characterLattice.baseChange bK S (-a)) hne (Fintype.card Oₐ)
      (fun r => -fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r)
      (neg_injective.comp (fiberRootEnum_injective k K f j hP hf hcent hT ν hν hGK hi))
      (mem_range_neg_fiberRootEnum_iff k K f j hP hf hcent hT ν hν hGK hi ha h2a hR)
    rw [Functor.map_comp]
    exact h

include ha h2a hR hProd in
/-- Every point of the root group of `a_K` is a positive orbit product over the fiber. -/
theorem fiber_hprodp : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f ≫ j))
      (characterLattice.baseChange (algebraBaseMap k K) S a) →
        ∃ c : (Dₚ).pinning.base.support → K,
          g = SplitPinning.orbitXp k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hOₐ c := by
  classical
  intro g hg
  obtain ⟨y, rfl⟩ :=
    ((fiberProduct_pos k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd).1 g).mp hg
  have hy : ∀ r, ∃ c : K, ((Dₚ).rootMaps ((eₐ).symm r).1).linked.xpPoint c =
      (y r : rationalPoints (G_K)) := fun r =>
    ((Dₚ).rootMaps ((eₐ).symm r).1).linked.exists_xpPoint_eq (y r).2
  choose c hc using hy
  refine ⟨fun t => if h : t ∈ Oₐ then c (eₐ ⟨t, h⟩) else 0, ?_⟩
  rw [SplitPinning.orbitXp_eq_prod_ofFn k K _ _ Oₐ hOₐ eₐ]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  have hcr : (fun t => if h : t ∈ Oₐ then c (eₐ ⟨t, h⟩) else 0) ((eₐ).symm r).1 = c r := by
    simp only [dite_eq_left_of_eq_true (eq_true ((eₐ).symm r).2), Subtype.coe_eta,
      Equiv.apply_symm_apply]
  exact (hc r).symm.trans
    (congrArg ((SplitPinning.rankData (Dₚ).rootMaps ((eₐ).symm r).1).xp) hcr.symm)

include ha h2a hR hProd in
/-- Positive orbit products over the fiber determine their coordinates on the fiber. -/
theorem fiber_huniqp : ∀ c c' : (Dₚ).pinning.base.support → K,
    SplitPinning.orbitXp k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hOₐ c =
      SplitPinning.orbitXp k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hOₐ c' →
        ∀ t ∈ Oₐ, c t = c' t := by
  intro c c' h t ht
  rw [SplitPinning.orbitXp_eq_prod_ofFn k K _ _ Oₐ hOₐ eₐ,
    SplitPinning.orbitXp_eq_prod_ofFn k K _ _ Oₐ hOₐ eₐ] at h
  let y : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints
      (S := T_K) j_K (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r) := fun r =>
    ⟨((Dₚ).rootMaps ((eₐ).symm r).1).linked.xpPoint (c ((eₐ).symm r).1),
      ((Dₚ).rootMaps ((eₐ).symm r).1).linked.xpPoint_mem _⟩
  let y' : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints
      (S := T_K) j_K (fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r) := fun r =>
    ⟨((Dₚ).rootMaps ((eₐ).symm r).1).linked.xpPoint (c' ((eₐ).symm r).1),
      ((Dₚ).rootMaps ((eₐ).symm r).1).linked.xpPoint_mem _⟩
  have hyy := (fiberProduct_pos k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd).2 y y' h
  have h2 := congrArg Subtype.val (congrFun hyy (eₐ ⟨t, ht⟩))
  simp only [y, y'] at h2
  have h3 := ((Dₚ).rootMaps ((eₐ).symm (eₐ ⟨t, ht⟩)).1).linked.xpPoint_injective h2
  simpa only [Equiv.symm_apply_apply] using h3

include ha h2a hR hProd in
/-- Every point of the root group of `-a_K` is a negative orbit product over the fiber. -/
theorem fiber_hprodm : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f ≫ j))
      (characterLattice.baseChange (algebraBaseMap k K) S (-a)) →
        ∃ c : (Dₚ).pinning.base.support → K,
          g = SplitPinning.orbitXm k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hOₐ c := by
  classical
  intro g hg
  obtain ⟨y, rfl⟩ :=
    ((fiberProduct_neg k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd).1 g).mp hg
  have hy : ∀ r, ∃ c : K, ((Dₚ).rootMaps ((eₐ).symm r).1).linked.xmPoint c =
      (y r : rationalPoints (G_K)) := fun r =>
    ((Dₚ).rootMaps ((eₐ).symm r).1).linked.exists_xmPoint_eq (y r).2
  choose c hc using hy
  refine ⟨fun t => if h : t ∈ Oₐ then c (eₐ ⟨t, h⟩) else 0, ?_⟩
  rw [SplitPinning.orbitXm_eq_prod_ofFn k K _ _ Oₐ hOₐ eₐ]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  have hcr : (fun t => if h : t ∈ Oₐ then c (eₐ ⟨t, h⟩) else 0) ((eₐ).symm r).1 = c r := by
    simp only [dite_eq_left_of_eq_true (eq_true ((eₐ).symm r).2), Subtype.coe_eta,
      Equiv.apply_symm_apply]
  exact (hc r).symm.trans
    (congrArg ((SplitPinning.rankData (Dₚ).rootMaps ((eₐ).symm r).1).xm) hcr.symm)

include ha h2a hR hProd in
/-- Negative orbit products over the fiber determine their coordinates on the fiber. -/
theorem fiber_huniqm : ∀ c c' : (Dₚ).pinning.base.support → K,
    SplitPinning.orbitXm k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hOₐ c =
      SplitPinning.orbitXm k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hOₐ c' →
        ∀ t ∈ Oₐ, c t = c' t := by
  intro c c' h t ht
  rw [SplitPinning.orbitXm_eq_prod_ofFn k K _ _ Oₐ hOₐ eₐ,
    SplitPinning.orbitXm_eq_prod_ofFn k K _ _ Oₐ hOₐ eₐ] at h
  let y : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints
      (S := T_K) j_K (-fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r) := fun r =>
    ⟨((Dₚ).rootMaps ((eₐ).symm r).1).linked.xmPoint (c ((eₐ).symm r).1),
      ((Dₚ).rootMaps ((eₐ).symm r).1).linked.xmPoint_mem _⟩
  let y' : (r : Fin (Fintype.card Oₐ)) → Langlands.Geometry.Building.rootGroupPoints
      (S := T_K) j_K (-fiberRootEnum k K f j hP hf hcent hT ν hν hGK hi (a := a) r) := fun r =>
    ⟨((Dₚ).rootMaps ((eₐ).symm r).1).linked.xmPoint (c' ((eₐ).symm r).1),
      ((Dₚ).rootMaps ((eₐ).symm r).1).linked.xmPoint_mem _⟩
  have hyy := (fiberProduct_neg k K f j hP hf hcent hT ν hν hGK hi ha h2a hR hProd).2 y y' h
  have h2 := congrArg Subtype.val (congrFun hyy (eₐ ⟨t, ht⟩))
  simp only [y, y'] at h2
  have h3 := ((Dₚ).rootMaps ((eₐ).symm (eₐ ⟨t, ht⟩)).1).linked.xmPoint_injective h2
  simpa only [Equiv.symm_apply_apply] using h3

end Products

end SimpleRootFiber

end Langlands.GroupScheme
