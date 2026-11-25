/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Data.Int.Interval

/-! # Homology of a finite-free zero-differential internal Hom complex

Source: Stacks Project, Tags 0BQY and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

-- An additive functor preserves a product supported on a finite set.
private noncomputable def map_finiteSupport_fan
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {I : Type*} (X : I → A)
    (t : Fan X) (ht : IsLimit t) (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (X i)) :
    IsLimit (Fan.mk (F.obj t.pt) (fun i ↦ F.map (t.proj i))) := by
  classical
  let t' : Fan (fun i : s ↦ X i) := Fan.mk t.pt (fun i ↦ t.proj i)
  have ht' : IsLimit t' := by
    refine Fan.IsLimit.mk t' (fun c ↦ ht.lift
      (Fan.mk c.pt (fun i ↦ if h : i ∈ s then c.proj ⟨i, h⟩ else 0))) ?_ ?_
    · intro c i
      simp [t']
    · intro c m hm
      refine ht.uniq
        (Fan.mk c.pt (fun i ↦ if h : i ∈ s then c.proj ⟨i, h⟩ else 0)) m ?_
      rintro ⟨i⟩
      by_cases hi : i ∈ s
      · change m ≫ t.proj i = _
        have hmi := hm ⟨i, hi⟩
        change m ≫ t.proj i = c.proj ⟨i, hi⟩ at hmi
        simpa only [Fan.mk_π_app, dite_eq_left hi] using hmi
      · exact (hz i hi).eq_of_tgt _ _
  have hFt' : IsLimit (Fan.mk (F.obj t.pt) (fun i : s ↦ F.map (t.proj i))) :=
    (Fan.isLimitMapConeEquiv F _ t') (isLimitOfPreserves F ht')
  refine Fan.IsLimit.mk _ (fun c ↦ hFt'.lift
    (Fan.mk c.pt (fun i : s ↦ c.proj i))) ?_ ?_
  · intro c i
    by_cases hi : i ∈ s
    · exact hFt'.fac (Fan.mk c.pt (fun j : s ↦ c.proj j)) ⟨i, hi⟩
    · exact (F.map_isZero (hz i hi)).eq_of_tgt _ _
  · intro c m hm
    refine hFt'.uniq (Fan.mk c.pt (fun i : s ↦ c.proj i)) m ?_
    rintro ⟨i⟩
    exact hm i

private theorem homMap_zero_left
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom 0) = 0
  rw [map_zero, map_zero]

private theorem homObj_isZero_left
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    (A B : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hA : IsZero A) : IsZero (SheafOfModules.homObj (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero]
  rw [← SheafOfModules.homObjMap_id (R := R) (M := A) (N := B)]
  rw [hA.eq_of_src (𝟙 A) 0, homMap_zero_left]

private instance homFunctor_additive
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (A : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ((SheafOfModules.homFunctor R).obj (op A)).Additive where
  map_add {M N} f g := by
    change SheafOfModules.homObjMap (𝟙 A) (f + g) =
      SheafOfModules.homObjMap (𝟙 A) f + SheafOfModules.homObjMap (𝟙 A) g
    apply SheafOfModules.hom_ext
    ext U φ : 3
    change (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 A : A ⟶ A).val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj U.unop).map (f + g).val =
      ((PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 A : A ⟶ A).val ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj U.unop).map f.val) +
      ((PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 A : A ⟶ A).val ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj U.unop).map g.val)
    ext W x
    rfl

private theorem finiteFreeHom_preservesHomology
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (A : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hA : ∃ r : ℕ, Nonempty (A ≅ SheafOfModules.free (ULift.{u} (Fin r)))) :
    ((SheafOfModules.homFunctor R).obj (op A)).PreservesHomology := by
  let F := (SheafOfModules.homFunctor R).obj (op A)
  apply ((Functor.exact_tfae F).out 1 3).1
  intro T hT
  obtain ⟨r, ⟨e⟩⟩ := hA
  obtain ⟨hz, h, _⟩ := SheafOfModules.finiteFreeInternalHomExact r A e T hT
  exact h

private theorem exactHomologyMap_cycle_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (T : ShortComplex B) (S : ShortComplex A) (φ : T ⟶ S.map F)
    (d : T.cycles ⟶ F.obj S.cycles)
    (hd : d ≫ F.map S.iCycles = T.iCycles ≫ φ.τ₂) :
    d ≫ F.map S.homologyπ =
      T.homologyπ ≫ ShortComplex.homologyMap φ ≫ (S.mapHomologyIso F).hom := by
  have : PreservesFiniteLimits F := Functor.preservesFiniteLimits_of_preservesHomology F
  have hcomp : (S.mapCyclesIso F).hom ≫ F.map S.homologyπ =
      (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom := by
    rw [S.leftHomologyData.mapCyclesIso_eq F,
      S.leftHomologyData.mapHomologyIso_eq F]
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso]
    rw [Category.assoc, ← F.map_comp,
      ← S.leftHomologyData.π_comp_homologyIso_inv,
      F.map_comp, ← Category.assoc]
    change ((S.leftHomologyData.map F).cyclesIso.hom ≫
      (S.leftHomologyData.map F).π) ≫ F.map S.leftHomologyData.homologyIso.inv = _
    rw [← (S.leftHomologyData.map F).homologyπ_comp_homologyIso_hom, Category.assoc]
  have he : d = ShortComplex.cyclesMap φ ≫ (S.mapCyclesIso F).hom := by
    apply (cancel_mono (F.map S.iCycles)).1
    rw [hd, Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles,
      ShortComplex.cyclesMap_i]
  rw [he, Category.assoc, hcomp, ShortComplex.homologyπ_naturality_assoc]

private noncomputable def fan_postcompose_iso
    {A : Type*} [Category A] {I : Type*} {X Y : I → A}
    (t : Fan X) (ht : IsLimit t) (e : ∀ i, X i ≅ Y i) :
    IsLimit (Fan.mk t.pt (fun i ↦ t.proj i ≫ (e i).hom)) := by
  refine Fan.IsLimit.mk _
    (fun c ↦ ht.lift (Fan.mk c.pt (fun i ↦ c.proj i ≫ (e i).inv))) ?_ ?_
  · intro c i
    simp only [fan_mk_proj]
    rw [← Category.assoc]
    simp [Fan.proj]
  · intro c m hm
    refine ht.uniq (Fan.mk c.pt (fun i ↦ c.proj i ≫ (e i).inv)) m ?_
    rintro ⟨i⟩
    change m ≫ t.proj i = c.proj i ≫ (e i).inv
    have hmi := congrArg (· ≫ (e i).inv) (hm i)
    simpa only [fan_mk_proj, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hmi

/-- The coordinate homology maps exhibit Hom-complex homology as a product.

Source: Stacks Project, Tag 0BQY, finite-free Hom calculation in Lemma 48.15.4,
expanded using Tag 0A8X, the product terms and differential of the Hom complex.
(blueprint: new-h3-finite-free-zero-homology-product).

Proof: Write P = Hom(E,K) and F_p = Hom(E.X p,-). The fixed product projections
and the zero differential of E give a map from the three-term short complex of P
at n to F_p applied to the three-term short complex of K at p+n. These maps are
product projections on each of the three objects, hence form a limiting fan of
short complexes. Outside a finite interval the source E.X p is zero and therefore
all three coordinate objects are zero. Restrict the fan to the finite interval;
its missing projections are uniquely zero. The additive short-complex homology
functor preserves this finite product, and its image of every omitted object is
again zero, giving a limiting fan on homology. finiteFreeInternalHomExact and
Functor.exact_tfae show that F_p preserves homology. Its canonical comparison
isomorphism identifies each coordinate homology with Hom(E.X p,H^(p+n)(K)).
Postcompose the limiting fan by these isomorphisms to obtain g. The comparison
on cycles followed by F_p(iCycles) is the ambient projection; this morphism is
monic because F_p is exact. Thus every supplied cycle lift d equals the canonical
one. Naturality of homologyπ and the exact-functor homology comparison give the
last equation. Transport along p+n=q gives the proof-indexed form. Empty support,
rank-zero coordinates, and arbitrary (not concentrated) K use the same argument.
-/
theorem finiteFreeZero_homologyProduct
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (ULift.{u} (Fin r)))) :
    let P := homComplex (R := R) E K
    ∃ g : ∀ (p q : ℤ), p + n = q →
        (P.homology n ⟶ SheafOfModules.homObj (R := R) (E.X p) (K.homology q)),
      Nonempty (IsLimit (Fan.mk (P.homology n)
        (fun p : ℤ ↦ g p (p + n) rfl))) ∧
      ∀ (p q : ℤ) (hpq : p + n = q)
        (d : P.cycles n ⟶ SheafOfModules.homObj (R := R) (E.X p) (K.cycles q)),
        d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles q) =
          P.iCycles n ≫ (Classical.choose (homComplex_projections_exists (R := R)))
            E K n p q hpq →
        d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ q) =
          P.homologyπ n ≫ g p q hpq  := by
  classical
  let P := homComplex (R := R) E K
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
  have hπ := Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := R))
  let c := ComplexShape.up ℤ
  have hn (k : ℤ) : c.next k = k + 1 := c.next_eq' rfl
  have hp (k : ℤ) : c.prev k = k - 1 := c.prev_eq' (by
    change k - 1 + 1 = k
    omega)
  let F (p : ℤ) := (SheafOfModules.homFunctor R).obj (op (E.X p))
  have hF (p : ℤ) : (F p).PreservesHomology :=
    finiteFreeHom_preservesHomology R (E.X p) (hfree p)
  let Q (p : ℤ) :=
    (K.sc' (p + c.prev n) (p + n) (p + c.next n)).map (F p)
  have hd (a b p q q' : ℤ) (hab : a + 1 = b)
      (hpq : p + b = q) (hpq' : p + a = q') :
      P.d a b ≫ π E K b p q hpq =
        π E K a p q' hpq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.d q' q) := by
    have hh := hπ.2.1 E K a b p q q' (q - a) hab hpq hpq' (by omega)
    simp only [hzero, homMap_zero_left, comp_zero, smul_zero, sub_zero] at hh
    exact hh
  let τ (p : ℤ) : P.sc n ⟶ Q p :=
    { τ₁ := π E K (c.prev n) p (p + c.prev n) rfl
      τ₂ := π E K n p (p + n) rfl
      τ₃ := π E K (c.next n) p (p + c.next n) rfl
      comm₁₂ := (hd (c.prev n) n p (p + n) (p + c.prev n)
        (by rw [hp]; omega) rfl rfl).symm
      comm₂₃ := (hd n (c.next n) p (p + c.next n) (p + n)
        (hn n).symm rfl rfl).symm }
  let t : Fan Q := Fan.mk (P.sc n) τ
  have ht : IsLimit t := by
    apply ShortComplex.isLimitOfIsLimitπ
    · refine (Fan.isLimitMapConeEquiv ShortComplex.π₁ Q t).symm ?_
      change IsLimit (Fan.mk (P.X (c.prev n))
        (fun p ↦ π E K (c.prev n) p (p + c.prev n) rfl))
      exact (hπ.1 E K (c.prev n)).some
    · refine (Fan.isLimitMapConeEquiv ShortComplex.π₂ Q t).symm ?_
      change IsLimit (Fan.mk (P.X n) (fun p ↦ π E K n p (p + n) rfl))
      exact (hπ.1 E K n).some
    · refine (Fan.isLimitMapConeEquiv ShortComplex.π₃ Q t).symm ?_
      change IsLimit (Fan.mk (P.X (c.next n))
        (fun p ↦ π E K (c.next n) p (p + c.next n) rfl))
      exact (hπ.1 E K (c.next n)).some
  obtain ⟨a, b, hs⟩ := hsupp
  have hz (p : ℤ) (hps : p ∉ Finset.Icc a b) : IsZero (Q p) := by
    have hE : IsZero (E.X p) := hs p (by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hps)
    rw [IsZero.iff_id_eq_zero]
    apply ShortComplex.hom_ext
    all_goals exact (homObj_isZero_left (R := R) (E.X p) _ hE).eq_of_src _ _
  have htH := map_finiteSupport_fan (ShortComplex.homologyFunctor _) Q t ht
    (Finset.Icc a b) hz
  let eS (p : ℤ) : K.sc (p + n) ≅
      K.sc' (p + c.prev n) (p + n) (p + c.next n) :=
    K.isoSc' _ _ _ (by rw [hp, hp]; omega) (by rw [hn, hn]; omega)
  let e (p : ℤ) : (Q p).homology ≅
      SheafOfModules.homObj (R := R) (E.X p) (K.homology (p + n)) :=
    ShortComplex.homologyMapIso ((F p).mapShortComplex.mapIso (eS p)).symm ≪≫
      (K.sc (p + n)).mapHomologyIso (F p)
  let g (p q : ℤ) (hpq : p + n = q) :
      P.homology n ⟶ SheafOfModules.homObj (R := R) (E.X p) (K.homology q) := by
    subst q
    exact ShortComplex.homologyMap (τ p) ≫ (e p).hom
  refine ⟨g, ⟨fan_postcompose_iso _ htH e⟩, ?_⟩
  intro p q hpq d hd'
  subst q
  let φ : P.sc n ⟶ (K.sc (p + n)).map (F p) :=
    τ p ≫ (F p).mapShortComplex.map (eS p).inv
  have hφ : φ.τ₂ = π E K n p (p + n) rfl := by
    change π E K n p (p + n) rfl ≫ (F p).map (𝟙 _) = _
    rw [Functor.map_id]
    exact Category.comp_id _
  have heq := exactHomologyMap_cycle_eq (F p) (P.sc n) (K.sc (p + n)) φ d
    (by
      rw [hφ]
      change d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles (p + n)) =
        P.iCycles n ≫ π E K n p (p + n) rfl
      exact hd')
  change d ≫ (F p).map (K.sc (p + n)).homologyπ =
    (P.sc n).homologyπ ≫ ShortComplex.homologyMap (τ p) ≫ (e p).hom
  dsimp only [φ] at heq
  rw [ShortComplex.homologyMap_comp (τ p) ((F p).mapShortComplex.map (eS p).inv)] at heq
  exact heq

end CategoryTheory
