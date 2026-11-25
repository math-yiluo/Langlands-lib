import Langlands.GaloisCohomology.CompactSupport.Internal.ConeSigns
import Langlands.Cohomology.Profinite.Mackey.Cohomology

/-!
# Mapping cocones of squares commuting up to homotopy (internal)

A square `f ≫ β ≃ α ≫ f'` commuting up to a homotopy induces a map of mapping cocones
(`mappingCoconeNat.mapOfHomotopy`), compatible with the projections and the connecting maps, and an
isomorphism in homology when `α` and `β` are (`isIso_homologyMap_mapOfHomotopy`, by the five lemma).
Products on cones of cocycles, and the behaviour of the foundations' conjugation homotopy on cup
products of cochains (`conjHomotopyFun_cupCochain`), are used for the Mackey compatibility of cup
products.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from MackeyFormula/ConeHomotopy.lean
section ConeHomotopy

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

namespace mappingCoconeNat

variable {K L K' L' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  {α : K ⟶ K'} {β : L ⟶ L'}

/-- The components of a homotopy, placed in the shifted factor of the cocone. -/
noncomputable def homotopyShiftF (h : Homotopy (f ≫ β) (α ≫ f')) :
    ∀ n, K.X n ⟶ shiftNegOneX L' n
  | 0 => 0
  | n + 1 => h.hom (n + 1) n

/-- The components of the map of cocones induced by a square commuting up to homotopy. -/
noncomputable def mapOfHomotopyF (h : Homotopy (f ≫ β) (α ≫ f')) (n : ℕ) :
    (mappingCoconeNat f).X n ⟶ (mappingCoconeNat f').X n :=
  ModuleCat.ofHom (((α.f n).hom.comp (LinearMap.fst k _ _)).prod
    ((shiftNegOneMapF β n).hom.comp (LinearMap.snd k _ _) -
      (homotopyShiftF h n).hom.comp (LinearMap.fst k _ _)))

theorem mapOfHomotopyF_comm (h : Homotopy (f ≫ β) (α ≫ f')) (n : ℕ) :
    mapOfHomotopyF h n ≫ (mappingCoconeNat f').d n (n + 1) =
      (mappingCoconeNat f).d n (n + 1) ≫ mapOfHomotopyF h (n + 1) := by
  have hβ : ∀ y : shiftNegOneX L n, (shiftNegOneMapF β (n + 1)).hom ((shiftNegOneD L n).hom y) =
      (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom y) := fun y =>
    (hom_apply_hom_apply_eq_of_comp_eq (shiftNegOneMapF_comm β n) y).symm

  have hcomm : ∀ x : K.X n, shiftNegOneSucc L' n ((β.f n).hom ((f.f n).hom x)) =
      shiftNegOneSucc L' n ((h.hom (n + 1) n).hom ((K.d n (n + 1)).hom x)) -
        (shiftNegOneD L' n).hom ((homotopyShiftF h n).hom x) +
          shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom x)) := fun x => by
    have e := congrArg (fun φ => φ.hom x) (h.comm n)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_add, LinearMap.add_apply] at e
    rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneSucc_apply]
    cases n with
    | zero =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex] at e
      change (β.f 0).hom ((f.f 0).hom x) = (h.hom 1 0).hom ((K.d 0 1).hom x) - 0 +
        (f'.f 0).hom ((α.f 0).hom x)
      rw [e]
      simp
    | succ n =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex] at e
      change (β.f (n + 1)).hom ((f.f (n + 1)).hom x) =
        (h.hom (n + 1 + 1) (n + 1)).hom ((K.d (n + 1) (n + 1 + 1)).hom x) -
          -(L'.d n (n + 1)).hom ((h.hom (n + 1) n).hom x) + (f'.f (n + 1)).hom ((α.f (n + 1)).hom x)
      rw [e]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      abel
  rw [mappingCoconeNat_d, mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (α.comm n (n + 1)) p.1
  · change shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom p.1)) +
        (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom p.2 - (homotopyShiftF h n).hom p.1) =
      (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom p.1) +
        (shiftNegOneD L n).hom p.2) -
          shiftNegOneSucc L' n ((h.hom (n + 1) n).hom ((K.d n (n + 1)).hom p.1))
    rw [map_add, shiftNegOneMapF_succ_apply, hβ, map_sub, hcomm p.1]
    abel

/-- The morphism of mapping cocones induced by a square `f ≫ β ≃ α ≫ f'` commuting up to a
homotopy. -/
noncomputable def mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f')) :
    mappingCoconeNat f ⟶ mappingCoconeNat f' :=
  CochainComplex.ofHom (mapOfHomotopyF h) (mapOfHomotopyF_comm h)

@[reassoc (attr := simp)]
theorem mapOfHomotopy_fst (h : Homotopy (f ≫ β) (α ≫ f')) :
    mapOfHomotopy h ≫ fst f' = fst f ≫ α :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem inr_mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f')) :
    inr f ≫ mapOfHomotopy h = shiftNegOneMap β ≫ inr f' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ ?_)
  · exact (α.f n).hom.map_zero
  · change (shiftNegOneMapF β n).hom y - (homotopyShiftF h n).hom 0 = (shiftNegOneMapF β n).hom y
    rw [map_zero, sub_zero]

section FiveLemma

open HomologicalComplex

theorem homologyδ_naturality_of_inr (Φ : mappingCoconeNat f ⟶ mappingCoconeNat f')
    (hinr : inr f ≫ Φ = shiftNegOneMap β ≫ inr f') (n : ℕ) :
    homologyδ f n ≫ homologyMap Φ (n + 1) = homologyMap β n ≫ homologyδ f' n := by
  rw [homologyδ, homologyδ, Category.assoc, ← homologyMap_comp, hinr, homologyMap_comp,
    shiftNegOneHomologyHom_naturality_assoc]

theorem isIso_homologyMap_of_comm (Φ : mappingCoconeNat f ⟶ mappingCoconeNat f')
    (hfst : Φ ≫ fst f' = fst f ≫ α) (hinr : inr f ≫ Φ = shiftNegOneMap β ≫ inr f')
    (hsq : ∀ n, homologyMap f n ≫ homologyMap β n = homologyMap α n ≫ homologyMap f' n)
    (hα : ∀ n, IsIso (homologyMap α n)) (hβ : ∀ n, IsIso (homologyMap β n)) (n : ℕ) :
    IsIso (homologyMap Φ n) := by
  have bα : ∀ m, Function.Bijective (homologyMap α m).hom := fun m => by
    have := hα m
    exact ConcreteCategory.bijective_of_isIso _
  have bβ : ∀ m, Function.Bijective (homologyMap β m).hom := fun m => by
    have := hβ m
    exact ConcreteCategory.bijective_of_isIso _

  have sfst : ∀ m x, (homologyMap (fst f') m).hom ((homologyMap Φ m).hom x) =
      (homologyMap α m).hom ((homologyMap (fst f) m).hom x) := fun m x =>
    hom_apply_hom_apply_eq_of_comp_eq (by rw [← homologyMap_comp, hfst, homologyMap_comp]) x
  have sδ : ∀ m y, (homologyMap Φ (m + 1)).hom ((homologyδ f m).hom y) =
      (homologyδ f' m).hom ((homologyMap β m).hom y) := fun m y =>
    hom_apply_hom_apply_eq_of_comp_eq (homologyδ_naturality_of_inr Φ hinr m) y
  have sf : ∀ m z, (homologyMap f' m).hom ((homologyMap α m).hom z) =
      (homologyMap β m).hom ((homologyMap f m).hom z) := fun m z =>
    (hom_apply_hom_apply_eq_of_comp_eq (hsq m) z).symm

  have e1 := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₁ f m)
  have e2 := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₂ f m)
  have e3 := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₃ f m)
  have e1' := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₁ f' m)
  have e2' := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₂ f' m)
  have inj_fst0 : ∀ {K₀ L₀ : CochainComplex (ModuleCat.{u} k) ℕ} (g : K₀ ⟶ L₀),
      Function.Injective (homologyMap (fst g) 0).hom := fun g => by
    have := mono_homologyMap_fst_zero g
    exact (ModuleCat.mono_iff_injective _).1 this
  refine @isIso_of_mono_of_epi _ _ _ _ _ _ ((ModuleCat.mono_iff_injective _).2 ?_)
    ((ModuleCat.epi_iff_surjective _).2 ?_)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    cases n with
    | zero =>
      apply inj_fst0 f
      rw [map_zero]
      apply (bα 0).1
      rw [← sfst, hx, map_zero, map_zero]
    | succ m =>
      have h1 : (homologyMap (fst f) (m + 1)).hom x = 0 := by
        apply (bα (m + 1)).1
        rw [← sfst, hx, map_zero, map_zero]
      obtain ⟨y, rfl⟩ := e2 m x h1
      have h2 : (homologyδ f' m).hom ((homologyMap β m).hom y) = 0 := by
        rw [← sδ]
        exact hx
      obtain ⟨z', hz'⟩ := e1' m _ h2
      obtain ⟨z, rfl⟩ := (bα m).2 z'
      have h3 : (homologyMap f m).hom z = y := by
        apply (bβ m).1
        rw [← sf]
        exact hz'
      change (homologyδ f m).hom y = 0
      rw [← h3]
      exact hom_apply_hom_apply_of_comp_eq (homologyMap_homologyδ f m) z
  · intro y'
    cases n with
    | zero =>
      obtain ⟨w, hw⟩ := (bα 0).2 ((homologyMap (fst f') 0).hom y')
      have h1 : (homologyMap f 0).hom w = 0 := by
        apply (bβ 0).1
        rw [← sf, hw, map_zero]
        exact hom_apply_hom_apply_of_comp_eq (homologyMap_fst_homologyMap f' 0) y'
      obtain ⟨x, rfl⟩ := e3 0 w h1
      refine ⟨x, inj_fst0 f' ?_⟩
      rw [sfst]
      exact hw
    | succ m =>
      obtain ⟨w, hw⟩ := (bα (m + 1)).2 ((homologyMap (fst f') (m + 1)).hom y')
      have h1 : (homologyMap f (m + 1)).hom w = 0 := by
        apply (bβ (m + 1)).1
        rw [← sf, hw, map_zero]
        exact hom_apply_hom_apply_of_comp_eq (homologyMap_fst_homologyMap f' (m + 1)) y'
      obtain ⟨x, rfl⟩ := e3 (m + 1) w h1
      have h2 : (homologyMap (fst f') (m + 1)).hom (y' - (homologyMap Φ (m + 1)).hom x) = 0 := by
        rw [map_sub, sfst, hw, sub_self]
      obtain ⟨u', hu'⟩ := e2' m _ h2
      obtain ⟨u, rfl⟩ := (bβ m).2 u'
      refine ⟨x + (homologyδ f m).hom u, ?_⟩
      rw [map_add, sδ]
      rw [show (homologyδ f' m).hom ((homologyMap β m).hom u) =
        y' - (homologyMap Φ (m + 1)).hom x from hu']
      abel

theorem isIso_homologyMap_mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f'))
    (hα : ∀ n, IsIso (homologyMap α n)) (hβ : ∀ n, IsIso (homologyMap β n)) (n : ℕ) :
    IsIso (homologyMap (mapOfHomotopy h) n) :=
  isIso_homologyMap_of_comm _ (mapOfHomotopy_fst h) (inr_mapOfHomotopy h)
    (fun m => by rw [← homologyMap_comp, ← homologyMap_comp, h.homologyMap_eq]) hα hβ n

end FiveLemma

end mappingCoconeNat

end ConeHomotopy

-- from PoincarePairs/ConeProduct.lean
section ConeProduct

noncomputable section


open CategoryTheory


variable {k : Type u} [CommRing k]

namespace mappingCoconeNat

section Cocycles

variable {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

theorem f_fst_eq_d_snd_of_d_eq_zero {n : ℕ} (p : (mappingCoconeNat f).X (n + 1))
    (hp : ((mappingCoconeNat f).d (n + 1) (n + 1 + 1)).hom p = 0) :
    (f.f (n + 1)).hom p.1 = (L.d n (n + 1)).hom (p.2 : L.X n) := by
  rw [mappingCoconeNat_d] at hp
  have h2 := congrArg Prod.snd hp
  change ((f.f (n + 1)).hom p.1 : L.X (n + 1)) + -(L.d n (n + 1)).hom (p.2 : L.X n) = 0 at h2
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem f_fst_eq_zero_of_d_eq_zero (p : (mappingCoconeNat f).X 0)
    (hp : ((mappingCoconeNat f).d 0 1).hom p = 0) :
    (f.f 0).hom p.1 = 0 := by
  rw [mappingCoconeNat_d] at hp
  have h2 := congrArg Prod.snd hp
  change ((f.f 0).hom p.1 : L.X 0) + 0 = 0 at h2
  rwa [add_zero] at h2

end Cocycles

section Product

variable {KA LA KC LC N LN KA' LA' KC' LC' N' LN' : CochainComplex (ModuleCat.{u} k) ℕ}
  {fA : KA ⟶ LA} {fC : KC ⟶ LC} {ρ : N ⟶ LN}
  {fA' : KA' ⟶ LA'} {fC' : KC' ⟶ LC'} {ρ' : N' ⟶ LN'}
  {αA : KA ⟶ KA'} {βA : LA ⟶ LA'} {αC : KC ⟶ KC'} {βC : LC ⟶ LC'} {αN : N ⟶ N'}
  {βN : LN ⟶ LN'}
  (hA : Homotopy (fA ≫ βA) (αA ≫ fA')) (hC : Homotopy (fC ≫ βC) (αC ≫ fC'))
  (hN : Homotopy (ρ ≫ βN) (αN ≫ ρ'))
  (μL : LeibnizPairing LA LN LC) (μK : LeibnizPairing KA N KC)
  (μL' : LeibnizPairing LA' LN' LC') (μK' : LeibnizPairing KA' N' KC')

include hN in

theorem homotopy_apply_zero_of_d_eq_zero (z : N.X 0) (hz : (N.d 0 1).hom z = 0) :
    (βN.f 0).hom ((ρ.f 0).hom z) = (ρ'.f 0).hom ((αN.f 0).hom z) := by
  have e := congrArg (fun φ => φ.hom z) (hN.comm 0)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply] at e
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex] at e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero, ModuleCat.hom_zero,
    LinearMap.zero_apply, zero_add] at e
  exact e

theorem homotopy_apply_succ_of_d_eq_zero (l : ℕ) (z : N.X (l + 1))
    (hz : (N.d (l + 1) (l + 1 + 1)).hom z = 0) :
    (βN.f (l + 1)).hom ((ρ.f (l + 1)).hom z) =
      (LN'.d l (l + 1)).hom ((hN.hom (l + 1) l).hom z) + (ρ'.f (l + 1)).hom ((αN.f (l + 1)).hom z) := by
  have e := congrArg (fun φ => φ.hom z) (hN.comm (l + 1))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply] at e
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex] at e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero, zero_add] at e
  exact e

theorem snd_sub_eq_neg_d (hβ : ∀ {r s n : ℕ} (h : r + s = n) (y : LA.X r) (w : LN.X s),
      (βC.f n).hom (μL.μ h y w) = μL'.μ h ((βA.f r).hom y) ((βN.f s).hom w))
    (hh : ∀ {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1) (x : KA.X (r + 1)) (z : N.X (s + 1)),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show r + (s + 1) = m by omega) ((hA.hom (r + 1) r).hom x)
            ((ρ'.f (s + 1)).hom ((αN.f (s + 1)).hom z)) +
          (-1 : k) ^ (r + 1) • μL'.μ (show r + 1 + s = m by omega)
            ((βA.f (r + 1)).hom ((fA.f (r + 1)).hom x)) ((hN.hom (s + 1) s).hom z))
    (j l : ℕ) (h : j + 1 + (l + 1) = j + l + 1 + 1) (a : KA.X (j + 1)) (b : LA.X j)
    (z : N.X (l + 1)) (hab : (fA.f (j + 1)).hom a = (LA.d j (j + 1)).hom b)
    (hz : (N.d (l + 1) (l + 1 + 1)).hom z = 0) :
    (βC.f (j + l + 1)).hom (μL.μ (show j + (l + 1) = j + l + 1 by omega) b ((ρ.f (l + 1)).hom z)) -
        (hC.hom (j + l + 1 + 1) (j + l + 1)).hom (μK.μ h a z) -
        μL'.μ (show j + (l + 1) = j + l + 1 by omega)
          ((βA.f j).hom b - (hA.hom (j + 1) j).hom a) ((ρ'.f (l + 1)).hom ((αN.f (l + 1)).hom z)) =
      -(LC'.d (j + l) (j + l + 1)).hom ((-1 : k) ^ (j + 1) •
        μL'.μ (show j + l = j + l from rfl) ((βA.f j).hom b) ((hN.hom (l + 1) l).hom z)) := by
  rw [hβ, homotopy_apply_succ_of_d_eq_zero hN l z hz, hh h a z, map_smul, μL'.leibniz,
    hom_apply_hom_apply_eq_of_comp_eq (βA.comm j (j + 1)) b, ← hab]
  simp only [map_add, map_sub, LinearMap.sub_apply, smul_add, smul_smul, ← pow_add]
  have e : (-1 : k) ^ (j + 1 + j) = -1 := by
    rw [show j + 1 + j = 2 * j + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [e, neg_one_smul]
  abel

theorem _root_.Langlands.GaloisCohomology.homologyπ_eq_of_iCycles_sub_eq_d (P : CochainComplex (ModuleCat.{u} k) ℕ)
    {m : ℕ} (a b : P.cycles (m + 1)) (c : P.X m)
    (h : (P.iCycles (m + 1)).hom a - (P.iCycles (m + 1)).hom b = (P.d m (m + 1)).hom c) :
    (P.homologyπ (m + 1)).hom a = (P.homologyπ (m + 1)).hom b := by
  have e : a - b = (P.toCycles m (m + 1)).hom c :=
    iCycles_hom_injective P (m + 1) (by rw [map_sub, h, iCycles_toCycles_hom_apply])
  rw [← sub_eq_zero, ← map_sub, e, homologyπ_toCycles_hom_apply]

theorem homologyMap_mapOfHomotopy_coconeLeft
    (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (z : N.X s),
      (fC.f n).hom (μK.μ h x z) = μL.μ h ((fA.f r).hom x) ((ρ.f s).hom z))
    (hc' : ∀ {r s n : ℕ} (h : r + s = n) (x : KA'.X r) (z : N'.X s),
      (fC'.f n).hom (μK'.μ h x z) = μL'.μ h ((fA'.f r).hom x) ((ρ'.f s).hom z))
    (hα : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (z : N.X s),
      (αC.f n).hom (μK.μ h x z) = μK'.μ h ((αA.f r).hom x) ((αN.f s).hom z))
    (hβ : ∀ {r s n : ℕ} (h : r + s = n) (y : LA.X r) (w : LN.X s),
      (βC.f n).hom (μL.μ h y w) = μL'.μ h ((βA.f r).hom y) ((βN.f s).hom w))
    (hh : ∀ {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1) (x : KA.X (r + 1)) (z : N.X (s + 1)),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show r + (s + 1) = m by omega) ((hA.hom (r + 1) r).hom x)
            ((ρ'.f (s + 1)).hom ((αN.f (s + 1)).hom z)) +
          (-1 : k) ^ (r + 1) • μL'.μ (show r + 1 + s = m by omega)
            ((βA.f (r + 1)).hom ((fA.f (r + 1)).hom x)) ((hN.hom (s + 1) s).hom z))
    (hh₀ : ∀ {s m : ℕ} (h : 0 + (s + 1) = m + 1) (x : KA.X 0) (z : N.X (s + 1)),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show 0 + s = m by omega) ((βA.f 0).hom ((fA.f 0).hom x)) ((hN.hom (s + 1) s).hom z))
    (hh₁ : ∀ {r m : ℕ} (h : r + 1 + 0 = m + 1) (x : KA.X (r + 1)) (z : N.X 0),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show r + 0 = m by omega) ((hA.hom (r + 1) r).hom x)
          ((ρ'.f 0).hom ((αN.f 0).hom z)))
    {r s n : ℕ} (h : r + s = n) (x : (mappingCoconeNat fA).homology r) (z : N.homology s) :
    (HomologicalComplex.homologyMap (mapOfHomotopy hC) n).hom
        ((LeibnizPairing.coconeLeft μL ρ μK hc).homology h x z) =
      (LeibnizPairing.coconeLeft μL' ρ' μK' hc').homology h
        ((HomologicalComplex.homologyMap (mapOfHomotopy hA) r).hom x)
        ((HomologicalComplex.homologyMap αN s).hom z) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨z, rfl⟩ := homologyπ_hom_surjective _ s z
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  have hx := iCycles_d_apply _ r (r + 1) x
  have hz := iCycles_d_apply _ s (s + 1) z
  have eL : ((mappingCoconeNat fC').iCycles n).hom (HomologicalComplex.cyclesMap
      (mapOfHomotopy hC) n ((LeibnizPairing.coconeLeft μL ρ μK hc).cycles h x z)) =
      (mapOfHomotopyF hC n).hom (LeibnizPairing.coconeLeftμ μL ρ μK h
        (((mappingCoconeNat fA).iCycles r).hom x) ((N.iCycles s).hom z)) := by
    rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles]
    rfl
  have eR : ((mappingCoconeNat fC').iCycles n).hom
      ((LeibnizPairing.coconeLeft μL' ρ' μK' hc').cycles h
        (HomologicalComplex.cyclesMap (mapOfHomotopy hA) r x)
        (HomologicalComplex.cyclesMap αN s z)) =
      LeibnizPairing.coconeLeftμ μL' ρ' μK' h
        ((mapOfHomotopyF hA r).hom (((mappingCoconeNat fA).iCycles r).hom x))
        ((αN.f s).hom ((N.iCycles s).hom z)) := by
    rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
    rfl
  generalize ((mappingCoconeNat fA).iCycles r).hom x = p at hx eL eR
  generalize (N.iCycles s).hom z = w at hz eL eR
  revert p
  intro (p : KA.X r × shiftNegOneX LA r) hx eL eR
  obtain ⟨a, b⟩ := p
  rcases n with _ | m
  · obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := by omega
    congr 1
    apply iCycles_hom_injective
    rw [eL, eR]
    exact Prod.ext (hα h a w) (Subsingleton.elim (α := PUnit) _ _)
  · rcases r with _ | j
    · obtain rfl : s = m + 1 := by omega
      refine homologyπ_eq_of_iCycles_sub_eq_d _ _ _ 0 ?_
      rw [map_zero, sub_eq_zero, eL, eR]
      refine Prod.ext (hα h a w) ?_
      change (βC.f m).hom 0 - (hC.hom (m + 1) m).hom (μK.μ h a w) = 0
      rw [map_zero, zero_sub, neg_eq_zero, hh₀ h, f_fst_eq_zero_of_d_eq_zero fA (a, b) hx, map_zero,
        map_zero, LinearMap.zero_apply]
    · rcases s with _ | l
      · obtain rfl : m = j := by omega
        obtain ⟨b', rfl⟩ : ∃ b' : LA.X m, b' = b := ⟨b, rfl⟩
        refine homologyπ_eq_of_iCycles_sub_eq_d _ _ _ 0 ?_
        rw [map_zero, sub_eq_zero, eL, eR]
        refine Prod.ext (hα h a w) ?_
        change (βC.f m).hom (μL.μ (show m + 0 = m by omega) b' ((ρ.f 0).hom w)) -
            (hC.hom (m + 1) m).hom (μK.μ h a w) =
          μL'.μ (show m + 0 = m by omega) ((βA.f m).hom b' - (hA.hom (m + 1) m).hom a)
            ((ρ'.f 0).hom ((αN.f 0).hom w))
        rw [hβ, homotopy_apply_zero_of_d_eq_zero hN w hz, hh₁ h, map_sub, LinearMap.sub_apply]
      · obtain rfl : m = j + l + 1 := by omega
        obtain ⟨b', rfl⟩ : ∃ b' : LA.X j, b' = b := ⟨b, rfl⟩
        refine homologyπ_eq_of_iCycles_sub_eq_d _ _ _ ((0 : KC'.X (j + l + 1)), ((-1 : k) ^ (j + 1) •
          μL'.μ (show j + l = j + l from rfl) ((βA.f j).hom b')
            ((hN.hom (l + 1) l).hom w) : LC'.X (j + l))) ?_
        rw [eL, eR, mappingCoconeNat_d]
        refine Prod.ext ?_ ?_
        · change (αC.f _).hom (μK.μ h a w) - μK'.μ h ((αA.f _).hom a) ((αN.f _).hom w) =
            (KC'.d _ _).hom 0
          rw [map_zero, hα, sub_self]
        · change (βC.f (j + l + 1)).hom (μL.μ (show j + (l + 1) = j + l + 1 by omega)
                b' ((ρ.f (l + 1)).hom w)) -
              (hC.hom (j + l + 1 + 1) (j + l + 1)).hom (μK.μ h a w) -
              μL'.μ (show j + (l + 1) = j + l + 1 by omega)
                ((βA.f j).hom b' - (hA.hom (j + 1) j).hom a)
                ((ρ'.f (l + 1)).hom ((αN.f (l + 1)).hom w)) =
            (fC'.f (j + l + 1)).hom 0 + -(LC'.d (j + l) (j + l + 1)).hom ((-1 : k) ^ (j + 1) •
              μL'.μ (show j + l = j + l from rfl) ((βA.f j).hom b')
                ((hN.hom (l + 1) l).hom w))
          rw [map_zero, zero_add]
          exact snd_sub_eq_neg_d hA hC hN μL μK μL' hβ hh j l h a b' w
            (f_fst_eq_d_snd_of_d_eq_zero fA (a, b') hx) hz

end Product

end mappingCoconeNat

end

end ConeProduct

-- from PoincarePairs/ConjHomotopyFunCupCochainZeroRight.lean
section ConjHomotopyFunCupCochainZeroRight

noncomputable section


open CategoryTheory MonoidalCategory TensorProduct Finset Langlands.ProfiniteCohomology.GroupCoh


section Sequences

variable {Γ : Type*} [Group Γ]

/-- The partial products `F 0 * F 1 * ⋯` of a sequence in a group (`seqProd F 0 = 1`). -/
def seqProd (F : ℕ → Γ) : ℕ → Γ
  | 0 => 1
  | r + 1 => seqProd F r * F r

theorem seqProd_succ (F : ℕ → Γ) (r : ℕ) : seqProd F (r + 1) = seqProd F r * F r :=
  rfl

theorem partialProd_seqTuple {n : ℕ} (F : ℕ → Γ) (r : ℕ) (hr : r < n + 1) :
    Fin.partialProd (seqTuple n F) ⟨r, hr⟩ = seqProd F r := by
  induction r with
  | zero => exact Fin.partialProd_zero _
  | succ r ih =>
    have h1 := Fin.partialProd_succ (seqTuple n F) ⟨r, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1
    rw [h1, ih (by omega), seqProd_succ]
    rfl

theorem seqProd_prismSeq_of_ge (g : Γ) {i r : ℕ} (hr : r ≤ i) (F : ℕ → Γ) :
    seqProd (prismSeq g i F) r = seqProd F r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [seqProd_succ, seqProd_succ, ih (by omega)]
    simp only [prismSeq, ite_eq_left (show r < i by omega)]

theorem seqProd_prismSeq_of_le (g : Γ) {i r : ℕ} (hi : i ≤ r) (F : ℕ → Γ) :
    seqProd (prismSeq g i F) (r + 1) = seqProd F r * g := by
  induction r with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [seqProd, prismSeq]
  | succ r ih =>
    rcases Nat.lt_or_ge i (r + 1) with h | h
    · rw [seqProd_succ, ih (by omega), seqProd_succ]
      simp only [prismSeq, ite_eq_right (show ¬ r + 1 < i by omega), ite_eq_right (show r + 1 ≠ i by omega),
        Nat.add_sub_cancel]
      group
    · obtain rfl : i = r + 1 := by omega
      rw [seqProd_succ, seqProd_prismSeq_of_ge g le_rfl, seqProd_succ]
      simp [prismSeq]

end Sequences

section Cup

variable {k Γ : Type u} [CommRing k] [Group Γ] {A B : Rep.{u} k Γ}

theorem cupCochain_seqTuple {r s n : ℕ} (h : r + s = n) (F : (Fin r → Γ) → A)
    (E : (Fin s → Γ) → B) (Y : ℕ → Γ) :
    cupCochain h F E (seqTuple n Y) =
      F (seqTuple r Y) ⊗ₜ[k] B.ρ (seqProd Y r) (E (seqTuple s fun l => Y (r + l))) := by
  rw [cupCochain_apply, partialProd_seqTuple]
  rfl

theorem cupCochain_seqTuple_prismSeq_of_le (g : Γ) {r s n : ℕ} (h : r + 1 + s = n)
    (F : (Fin (r + 1) → Γ) → A) (E : (Fin s → Γ) → B) (Y : ℕ → Γ) {i : ℕ} (hi : i ≤ r) :
    cupCochain h F E (seqTuple n (prismSeq g i Y)) =
      F (seqTuple (r + 1) (prismSeq g i Y)) ⊗ₜ[k] B.ρ (seqProd Y r)
        (conjCochainFun B g E (seqTuple s fun l => Y (r + l))) := by
  rw [cupCochain_seqTuple, seqProd_prismSeq_of_le g hi, map_mul, Module.End.mul_apply]
  congr 2
  change B.ρ g (E _) = B.ρ g (E _)
  congr 2
  funext l
  change prismSeq g i Y (r + 1 + l) = g⁻¹ * Y (r + l) * g
  simp only [prismSeq, ite_eq_right (show ¬ r + 1 + l < i by omega),
    ite_eq_right (show r + 1 + (l : ℕ) ≠ i by omega)]
  congr 3
  omega

theorem cupCochain_seqTuple_prismSeq_add (g : Γ) {r s n : ℕ} (h : r + (s + 1) = n)
    (F : (Fin r → Γ) → A) (E : (Fin (s + 1) → Γ) → B) (Y : ℕ → Γ) (j : ℕ) :
    cupCochain h F E (seqTuple n (prismSeq g (r + j) Y)) =
      F (seqTuple r Y) ⊗ₜ[k] B.ρ (seqProd Y r)
        (E (seqTuple (s + 1) (prismSeq g j fun l => Y (r + l)))) := by
  rw [cupCochain_seqTuple, seqProd_prismSeq_of_ge g (by omega)]
  congr 1
  · congr 1
    exact seqTuple_congr fun l hl => by simp only [prismSeq, ite_eq_left (show l < r + j by omega)]
  · congr 2
    refine seqTuple_congr fun l hl => ?_
    simp only [prismSeq]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first | omega | rfl | (rw [show r + l - 1 = r + (l - 1) by omega])

end Cup

section Leibniz

variable {k Γ : Type u} [CommRing k] [Group Γ] {A B : Rep.{u} k Γ}

theorem conjHomotopyFun_cupCochain (g : Γ) {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1)
    (F : (Fin (r + 1) → Γ) → A) (E : (Fin (s + 1) → Γ) → B) :
    conjHomotopyFun (A ⊗ B) g m (cupCochain h F E) =
      cupCochain (show r + (s + 1) = m by omega) (conjHomotopyFun A g r F) (conjCochainFun B g E) +
        (-1 : k) ^ (r + 1) • cupCochain (show r + 1 + s = m by omega) F (conjHomotopyFun B g s E) := by
  obtain rfl : m = r + 1 + s := by omega
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set Y := tupleSeq γ
  rw [Pi.add_apply, Pi.smul_apply, conjHomotopyFun_seqTuple, cupCochain_seqTuple,
    cupCochain_seqTuple, conjHomotopyFun_seqTuple, conjHomotopyFun_seqTuple,
    show range (r + 1 + s + 1) = range ((r + 1) + (s + 1)) from rfl, sum_range_add]
  congr 1
  · rw [sum_tmul]
    refine sum_congr rfl fun i hi => ?_
    rw [cupCochain_seqTuple_prismSeq_of_le g h F E Y (by simp at hi; omega), smul_tmul']
  · rw [map_sum, tmul_sum, smul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [cupCochain_seqTuple_prismSeq_add g h F E Y j, map_smul, tmul_smul, smul_smul, pow_add]

theorem conjHomotopyFun_cupCochain_zero_left (g : Γ) {s m : ℕ} (h : 0 + (s + 1) = m + 1)
    (F : (Fin 0 → Γ) → A) (E : (Fin (s + 1) → Γ) → B) :
    conjHomotopyFun (A ⊗ B) g m (cupCochain h F E) =
      cupCochain (show 0 + s = m by omega) F (conjHomotopyFun B g s E) := by
  obtain rfl : m = s := by omega
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set Y := tupleSeq γ
  rw [conjHomotopyFun_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, map_sum, tmul_sum]
  refine sum_congr rfl fun j _ => ?_
  have e := cupCochain_seqTuple_prismSeq_add g h F E Y j
  rw [zero_add] at e
  rw [e, map_smul, tmul_smul]

theorem conjHomotopyFun_cupCochain_zero_right (g : Γ) {r m : ℕ} (h : r + 1 + 0 = m + 1)
    (F : (Fin (r + 1) → Γ) → A) (E : (Fin 0 → Γ) → B) :
    conjHomotopyFun (A ⊗ B) g m (cupCochain h F E) =
      cupCochain (show r + 0 = m by omega) (conjHomotopyFun A g r F) (conjCochainFun B g E) := by
  obtain rfl : m = r := by omega
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set Y := tupleSeq γ
  rw [conjHomotopyFun_seqTuple, cupCochain_seqTuple, conjHomotopyFun_seqTuple, sum_tmul]
  refine sum_congr rfl fun i hi => ?_
  rw [cupCochain_seqTuple_prismSeq_of_le g h F E Y (by simp at hi; omega), smul_tmul']

end Leibniz

end

end ConjHomotopyFunCupCochainZeroRight

end Langlands.GaloisCohomology
