import Langlands.Cohomology.Profinite.Duality.Devissage

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory

universe u

section MapAlongEquiv

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem bijective_map_of_mulEquiv (e : H ≃* G) (he : Continuous e.toMonoidHom)
    (he' : Continuous e.symm.toMonoidHom) {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A]
    [IsSmoothRep B] (f : Rep.res e.toMonoidHom A ⟶ B) (g : Rep.res e.symm.toMonoidHom B ⟶ A)
    (hgf : ∀ a : A, g.hom (f.hom a) = a) (hfg : ∀ b : B, f.hom (g.hom b) = b) (n : ℕ) :
    Function.Bijective (map ⟨e.toMonoidHom, he⟩ f n).hom := by
  have h1 : map ⟨e.toMonoidHom, he⟩ f n ≫
      map ⟨e.symm.toMonoidHom, he'⟩ g n = 𝟙 _ := by
    rw [← map_comp]
    exact map_eq_id _ (by ext x; exact e.apply_symm_apply x) (fun a => hgf a) n
  have h2 : map ⟨e.symm.toMonoidHom, he'⟩ g n ≫
      map ⟨e.toMonoidHom, he⟩ f n = 𝟙 _ := by
    rw [← map_comp]
    exact map_eq_id _ (by ext x; exact e.symm_apply_apply x) (fun b => hfg b) n
  have e1 : ∀ x, (map ⟨e.symm.toMonoidHom, he'⟩ g n).hom
      ((map ⟨e.toMonoidHom, he⟩ f n).hom x) = x := fun x =>
    congrArg (fun φ => φ.hom x) h1
  have e2 : ∀ y, (map ⟨e.toMonoidHom, he⟩ f n).hom
      ((map ⟨e.symm.toMonoidHom, he'⟩ g n).hom y) = y := fun y =>
    congrArg (fun φ => φ.hom y) h2
  exact ⟨Function.LeftInverse.injective e1, Function.RightInverse.surjective e2⟩

end MapAlongEquiv

section OpenSubgroupOf

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in

theorem exists_eq_openSubgroupOf (U : OpenSubgroup G) (W : OpenSubgroup (U : Subgroup G)) :
    ∃ V : OpenSubgroup G, V ≤ U ∧ W = openSubgroupOf U V := by
  let V : OpenSubgroup G :=
    { toSubgroup := (W : Subgroup (U : Subgroup G)).map (U : Subgroup G).subtype
      isOpen' := by
        change IsOpen (Subtype.val '' (W : Set (U : Subgroup G)))
        exact U.isOpen.isOpenMap_subtype_val _ W.isOpen }
  refine ⟨V, fun x hx => ?_, ?_⟩
  · exact Subgroup.map_subtype_le (W : Subgroup (U : Subgroup G)) hx
  · apply OpenSubgroup.toSubgroup_injective
    change (W : Subgroup (U : Subgroup G)) =
      ((W : Subgroup (U : Subgroup G)).map (U : Subgroup G).subtype).subgroupOf U
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm

end OpenSubgroupOf

section Transport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {n : ℕ} {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]

namespace DualizingData

variable (H : DualizingData n D)

abbrev fromSubgroupOf {U V : OpenSubgroup G} (hVU : V ≤ U) (C : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep C] (m : ℕ) :=
  map (subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU)) (resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) C) m

omit [CompactSpace G] in
theorem bijective_fromSubgroupOf {U V : OpenSubgroup G} (hVU : V ≤ U) (C : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep C] (m : ℕ) : Function.Bijective (fromSubgroupOf hVU C m).hom :=
  bijective_map_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm
    (continuous_subgroupOfEquivOfLe_symm (show (V : Subgroup G) ≤ U from hVU))
    (continuous_subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU))
    (resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) C)
    (resSubgroupOfInvHom (show (V : Subgroup G) ≤ U from hVU) C) (fun _ => rfl) (fun _ => rfl) m

include H in

theorem t_cores_openSubgroupOf (U V : OpenSubgroup G) (hVU : V ≤ U)
    (z : cohomology (Rep.res (openSubgroupOf U V : Subgroup (U : Subgroup G)).subtype
      (Rep.res (U : Subgroup G).subtype D)) 2) :
    H.t U ((cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom z) =
      H.t V ((fromSubgroupOf hVU D 2).hom z) := by
  rw [← H.t_cores U V hVU, coresOfLE_eq]
  congr 1
  have h := congrArg (fun φ => φ.hom z)
    (map_resSubgroupOfHom_comp (show (V : Subgroup G) ≤ U from hVU) D 2)
  change (cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom z =
    (cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom
      ((map (subgroupOfEquivOfLeHom (show (V : Subgroup G) ≤ U from hVU))
          (resSubgroupOfInvHom _ D) 2).hom ((fromSubgroupOf hVU D 2).hom z))
  congr 1
  exact h.symm

include H in

theorem bijective_t_cores_openSubgroupOf (U V : OpenSubgroup G) (hVU : V ≤ U) :
    Function.Bijective ((H.t U).toAddMonoidHom.comp
      (cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom.toAddMonoidHom) := by
  have hfun : ⇑((H.t U).toAddMonoidHom.comp
      (cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype D) 2).hom.toAddMonoidHom) =
      (H.t V) ∘ (fromSubgroupOf hVU D 2).hom := by
    funext z
    exact H.t_cores_openSubgroupOf U V hVU z
  rw [hfun]
  exact (H.t V).bijective.comp (bijective_fromSubgroupOf hVU D 2)

end DualizingData

end Transport

section Perfect

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {n : ℕ} {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]

namespace DualizingData

variable (H : DualizingData n D)

omit [IsTopologicalGroup G] [CompactSpace G] [IsSmoothRep D] in
variable (n) in

def zmodSubgroupOfHom {U V : OpenSubgroup G} (hVU : V ≤ U) :
    Rep.res (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm.toMonoidHom
      (zmodRep.{u} ((V : Subgroup G).subgroupOf U) n) ⟶ zmodRep.{u} (V : Subgroup G) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [IsTopologicalGroup G] [CompactSpace G] [IsSmoothRep D] in
variable (n) in

def zmodSubgroupOfInvHom {U V : OpenSubgroup G} (hVU : V ≤ U) :
    Rep.res (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).toMonoidHom
      (zmodRep.{u} (V : Subgroup G) n) ⟶ zmodRep.{u} ((V : Subgroup G).subgroupOf U) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [CompactSpace G] [IsSmoothRep D] in
theorem bijective_zmodFromSubgroupOf {U V : OpenSubgroup G} (hVU : V ≤ U) (m : ℕ) :
    Function.Bijective (map
      (subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU)) (zmodSubgroupOfHom n hVU) m).hom :=
  bijective_map_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU)).symm
    (continuous_subgroupOfEquivOfLe_symm (show (V : Subgroup G) ≤ U from hVU))
    (continuous_subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from hVU))
    (zmodSubgroupOfHom n hVU) (zmodSubgroupOfInvHom n hVU) (fun _ => rfl) (fun _ => rfl) m

omit [IsTopologicalGroup G] [CompactSpace G] [IsSmoothRep D] in

theorem resFunctor_map_zmodMulPairing_comp {U V : OpenSubgroup G} (hVU : V ≤ U)
    (hD : ∀ d : D, n • d = 0) :
    (Rep.resFunctor
        ((subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU) :
            (V : Subgroup G) →ₜ* (V : Subgroup G).subgroupOf U) :
          (V : Subgroup G) →* (V : Subgroup G).subgroupOf U)).map
        (zmodMulPairing n (Rep.res ((V : Subgroup G).subgroupOf U).subtype
          (Rep.res (U : Subgroup G).subtype D)) hD) ≫
        resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) D =
      resTensorHom
          ((subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU) :
              (V : Subgroup G) →ₜ* (V : Subgroup G).subgroupOf U) :
            (V : Subgroup G) →* (V : Subgroup G).subgroupOf U)
          (zmodSubgroupOfHom n hVU) (resSubgroupOfHom (show (V : Subgroup G) ≤ U from hVU) D) ≫
        zmodMulPairing n (Rep.res (V : Subgroup G).subtype D) hD := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a d => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [CompactSpace G] in

set_option backward.isDefEq.respectTransparency false in
-- The restriction functor is applied along `(subgroupOfEquivOfLe _).symm.toMonoidHom` and along
-- the coercion of its bundled version; the two are definitionally, not reducibly, equal.
theorem fromSubgroupOf_cupPairing {U V : OpenSubgroup G} (hVU : V ≤ U) (hD : ∀ d : D, n • d = 0)
    (a : cohomology (zmodRep.{u} ((V : Subgroup G).subgroupOf U) n) 1)
    (b : cohomology (Rep.res ((V : Subgroup G).subgroupOf U).subtype
      (Rep.res (U : Subgroup G).subtype D)) 1) :
    fromSubgroupOf hVU D 2 (cupPairing (zmodMulPairing n (Rep.res ((V : Subgroup G).subgroupOf U).subtype
        (Rep.res (U : Subgroup G).subtype D)) hD) (show 1 + 1 = 2 from rfl) a b) =
      cupPairing (zmodMulPairing n (Rep.res (V : Subgroup G).subtype D) hD) (show 1 + 1 = 2 from rfl)
        (map
          (subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU)) (zmodSubgroupOfHom n hVU) 1 a)
        (fromSubgroupOf hVU D 1 b) := by
  rw [cupPairing_apply, cupPairing_apply, map_coeffMap, resFunctor_map_zmodMulPairing_comp hVU hD,
    ← cohomologyMap_map, map_resTensorHom_cup]

include H in

theorem isPerfectPairing_openSubgroupOf (U V : OpenSubgroup G) (hVU : V ≤ U) :
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (openSubgroupOf U V :
        Subgroup (U : Subgroup G)).subtype (Rep.res (U : Subgroup G).subtype D))
        (nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      ((H.t U).toAddMonoidHom.comp (cores (openSubgroupOf U V)
        (Rep.res (U : Subgroup G).subtype D) 2).hom.toAddMonoidHom) := by
  obtain ⟨P₁, P₂⟩ := H.isPerfectPairing V
  have hD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have key : ∀ a b, (H.t U) ((cores (openSubgroupOf U V)
      (Rep.res (U : Subgroup G).subtype D) 2).hom
        (cupPairing (zmodMulPairing n (Rep.res ((V : Subgroup G).subgroupOf U).subtype
          (Rep.res (U : Subgroup G).subtype D)) hD) (show 1 + 1 = 2 from rfl) a b)) =
      H.t V (cupPairing (zmodMulPairing n (Rep.res (V : Subgroup G).subtype D) hD)
        (show 1 + 1 = 2 from rfl)
        ((map
          (subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU)) (zmodSubgroupOfHom n hVU) 1).hom a)
        ((fromSubgroupOf hVU D 1).hom b)) := by
    intro a b
    rw [H.t_cores_openSubgroupOf U V hVU]
    exact congrArg (H.t V) (fromSubgroupOf_cupPairing hVU hD a b)
  constructor
  · exact bijective_of_bijective_comp P₁ (bijective_zmodFromSubgroupOf hVU 1)
      (γ := (fromSubgroupOf hVU D 1).hom.toAddMonoidHom) (bijective_fromSubgroupOf hVU D 1)
      (fun a b => key a b)
  · exact bijective_of_bijective_comp P₂ (bijective_fromSubgroupOf hVU D 1)
      (γ := (map
          (subgroupOfEquivOfLeSymmHom (show (V : Subgroup G) ≤ U from hVU)) (zmodSubgroupOfHom n hVU) 1).hom.toAddMonoidHom)
      (bijective_zmodFromSubgroupOf hVU 1) (fun b a => key a b)

include H in

theorem groupDualityHypotheses (U : OpenSubgroup G) :
    GroupDualityHypotheses n (Rep.res (U : Subgroup G).subtype D) (H.t U).toAddMonoidHom where
  nonempty_addEquiv := H.nonempty_addEquiv
  finite_two M _ _ hM := H.finite_cohomology U M hM 2 le_rfl
  subsingleton_three M _ _ hM := H.subsingleton_cohomology_three U M hM
  bijective_cores W := by
    obtain ⟨V, hVU, rfl⟩ := exists_eq_openSubgroupOf U W
    exact H.bijective_t_cores_openSubgroupOf U V hVU
  isPerfectPairing W := by
    obtain ⟨V, hVU, rfl⟩ := exists_eq_openSubgroupOf U W
    exact H.isPerfectPairing_openSubgroupOf U V hVU

end DualizingData

end Perfect

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]

namespace DualizingData

variable (H : DualizingData n D)

instance isSmoothRep_dualRep_res (S : Subgroup G) (M : Rep.{u} (ULift.{u} ℤ) S) [IsSmoothRep M]
    [Finite M] : IsSmoothRep (dualRep (Rep.res S.subtype D) M) :=
  isSmoothRep_dualRep _ _

include H in

theorem dualityMap_bijective (U : OpenSubgroup G) (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective
      (dualityMap (Rep.res (U : Subgroup G).subtype D) h (H.t U).toAddMonoidHom M) :=
  (H.groupDualityHypotheses U).bijective_dualityMap M hM h

end DualizingData

end Main

section Top

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def topOpenSubgroupEquiv : ((⊤ : OpenSubgroup G) : Subgroup G) ≃* G where
  toFun x := x
  invFun x := ⟨x, Subgroup.mem_top x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [IsTopologicalGroup G] in
theorem continuous_topOpenSubgroupEquiv :
    Continuous (topOpenSubgroupEquiv (G := G)).toMonoidHom :=
  continuous_subtype_val

omit [IsTopologicalGroup G] in
theorem continuous_topOpenSubgroupEquiv_symm :
    Continuous (topOpenSubgroupEquiv (G := G)).symm.toMonoidHom :=
  continuous_id.subtype_mk _

theorem bijective_res_top {k : Type u} [CommRing k] (A : Rep.{u} k G) [IsSmoothRep A]
    (m : ℕ) : Function.Bijective (res A ((⊤ : OpenSubgroup G) : Subgroup G) m).hom :=
  bijective_map_of_mulEquiv (A := A)
    (B := Rep.res ((⊤ : OpenSubgroup G) : Subgroup G).subtype A) topOpenSubgroupEquiv
    continuous_topOpenSubgroupEquiv continuous_topOpenSubgroupEquiv_symm (𝟙 _)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) (fun _ => rfl) (fun _ => rfl) m

end Top

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {n : ℕ} {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsSmoothRep D] in

theorem resTensorIso_inv_comp_resFunctor_map_evalPairing (S : Subgroup G)
    (M : Rep.{u} (ULift.{u} ℤ) G) :
    (resTensorIso S.subtype M (dualRep D M)).inv ≫ (Rep.resFunctor S.subtype).map (evalPairing D M) =
      evalPairing (Rep.res S.subtype D) (Rep.res S.subtype M) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace DualizingData

variable (H : DualizingData n D)

def tTop : cohomology D 2 →+ ZMod n :=
  (H.t ⊤).toAddMonoidHom.comp
    (res D ((⊤ : OpenSubgroup G) : Subgroup G) 2).hom.toAddMonoidHom

variable [NeZero n]

include H in

theorem dualityMap_bijective_of_group (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (dualityMap D h H.tTop M) := by
  have : Finite (Rep.res ((⊤ : OpenSubgroup G) : Subgroup G).subtype M) := inferInstanceAs (Finite M)
  have hU := H.dualityMap_bijective ⊤ (Rep.res ((⊤ : OpenSubgroup G) : Subgroup G).subtype M)
    hM h
  refine bijective_of_bijective_comp hU (bijective_res_top M r)
    (γ := (res (dualRep D M) ((⊤ : OpenSubgroup G) : Subgroup G) s).hom.toAddMonoidHom)
    (bijective_res_top (dualRep D M) s) fun x y => ?_
  rw [dualityMap_apply, dualityMap_apply]
  change (H.t ⊤) (res D ((⊤ : OpenSubgroup G) : Subgroup G) 2
    (cupPairing (evalPairing D M) h x y)) = _
  rw [res_cupPairing, resTensorIso_inv_comp_resFunctor_map_evalPairing]
  rfl

end DualizingData

end Group

end Langlands.ProfiniteCohomology
