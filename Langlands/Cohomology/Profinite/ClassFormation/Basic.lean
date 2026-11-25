import Langlands.Cohomology.Profinite.Characters

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section ResLE

omit [IsTopologicalGroup G] in

theorem continuous_subgroup_inclusion {U V : Subgroup G} (h : V ≤ U) :
    Continuous (Subgroup.inclusion h) :=
  continuous_induced_rng.2 continuous_subtype_val

/-- The inclusion `V → U` of subgroups `V ≤ U`, as a continuous homomorphism. -/
abbrev subgroupInclusionOfLE {U V : Subgroup G} (h : V ≤ U) : V →ₜ* U :=
  ⟨Subgroup.inclusion h, continuous_subgroup_inclusion h⟩

variable (A : Rep.{u} k G)

def resResHom {U V : Subgroup G} (h : V ≤ U) :
    Rep.res (Subgroup.inclusion h) (Rep.res U.subtype A) ⟶ Rep.res V.subtype A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem resResHom_hom_apply {U V : Subgroup G} (h : V ≤ U) (a : A) :
    (resResHom A h).hom a = a :=
  rfl

variable [IsSmoothRep A]

noncomputable def resOfLE {U V : Subgroup G} (h : V ≤ U) (n : ℕ) :
    cohomology (Rep.res U.subtype A) n ⟶ cohomology (Rep.res V.subtype A) n :=
  map (subgroupInclusionOfLE h) (resResHom A h) n

theorem resOfLE_eq {U V : Subgroup G} (h : V ≤ U) (n : ℕ) :
    resOfLE A h n = map (subgroupInclusionOfLE h) (resResHom A h) n :=
  rfl

instance isSmoothRep_res_quotientToInvariants (W : Subgroup G) (N : Subgroup W) [N.Normal] :
    IsSmoothRep ((Rep.res W.subtype A).quotientToInvariants N) :=
  isSmoothRep_quotientToInvariants _ _

end ResLE

noncomputable abbrev H2Open (C : Rep.{u} k G) [IsSmoothRep C] (U : OpenSubgroup G) : Type u :=
  cohomology (Rep.res (U : Subgroup G).subtype C) 2

structure PreClassFormation (C : Rep.{u} k G) [IsSmoothRep C] where

  inv : ∀ U : OpenSubgroup G, H2Open C U →+ QZ

  isZero_H1_open_subgroups : ∀ U : OpenSubgroup G,
    Limits.IsZero (cohomology (Rep.res (U : Subgroup G).subtype C) 1)

  inv_res : ∀ (U V : OpenSubgroup G) (h : V ≤ U) (x : H2Open C U),
    inv V ((resOfLE C (show (V : Subgroup G) ≤ U from h) 2).hom x) =
      (V : Subgroup G).relIndex U • inv U x

structure ClassFormation (C : Rep.{u} k G) [IsSmoothRep C] extends PreClassFormation C where

  inv_bijective : ∀ U : OpenSubgroup G, Function.Bijective (inv U)

structure ClassFormation.At (P : Set Nat.Primes) (C : Rep.{u} k G) [IsSmoothRep C]
    extends PreClassFormation C where

  inv_injective : ∀ U : OpenSubgroup G, Function.Injective (inv U)

  primaryComponent_le_range : ∀ (U : OpenSubgroup G), ∀ p ∈ P,
    ∀ x ∈ AddCommMonoid.primaryComponent QZ (p : ℕ), x ∈ (inv U).range

namespace ClassFormation

open Langlands.ClassFieldTheory.Local

variable {C : Rep.{u} k G} [IsSmoothRep C]

/-- The invariant map of a class formation on an open subgroup `U`, as an isomorphism
`H²(U, C) ≃+ ℚ/ℤ` with values in the Library's `RationalModIntegers`. -/
noncomputable def invEquiv (F : ClassFormation C) (U : OpenSubgroup G) :
    cohomology (Rep.res (U : Subgroup G).subtype C) 2 ≃+ RationalModIntegers :=
  (AddEquiv.ofBijective (F.inv U) (F.inv_bijective U)).trans QZ.toRationalModIntegers

theorem invEquiv_apply (F : ClassFormation C) (U : OpenSubgroup G)
    (x : cohomology (Rep.res (U : Subgroup G).subtype C) 2) :
    F.invEquiv U x = QZ.toRationalModIntegers (F.inv U x) :=
  rfl

/-- The invariant maps are compatible with restriction, up to the relative index. -/
theorem invEquiv_res (F : ClassFormation C) (U V : OpenSubgroup G) (h : V ≤ U)
    (x : cohomology (Rep.res (U : Subgroup G).subtype C) 2) :
    F.invEquiv V ((resOfLE C (show (V : Subgroup G) ≤ U from h) 2).hom x) =
      (V : Subgroup G).relIndex U • F.invEquiv U x := by
  rw [invEquiv_apply, invEquiv_apply, F.inv_res U V h x, map_nsmul]

/-- A class formation from invariant isomorphisms on the `H²` of the open
subgroups with values in `RationalModIntegers`, vanishing `H¹` of the open subgroups, and the
compatibility of the invariants with restriction. -/
noncomputable def ofAddEquiv
    (inv : ∀ U : OpenSubgroup G,
      cohomology (Rep.res (U : Subgroup G).subtype C) 2 ≃+ RationalModIntegers)
    (isZero_one : ∀ U : OpenSubgroup G,
      Limits.IsZero (cohomology (Rep.res (U : Subgroup G).subtype C) 1))
    (inv_res : ∀ (U V : OpenSubgroup G) (h : V ≤ U)
      (x : cohomology (Rep.res (U : Subgroup G).subtype C) 2),
      inv V ((resOfLE C (show (V : Subgroup G) ≤ U from h) 2).hom x) =
        (V : Subgroup G).relIndex U • inv U x) :
    ClassFormation C where
  inv U := QZ.toRationalModIntegers.symm.toAddMonoidHom.comp (inv U).toAddMonoidHom
  isZero_H1_open_subgroups := isZero_one
  inv_res U V h x := by
    simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
    rw [inv_res U V h x, map_nsmul]
  inv_bijective U := QZ.toRationalModIntegers.symm.bijective.comp (inv U).bijective

@[simp]
theorem invEquiv_ofAddEquiv (inv : ∀ U : OpenSubgroup G,
      cohomology (Rep.res (U : Subgroup G).subtype C) 2 ≃+ RationalModIntegers)
    (isZero_one) (inv_res) (U : OpenSubgroup G) :
    (ofAddEquiv inv isZero_one inv_res).invEquiv U = inv U := by
  ext x
  rfl

end ClassFormation

namespace PreClassFormation

variable {C : Rep.{u} k G} [IsSmoothRep C] (F : PreClassFormation C)

noncomputable abbrev H2Quotient (C : Rep.{u} k G) [IsSmoothRep C] (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] : Type u :=
  cohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
    ((V : Subgroup G).subgroupOf U)) 2

noncomputable def fundamentalClass (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] : H2Quotient C U V :=
  haveI : Nonempty (H2Quotient C U V) := ⟨0⟩
  Function.invFun
    (fun x : H2Quotient C U V =>
      F.inv U ((infl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom x))
    (QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)))

end PreClassFormation

end Langlands.ProfiniteCohomology


namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup K]

section Congr

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A] [IsSmoothRep B]

theorem cochainsMap_congr {φ ψ : H →ₜ* G} (f : Rep.res (φ : H →* G) A ⟶ B)
    (g : Rep.res (ψ : H →* G) A ⟶ B) (h : φ = ψ) (hfg : ∀ a : A, f.hom a = g.hom a) :
    cochainsMap φ f = cochainsMap ψ g := by
  subst h
  have : f = g := by
    ext a
    exact hfg a
  subst this
  rfl

theorem map_congr {φ ψ : H →ₜ* G} (f : Rep.res (φ : H →* G) A ⟶ B)
    (g : Rep.res (ψ : H →* G) A ⟶ B) (h : φ = ψ) (hfg : ∀ a : A, f.hom a = g.hom a) (n : ℕ) :
    map φ f n = map ψ g n := by
  unfold map
  rw [cochainsMap_congr f g h hfg]

omit [IsTopologicalGroup H] in
theorem map_eq_id {φ : G →ₜ* G} (f : Rep.res (φ : G →* G) A ⟶ A)
    (h : φ = ContinuousMonoidHom.id G) (hf : ∀ a : A, f.hom a = a) (n : ℕ) :
    map φ f n = 𝟙 _ := by
  subst h
  have : f = 𝟙 A := by
    ext a
    exact hf a
  subst this
  exact map_id n

end Congr

section Iso

variable {A : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A] [IsSmoothRep B]

noncomputable def resInvHom (e : H ≃* G) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) : Rep.res e.symm.toMonoidHom B ⟶ A :=
  Rep.ofHom
    { toLinearMap := (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm.toLinearMap
      isIntertwining' := fun g => by
        ext b
        set L := LinearEquiv.ofBijective f.hom.toLinearMap hf
        apply L.injective
        have h2 : f.hom (A.ρ (e (e.symm g)) (L.symm b)) = B.ρ (e.symm g) (f.hom (L.symm b)) :=
          LinearMap.congr_fun (f.hom.isIntertwining' (e.symm g)) (L.symm b)
        rw [MulEquiv.apply_symm_apply] at h2
        have h3 : f.hom (L.symm b) = b := L.apply_symm_apply b
        rw [h3] at h2
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        exact h2.symm }

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [IsSmoothRep A] [IsSmoothRep B] in
theorem resInvHom_hom_apply (e : H ≃* G) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) (b : B) :
    f.hom ((resInvHom e f hf).hom b) = b :=
  (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply b

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [IsSmoothRep A] [IsSmoothRep B] in
theorem resInvHom_hom_apply' (e : H ≃* G) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) (a : A) :
    (resInvHom e f hf).hom (f.hom a) = a :=
  (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm_apply_apply a

/-- A topological isomorphism `e : H ≃* G` (continuous with continuous inverse) and a bijective
compatible coefficient map induce isomorphisms on cohomology. -/
theorem isIso_map_of_mulEquiv (e : H ≃* G) (he : Continuous e.toMonoidHom)
    (he' : Continuous e.symm.toMonoidHom) (f : Rep.res e.toMonoidHom A ⟶ B)
    (hf : Function.Bijective f.hom) (n : ℕ) :
    IsIso (map ⟨e.toMonoidHom, he⟩ f n) := by
  refine ⟨map ⟨e.symm.toMonoidHom, he'⟩ (resInvHom e f hf) n, ?_, ?_⟩
  · rw [← map_comp]
    exact map_eq_id _ (by ext x; exact e.apply_symm_apply x) (fun a => resInvHom_hom_apply' e f hf a) n
  · rw [← map_comp]
    exact map_eq_id _ (by ext x; exact e.symm_apply_apply x) (fun b => resInvHom_hom_apply e f hf b) n

end Iso

section ResLE

variable (A : Rep.{u} k G) [IsSmoothRep A]

@[reassoc]
theorem resOfLE_comp {U V W : Subgroup G} (hVU : V ≤ U) (hWV : W ≤ V) (n : ℕ) :
    resOfLE A hVU n ≫ resOfLE A hWV n = resOfLE A (hWV.trans hVU) n := by
  rw [resOfLE, resOfLE, resOfLE, ← map_comp]
  exact map_congr _ _ (by ext; rfl) (fun _ => rfl) n

end ResLE

section SubgroupOf

variable {U V : Subgroup G} (h : V ≤ U)

omit [IsTopologicalGroup G] in
theorem continuous_subgroupOfEquivOfLe : Continuous (Subgroup.subgroupOfEquivOfLe h).toMonoidHom :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] in
theorem continuous_subgroupOfEquivOfLe_symm :
    Continuous (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The isomorphism `V → V ⊓ U` (as a subgroup of `U`) for `V ≤ U`, as a continuous homomorphism. -/
abbrev subgroupOfEquivOfLeSymmHom : V →ₜ* (V.subgroupOf U) :=
  ⟨(Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom, continuous_subgroupOfEquivOfLe_symm h⟩

/-- The isomorphism `V ⊓ U → V` (`V ⊓ U` as a subgroup of `U`) for `V ≤ U`, as a continuous
homomorphism. -/
abbrev subgroupOfEquivOfLeHom : (V.subgroupOf U) →ₜ* V :=
  ⟨(Subgroup.subgroupOfEquivOfLe h).toMonoidHom, continuous_subgroupOfEquivOfLe h⟩

variable (A : Rep.{u} k G)

def resSubgroupOfHom :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
        (Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A)) ⟶ Rep.res V.subtype A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [IsSmoothRep A]

omit h in
instance isSmoothRep_res_res (W : Subgroup G) (S : Subgroup W) :
    IsSmoothRep (Rep.res S.subtype (Rep.res W.subtype A)) :=
  isSmoothRep_res_subtype _ _

theorem resOfLE_eq_res_comp (n : ℕ) :
    resOfLE A h n = res (Rep.res U.subtype A) (V.subgroupOf U) n ≫
      map (subgroupOfEquivOfLeSymmHom h) (resSubgroupOfHom h A) n := by
  rw [res, ← map_comp]
  exact map_congr _ _ (by ext; rfl) (fun _ => rfl) n

instance isIso_map_resSubgroupOfHom (n : ℕ) :
    IsIso (map (subgroupOfEquivOfLeSymmHom h) (resSubgroupOfHom h A) n) :=
  isIso_map_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h).symm
    (continuous_subgroupOfEquivOfLe_symm h) (continuous_subgroupOfEquivOfLe h) _
    (show Function.Bijective (id : A → A) from Function.bijective_id) n

theorem resOfLE_apply_eq_zero_iff (n : ℕ) (x : cohomology (Rep.res U.subtype A) n) :
    (resOfLE A h n).hom x = 0 ↔
      (res (Rep.res U.subtype A) (V.subgroupOf U) n).hom x = 0 := by
  rw [resOfLE_eq_res_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hinj : Function.Injective (map (subgroupOfEquivOfLeSymmHom h) (resSubgroupOfHom h A) n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact ⟨fun hx => hinj (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩

end SubgroupOf



namespace PreClassFormation

variable {C : Rep.{u} k G} [IsSmoothRep C] (F : PreClassFormation C)

theorem resLE_eq_zero_iff {U V : OpenSubgroup G} (h : V ≤ U) (hV : Function.Injective (F.inv V))
    (x : H2Open C U) :
    (resOfLE C (show (V : Subgroup G) ≤ U from h) 2).hom x = 0 ↔
      (V : Subgroup G).relIndex U • F.inv U x = 0 := by
  rw [← F.inv_res U V h x]
  exact ⟨fun hx => by rw [hx, map_zero], fun hx => hV (by rw [hx, map_zero])⟩

end PreClassFormation

namespace ClassFormation

variable {C : Rep.{u} k G} [IsSmoothRep C] (F : ClassFormation C)

def toAt (P : Set Nat.Primes) : ClassFormation.At P C where
  toPreClassFormation := F.toPreClassFormation
  inv_injective U := (F.inv_bijective U).1
  primaryComponent_le_range U _ _ x _ := (F.inv_bijective U).2 x

end ClassFormation

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section ContinuousMulEquiv

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Restriction along a topological isomorphism is injective on cohomology. -/
theorem injective_map_of_continuousMulEquiv (m : H ≃ₜ* G) (A : Rep.{u} k G) [IsSmoothRep A]
    (n : ℕ) :
    Function.Injective (map (m : H →ₜ* G) (𝟙 (Rep.res ((m : H →ₜ* G) : H →* G) A)) n).hom := by
  have h := isIso_map_of_mulEquiv m.toMulEquiv m.continuous m.symm.continuous
    (𝟙 (Rep.res ((m : H →ₜ* G) : H →* G) A)) Function.bijective_id n
  have : IsIso (map (m : H →ₜ* G) (𝟙 (Rep.res ((m : H →ₜ* G) : H →* G) A)) n) := h
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

end ContinuousMulEquiv

end Langlands.ProfiniteCohomology
