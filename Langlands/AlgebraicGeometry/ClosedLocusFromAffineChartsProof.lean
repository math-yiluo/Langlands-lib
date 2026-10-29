/-
Portions of this file are adapted from the module
`P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart.lean`
(namespace `GlueClosed2`) of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), licensed under the Apache License 2.0.
The adaptation replaces the triviality predicate on rigidified line bundles by an arbitrary
property of morphisms and changes the universe from `0` to `u`.
-/
import Langlands.AlgebraicGeometry.ClosedLocusFromAffineChartsStatement
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Proof that closed loci detected on affine charts glue -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ClosedLocusFromAffineCharts

noncomputable section

variable {X : Scheme.{u}}

/-- A closed chart of a property `P` of morphisms into `X` over an open `U` of `X`: a closed
immersion into `U` through which exactly the morphisms into `U` satisfying `P` factor. -/
structure Chart (P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop) (U : X.Opens) where
  /-- The closed subscheme of `U`. -/
  Z : Scheme.{u}
  /-- Its inclusion into `U`. -/
  ι : Z ⟶ U.toScheme
  closed : IsClosedImmersion ι
  iff : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ U.toScheme), (∃ k : Y ⟶ Z, k ≫ ι = g) ↔ P (g ≫ U.ι)

attribute [local instance] Chart.closed

namespace Chart

variable {P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop} {U : X.Opens} (C : Chart P U)

/-- The composite of the chart inclusion with the open immersion `U ⟶ X`. -/
abbrev emb : C.Z ⟶ X := C.ι ≫ U.ι

theorem range_emb : Set.range C.emb.base ⊆ (U : Set X) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Scheme.Opens.range_ι U]
  exact Set.image_subset_range _ _

theorem iff' {Y : Scheme.{u}} (ψ : Y ⟶ X) (hr : Set.range ψ.base ⊆ (U : Set X)) :
    P ψ ↔ ∃ ψ₀ : Y ⟶ C.Z, ψ₀ ≫ C.emb = ψ := by
  have hr' : Set.range ψ.base ⊆ Set.range U.ι.base := by rwa [Scheme.Opens.range_ι]
  have fac := IsOpenImmersion.lift_fac U.ι ψ hr'
  have key := C.iff (IsOpenImmersion.lift U.ι ψ hr')
  rw [fac] at key
  rw [← key]
  constructor
  · rintro ⟨ψ₀, h⟩
    exact ⟨ψ₀, by rw [emb, ← Category.assoc, h, fac]⟩
  · rintro ⟨ψ₀, h⟩
    refine ⟨ψ₀, ?_⟩
    rw [← cancel_mono U.ι, Category.assoc, fac]
    exact h

theorem prop_emb : P C.emb :=
  (C.iff' C.emb C.range_emb).2 ⟨𝟙 _, Category.id_comp _⟩

end Chart

theorem ker_app_res {T : Scheme.{u}} (h : T ⟶ X) (V : X.Opens) :
    RingHom.ker (((h ⁻¹ᵁ V).ι ≫ h).app V).hom = RingHom.ker (h.app V).hom := by
  have : IsIso ((h ⁻¹ᵁ V).ι.app (h ⁻¹ᵁ V)) :=
    Scheme.Hom.isIso_app _ _ (by rw [Scheme.Opens.opensRange_ι])
  ext x
  simp only [RingHom.mem_ker, Scheme.Hom.comp_app]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso ((h ⁻¹ᵁ V).ι.app (h ⁻¹ᵁ V))).1

theorem range_res_subset {T : Scheme.{u}} (h : T ⟶ X) (V : X.Opens) :
    Set.range ((h ⁻¹ᵁ V).ι ≫ h).base ⊆ (V : Set X) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  exact Set.image_preimage_subset _ _

/-- The restriction isomorphism `Γ(X, V) ⟶ Γ(V, ⊤)`. -/
abbrev θ (V : X.Opens) : Γ(X, V) ⟶ Γ(V.toScheme, ⊤) := V.ι.appLE V ⊤ V.ι_preimage_self.ge

instance (V : X.Opens) : IsIso (θ V) :=
  inferInstanceAs (IsIso (V.ι.appLE V ⊤ V.ι_preimage_self.ge))

theorem ker_comp_ι_app {T : Scheme.{u}} (V : X.Opens) (k : T ⟶ V.toScheme) :
    RingHom.ker ((k ≫ V.ι).app V).hom = (RingHom.ker k.appTop.hom).comap (θ V).hom := by
  have e : (⊤ : T.Opens) ≤ (k ≫ V.ι) ⁻¹ᵁ V := fun x _ => (k.base x).2
  have h1 : (k ≫ V.ι).app V ≫ T.presheaf.map (homOfLE e).op = θ V ≫ k.appTop := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    have := Scheme.Hom.appLE_comp_appLE k V.ι V ⊤ (k ⁻¹ᵁ ⊤) V.ι_preimage_self.ge le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact this.symm
  have htop : (k ≫ V.ι) ⁻¹ᵁ V = ⊤ := top_le_iff.mp e
  have hhom : (homOfLE e).op = (eqToHom htop.symm).op := by congr 1
  have : IsIso (T.presheaf.map (homOfLE e).op) := by rw [hhom, eqToHom_op]; infer_instance
  ext x
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, ← h1, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (T.presheaf.map (homOfLE e).op)).1).symm

section Agree

variable {P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop}
  (hcomp : ∀ ⦃Y Y' : Scheme.{u}⦄ (f : Y' ⟶ Y) (g : Y ⟶ X), P g → P (f ≫ g))
  (Z : ∀ U : X.affineOpens, Chart P (U : X.Opens))

/-- The ideal of the chart over `V`, as an ideal of `Γ(X, V)`. -/
abbrev κ (V : X.affineOpens) : Ideal Γ(X, (V : X.Opens)) := RingHom.ker ((Z V).emb.app V).hom

include hcomp in
theorem ker_emb_app_eq {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    RingHom.ker ((Z U).emb.app V).hom = κ Z V := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := ((Z U).iff' (Z V).emb
      (fun x hx => hVU ((Z V).range_emb hx))).1 (Z V).prop_emb
    intro x hx
    rw [RingHom.mem_ker] at hx
    show (((Z V).emb).app V).hom x = 0
    rw [← ha, Scheme.Hom.comp_app]
    first
      | (simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero])
      | (erw [CommRingCat.hom_comp]; rw [RingHom.comp_apply, hx, map_zero])
  · intro x hx
    let h : ((Z U).emb ⁻¹ᵁ (V : X.Opens)).toScheme ⟶ X := ((Z U).emb ⁻¹ᵁ (V : X.Opens)).ι ≫ (Z U).emb
    have hrV : Set.range h.base ⊆ ((V : X.Opens) : Set X) := range_res_subset (Z U).emb V
    have hT : P h := hcomp _ _ (Z U).prop_emb
    obtain ⟨b, hb⟩ := ((Z V).iff' h hrV).1 hT
    have hx0 : (((Z V).emb).app V).hom x = 0 := hx
    rw [← ker_app_res (Z U).emb V]
    change x ∈ RingHom.ker (h.app V).hom
    rw [RingHom.mem_ker, ← hb, Scheme.Hom.comp_app]
    first
      | (simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx0, map_zero])
      | (erw [CommRingCat.hom_comp]; rw [RingHom.comp_apply, hx0, map_zero])

theorem ker_emb_app_map_basicOpen (W : X.affineOpens) (s : Γ(X, (W : X.Opens))) :
    (RingHom.ker ((Z W).emb.app W).hom).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      RingHom.ker ((Z W).emb.app (X.affineBasicOpen s)).hom := by
  set h := (Z W).emb with hh
  have hcompact : IsCompact (h ⁻¹ᵁ (W : X.Opens)).1 := by
    have h1 : h ⁻¹ᵁ (W : X.Opens) = (Z W).ι ⁻¹ᵁ ((W : X.Opens).ι ⁻¹ᵁ (W : X.Opens)) := rfl
    rw [h1, Scheme.Opens.ι_preimage_self]
    exact QuasiCompact.isCompact_preimage _ isOpen_univ isCompact_univ
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [RingHom.mem_ker] at hx
    change (h.app (X.basicOpen s)).hom ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom x) = 0
    rw [← CommRingCat.comp_apply, h.naturality, CommRingCat.comp_apply, hx, map_zero]
  · intro x hx
    have := W.2.isLocalization_basicOpen s
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    refine (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ?_
    suffices ∃ (V : (Z W).Z.Opens) (hV : V = (Z W).Z.basicOpen ((h.app W).hom s)),
        letI := hV.trans_le ((Z W).Z.basicOpen_le _); ((h.app W).hom x |_ V) = 0 by
      obtain ⟨_, rfl, H⟩ := this
      obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        (Z W).Z (U := h ⁻¹ᵁ (W : X.Opens)) hcompact ((h.app W).hom x) ((h.app W).hom s) H
      exact ⟨_, ⟨n, rfl⟩, by simpa using hn⟩
    refine ⟨h ⁻¹ᵁ X.basicOpen s, by simp, ?_⟩
    replace hx : (X.presheaf.map (homOfLE (X.basicOpen_le s)).op ≫ h.app _).hom x = 0 := by
      trans (h.app (X.basicOpen s)).hom (algebraMap Γ(X, (W : X.Opens)) _ x)
      · simp [-NatTrans.naturality, RingHom.algebraMap_toAlgebra]
      · have hx' : (h.app (X.basicOpen s)).hom
            (IsLocalization.mk' (Γ(X, X.basicOpen s)) x
              (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) = 0 := hx
        rw [← IsLocalization.mk'_spec' (Γ(X, X.basicOpen s)) x
          (⟨s ^ n, n, rfl⟩ : Submonoid.powers s), map_mul, hx', mul_zero]
    rwa [h.naturality] at hx

/-- The ideal sheaf glued from the ideals of the charts. -/
def glued : X.IdealSheafData where
  ideal V := κ Z V
  map_ideal_basicOpen V s := by
    rw [ker_emb_app_map_basicOpen Z V s]
    exact ker_emb_app_eq hcomp Z (X.basicOpen_le s)

end Agree

theorem main {P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop}
    (hcomp : ∀ ⦃Y Y' : Scheme.{u}⦄ (f : Y' ⟶ Y) (g : Y ⟶ X), P g → P (f ≫ g))
    (hloc : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X),
      (∀ V : X.affineOpens, P ((g ⁻¹ᵁ (V : X.Opens)).ι ≫ g)) → P g)
    (Z : ∀ U : X.affineOpens, Chart P (U : X.Opens)) :
    ∃ (Zs : Scheme.{u}) (ι : Zs ⟶ X), IsClosedImmersion ι ∧
      ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X), (∃ k : Y ⟶ Zs, k ≫ ι = g) ↔ P g := by
  let I := glued hcomp Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  intro T ψ
  constructor
  · rintro ⟨ψ₀, hψ₀⟩
    have hIψ : ∀ V : X.affineOpens, κ Z V ≤ RingHom.ker (ψ.app V).hom := fun V => by
      have h1 : I ≤ ψ.ker := by
        rw [← hψ₀]
        have := Scheme.Hom.le_ker_comp ψ₀ I.subschemeι
        rwa [Scheme.IdealSheafData.ker_subschemeι] at this
      exact (Scheme.IdealSheafData.ideal_mono h1 V).trans (ψ.ideal_ker_le V)
    refine hloc ψ fun V => ?_
    let hV : (ψ ⁻¹ᵁ (V : X.Opens)).toScheme ⟶ X := (ψ ⁻¹ᵁ (V : X.Opens)).ι ≫ ψ
    have hr : Set.range hV.base ⊆ ((V : X.Opens) : Set X) := range_res_subset ψ V
    have hr' : Set.range hV.base ⊆ Set.range (V : X.Opens).ι.base := by
      rwa [Scheme.Opens.range_ι]
    let k := IsOpenImmersion.lift (V : X.Opens).ι hV hr'
    have hk : k ≫ (V : X.Opens).ι = hV := IsOpenImmersion.lift_fac _ _ _
    have hkerTop : RingHom.ker ((Z V).ι.appTop).hom ≤ RingHom.ker (k.appTop).hom := by
      intro x' hx'
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (θ (V : X.Opens))).2 x'
      have m1 : x ∈ RingHom.ker (((Z V).ι ≫ (V : X.Opens).ι).app V).hom := by
        rw [ker_comp_ι_app]; exact hx'
      have m2 : x ∈ RingHom.ker (hV.app V).hom := by
        change x ∈ RingHom.ker ((((ψ ⁻¹ᵁ (V : X.Opens)).ι ≫ ψ)).app V).hom
        rw [ker_app_res]
        exact hIψ V m1
      rw [← hk, ker_comp_ι_app] at m2
      exact m2
    have hle : (Z V).ι.ker ≤ k.ker := by
      rw [Scheme.ker_of_isAffine k]
      refine Scheme.IdealSheafData.le_of_isAffine ?_
      rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ofIdealTop_ideal]
      intro y hy
      have hid : (homOfLE (le_top : (⊤ : (V : X.Opens).toScheme.Opens) ≤ ⊤)) = 𝟙 _ :=
        Subsingleton.elim _ _
      have hy' : y = (((V : X.Opens).toScheme).presheaf.map (homOfLE le_top).op).hom y := by
        rw [hid, op_id, CategoryTheory.Functor.map_id]; rfl
      rw [hy']
      exact Ideal.mem_map_of_mem _ (hkerTop hy)
    refine ((Z V).iff' _ hr).2 ⟨IsClosedImmersion.lift (Z V).ι k hle, ?_⟩
    show (IsClosedImmersion.lift (Z V).ι k hle ≫ ((Z V).ι ≫ (V : X.Opens).ι)) = hV
    rw [← Category.assoc, IsClosedImmersion.lift_fac, hk]
  · intro hT
    have hle : I ≤ ψ.ker := by
      change I ≤ Scheme.IdealSheafData.ofIdeals _
      rw [Scheme.IdealSheafData.le_ofIdeals_iff]
      intro V x hx
      have hT' : P ((ψ ⁻¹ᵁ (V : X.Opens)).ι ≫ ψ) := hcomp _ _ hT
      obtain ⟨ψ₀, h₀⟩ := ((Z V).iff' _ (range_res_subset ψ V)).1 hT'
      have hx0 : (((Z V).emb).app V).hom x = 0 := hx
      change x ∈ RingHom.ker (ψ.app V).hom
      rw [← ker_app_res ψ V, RingHom.mem_ker]
      rw [← h₀, Scheme.Hom.comp_app]
      first
        | (simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx0, map_zero])
        | (erw [CommRingCat.hom_comp]; rw [RingHom.comp_apply, hx0, map_zero])
    exact ⟨IsClosedImmersion.lift I.subschemeι ψ
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hle),
      IsClosedImmersion.lift_fac _ _ _⟩

end

end ClosedLocusFromAffineCharts

/-- Closed loci detected on all affine charts glue to a closed subscheme. -/
theorem closedLocusFromAffineCharts : ClosedLocusFromAffineChartsStatement.{u} := by
  intro X P hcomp hloc hchart
  exact ClosedLocusFromAffineCharts.main hcomp hloc fun U =>
    ⟨(hchart U).choose, (hchart U).choose_spec.choose, (hchart U).choose_spec.choose_spec.1,
      (hchart U).choose_spec.choose_spec.2⟩

end Langlands.AlgebraicGeometry
