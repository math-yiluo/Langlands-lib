import Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AwayBijective
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite type models of an open of an affine scheme

Stacks Project, Limits, Lemma 32.5.3 (Tag 07RN), for an affine scheme `S`: if a quasi-compact
open `V ⊆ S` is the limit of a cofiltered diagram of schemes `D i` of finite type over `ℤ` with
affine transition maps, then at every sufficiently small level `i` there is a finite type
`ℤ`-algebra `A` with a morphism `φ : S ⟶ Spec A` and an open immersion `D i ⟶ Spec A` whose
square with `V ⊆ S` is a pullback and such that `φ` pulls the image of `D i` back to `V`.
Finitely many prescribed global functions on `S` can be required to come from `A`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation

section Ring

/-- A localization map `B_g → R_{s g}` is bijective if it is identified, through given
localizations `M` of `B` at `g` and `N` of `R` at `s g`, with a bijective ring map `M → N`. -/
lemma bijective_awayMap_of_isLocalization {B R M N : Type*} [CommRing B] [CommRing R]
    [CommRing M] [CommRing N] (s : B →+* R) (g : B) [Algebra B M] [IsLocalization.Away g M]
    [Algebra R N] [IsLocalization.Away (s g) N] (F : M →+* N) (hF : Function.Bijective F)
    (hcomm : F.comp (algebraMap B M) = (algebraMap R N).comp s) :
    Function.Bijective (Localization.awayMap s g) := by
  let e₁ : Localization.Away g ≃ₐ[B] M := IsLocalization.algEquiv (Submonoid.powers g) _ _
  let e₂ : Localization.Away (s g) ≃ₐ[R] N :=
    IsLocalization.algEquiv (Submonoid.powers (s g)) _ _
  have : Localization.awayMap s g =
      ((e₂.symm : N →+* Localization.Away (s g)).comp F).comp (e₁ : Localization.Away g →+* M) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext b
    have h := congrArg (fun φ : B →+* N => φ b) hcomm
    simp only [RingHom.comp_apply] at h
    simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, RingHom.coe_coe, AlgEquiv.commutes, h]
  rw [this]
  exact (e₂.symm.bijective.comp hF).comp e₁.bijective

/-- Bijectivity of localization maps is stable under composition: if `A_a → B_{f a}` and
`B_{f a} → C_{g (f a)}` are bijective, so is `A_a → C_{g (f a)}`. -/
lemma bijective_awayMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (a : A) (hf : Function.Bijective (Localization.awayMap f a))
    (hg : Function.Bijective (Localization.awayMap g (f a))) :
    Function.Bijective (Localization.awayMap (g.comp f) a) := by
  have : Localization.awayMap (g.comp f) a =
      (Localization.awayMap g (f a)).comp (Localization.awayMap f a) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext x
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  rw [this]
  exact hg.comp hf

end Ring

section FiniteType

/-- A scheme locally of finite type over `ℤ` has finite type `ℤ`-algebras of sections over its
affine opens. -/
lemma finiteType_of_locallyOfFiniteType {X : Scheme.{u}} [LocallyOfFiniteType (terminal.from X)]
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  let z : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) := terminalIsoIsTerminal specULiftZIsTerminal
  let f : X ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from X ≫ z.hom
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType f (inferInstance : LocallyOfFiniteType f)
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₁ : ((Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv ≫
      f.appLE ⊤ U le_top).hom.FiniteType :=
    h.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv).2)
  let e : ULift.{u} ℤ ≃+* ℤ := ULift.ringEquiv
  let g : ℤ →+* Γ(X, U) := ((Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv ≫
      f.appLE ⊤ U le_top).hom.comp e.symm.toRingHom
  have h₂ : g.FiniteType := h₁.comp (RingHom.FiniteType.of_surjective _ e.symm.surjective)
  rw [← RingHom.finiteType_algebraMap, RingHom.ext_int (algebraMap ℤ Γ(X, U)) g]
  exact h₂

/-- Finite type over `ℤ` is invariant under ring isomorphisms, for any `ℤ`-algebra structures. -/
lemma finiteType_int_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra ℤ R]
    [Algebra ℤ S] (e : R ≃+* S) (h : Algebra.FiniteType ℤ R) : Algebra.FiniteType ℤ S := by
  rw [← RingHom.finiteType_algebraMap] at h ⊢
  rw [RingHom.ext_int (algebraMap ℤ S) ((e : R →+* S).comp (algebraMap ℤ R))]
  exact (RingHom.FiniteType.of_surjective _ e.surjective).comp h

/-- A scheme locally of finite type over `ℤ` is locally Noetherian. -/
lemma isLocallyNoetherian_of_locallyOfFiniteType (X : Scheme.{u})
    [LocallyOfFiniteType (terminal.from X)] : IsLocallyNoetherian X := by
  let z : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) := terminalIsoIsTerminal specULiftZIsTerminal
  have : IsNoetherianRing (CommRingCat.of (ULift.{u} ℤ)) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian (terminal.from X ≫ z.hom)

end FiniteType

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- Finitely many properties of objects of a cofiltered category, each stable under morphisms and
each true for some object, hold simultaneously at some object over any given object. -/
lemma exists_forall_of_isCofiltered {J : Type*} [Finite J] (Q : J → I → Prop)
    (hQ : ∀ l {i j : I}, (j ⟶ i) → Q l i → Q l j) (h : ∀ l, ∃ i, Q l i) (i₀ : I) :
    ∃ (i : I) (_ : i ⟶ i₀), ∀ l, Q l i := by
  classical
  choose m hm using h
  cases nonempty_fintype J
  obtain ⟨k, fk⟩ := IsCofiltered.inf_objs_exists (insert i₀ (Finset.univ.image m))
  exact ⟨k, (fk (Finset.mem_insert_self _ _)).some, fun l =>
    hQ l (fk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))).some
      (hm l)⟩

omit [IsCofiltered I] in
lemma appTop_π_map_appTop {D : I ⥤ Scheme.{u}} (c : Cone D) {i j : I} (f : j ⟶ i)
    (u : Γ(D.obj i, ⊤)) : (c.π.app j).appTop ((D.map f).appTop u) = (c.π.app i).appTop u := by
  rw [← c.w f, Scheme.Hom.comp_appTop]
  rfl

variable (D : I ⥤ Scheme.{u}) [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (c : Cone D) (hc : IsLimit c)

include hc in
/-- A global function on the limit whose basic open is affine comes from a level at which its
basic open is affine. -/
lemma exists_appTop_π_eq_isAffineOpen_basicOpen (r : Γ(c.pt, ⊤))
    (hr : IsAffineOpen (c.pt.basicOpen r)) :
    ∃ (i : I) (u : Γ(D.obj i, ⊤)), (c.π.app i).appTop u = r ∧
      IsAffineOpen ((D.obj i).basicOpen u) := by
  obtain ⟨i, V, hV, hVr⟩ := exists_isAffineOpen_preimage_eq D c hc _ hr
  obtain ⟨j, t, rfl⟩ := exists_appTop_π_eq_of_isLimit D c hc r
  obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hV' : IsAffineOpen (D.map fki ⁻¹ᵁ V) := hV.preimage _
  have H : c.π.app k ⁻¹ᵁ (D.obj k).basicOpen ((D.map fkj).appTop t) =
      c.π.app k ⁻¹ᵁ (D.map fki ⁻¹ᵁ V) := by
    rw [Scheme.preimage_basicOpen_top, appTop_π_map_appTop, ← Scheme.Hom.comp_preimage, c.w,
      hVr]
    rfl
  obtain ⟨m, fmk, hm⟩ := exists_map_preimage_eq_map_preimage D c hc
    (isCompact_basicOpen (D.obj k) isCompact_univ _) hV'.isCompact H
  refine ⟨m, (D.map fmk).appTop ((D.map fkj).appTop t), ?_, ?_⟩
  · rw [appTop_π_map_appTop, appTop_π_map_appTop]
  · rw [← Scheme.preimage_basicOpen_top, hm]
    exact hV'.preimage _

include hc in
/-- A finite cover of the limit by affine basic opens of global functions, together with finitely
many further global functions, comes from a level below any given one. -/
lemma exists_level_basicOpen_cover {J K : Type*} [Finite J] [Finite K] (r : J → Γ(c.pt, ⊤))
    (hr : ∀ l, IsAffineOpen (c.pt.basicOpen (r l))) (hcov : ⨆ l, c.pt.basicOpen (r l) = ⊤)
    (x : K → Γ(c.pt, ⊤)) (i₀ : I) :
    ∃ (i : I) (_ : i ⟶ i₀) (r' : J → Γ(D.obj i, ⊤)) (x' : K → Γ(D.obj i, ⊤)),
      (∀ l, (c.π.app i).appTop (r' l) = r l) ∧ (∀ l, IsAffineOpen ((D.obj i).basicOpen (r' l))) ∧
      ⨆ l, (D.obj i).basicOpen (r' l) = ⊤ ∧ ∀ k, (c.π.app i).appTop (x' k) = x k := by
  let Q : J ⊕ K → I → Prop
    | .inl l, i => ∃ u : Γ(D.obj i, ⊤), (c.π.app i).appTop u = r l ∧
        IsAffineOpen ((D.obj i).basicOpen u)
    | .inr k, i => ∃ u : Γ(D.obj i, ⊤), (c.π.app i).appTop u = x k
  have hQ : ∀ l {i j : I}, (j ⟶ i) → Q l i → Q l j := by
    rintro (l | k) i j f ⟨u, hu⟩
    · refine ⟨(D.map f).appTop u, by rw [appTop_π_map_appTop, hu.1], ?_⟩
      rw [← Scheme.preimage_basicOpen_top]
      exact hu.2.preimage _
    · exact ⟨(D.map f).appTop u, by rw [appTop_π_map_appTop, hu]⟩
  have h : ∀ l, ∃ i, Q l i := by
    rintro (l | k)
    · obtain ⟨i, u, hu⟩ := exists_appTop_π_eq_isAffineOpen_basicOpen D c hc (r l) (hr l)
      exact ⟨i, u, hu⟩
    · obtain ⟨i, u, hu⟩ := exists_appTop_π_eq_of_isLimit D c hc (x k)
      exact ⟨i, u, hu.symm⟩
  obtain ⟨m, fm, hm⟩ := exists_forall_of_isCofiltered Q hQ h i₀
  choose u hu using fun l => hm (.inl l)
  choose v hv using fun k => hm (.inr k)
  obtain ⟨j, fjm, hj⟩ := exists_map_eq_top D c hc (⨆ l, (D.obj m).basicOpen (u l)) (by
    simp_rw [Scheme.Hom.preimage_iSup, Scheme.preimage_basicOpen_top, fun l => (hu l).1]
    exact hcov)
  refine ⟨j, fjm ≫ fm, fun l => (D.map fjm).appTop (u l), fun k => (D.map fjm).appTop (v k),
    fun l => by rw [appTop_π_map_appTop, (hu l).1], fun l => ?_, ?_,
    fun k => by rw [appTop_π_map_appTop, hv k]⟩
  · rw [← Scheme.preimage_basicOpen_top]
    exact (hu l).2.preimage _
  · simpa only [Scheme.Hom.preimage_iSup, Scheme.preimage_basicOpen_top] using hj

end Limit

section OpenImmersion

/-- If an open immersion `ι : X ⟶ S` of quasi-compact quasi-separated schemes has image containing
`D(g)`, then `Γ(S, ⊤)_g → Γ(X, ⊤)_{ι^* g}` is bijective. -/
lemma bijective_awayMap_appTop_of_isOpenImmersion {X S : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S] (ι : X ⟶ S)
    [IsOpenImmersion ι] (g : Γ(S, ⊤)) (hg : S.basicOpen g ≤ ι.opensRange) :
    Function.Bijective (Localization.awayMap ι.appTop.hom g) := by
  have := isLocalization_basicOpen_of_qcqs (X := S) isCompact_univ isQuasiSeparated_univ g
  have := isLocalization_basicOpen_of_qcqs (X := X) isCompact_univ isQuasiSeparated_univ
    (ι.appTop.hom g)
  have hU := Scheme.preimage_basicOpen_top ι g
  refine bijective_awayMap_of_isLocalization ι.appTop.hom g
    (ι.appLE (S.basicOpen g) (X.basicOpen (ι.appTop.hom g)) hU.ge).hom ?_ ?_
  · rw [Scheme.Hom.appLE_congr _ _ rfl hU.symm (fun f => Function.Bijective f.hom),
      Scheme.Hom.appLE_eq_app]
    have := ι.isIso_app _ hg
    exact ConcreteCategory.bijective_of_isIso _
  · change CommRingCat.Hom.hom (S.presheaf.map _ ≫ ι.appLE _ _ _) =
      CommRingCat.Hom.hom (ι.appTop ≫ X.presheaf.map _)
    rw [ι.map_appLE, Scheme.Hom.appLE]
    rfl

/-- If `X` is quasi-affine and `ψ : A ⟶ Γ(X, ⊤)` becomes bijective after inverting each `a l`,
where the basic opens of the images `ψ (a l)` cover `X`, then `X ⟶ Spec Γ(X, ⊤) ⟶ Spec A` is an
open immersion with image in `⋃ D(a l)`. -/
lemma isOpenImmersion_toSpecΓ_comp_SpecMap {X : Scheme.{u}} [X.IsQuasiAffine]
    {A : CommRingCat.{u}} (ψ : A ⟶ Γ(X, ⊤)) {J : Type*} (a : J → A)
    (hψ : ∀ l, Function.Bijective (Localization.awayMap ψ.hom (a l)))
    (hcov : ⨆ l, X.basicOpen (ψ (a l)) = ⊤) :
    IsOpenImmersion (X.toSpecΓ ≫ Spec.map ψ) ∧
      ∀ y, (X.toSpecΓ ≫ Spec.map ψ) y ∈ (⨆ l, PrimeSpectrum.basicOpen (a l) : (Spec A).Opens) := by
  have := isIso_SpecMap_restrict_iSup_basicOpen ψ a hψ
  let V : (Spec A).Opens := ⨆ l, PrimeSpectrum.basicOpen (a l)
  have hW : ∀ y : X, Spec.map ψ (X.toSpecΓ y) ∈ V := by
    intro y
    have hy : y ∈ ⨆ l, X.basicOpen (ψ (a l)) := by rw [hcov]; trivial
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hy
    refine Opens.mem_iSup.mpr ⟨l, ?_⟩
    rw [← Scheme.toSpecΓ_preimage_basicOpen] at hl
    exact hl
  let W := Spec.map ψ ⁻¹ᵁ V
  have H' : Set.range X.toSpecΓ ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hW y
  let j := IsOpenImmersion.lift W.ι X.toSpecΓ H'
  have : IsOpenImmersion j := by
    have : IsOpenImmersion (j ≫ W.ι) := by rw [IsOpenImmersion.lift_fac]; infer_instance
    exact IsOpenImmersion.of_comp j W.ι
  have he : X.toSpecΓ ≫ Spec.map ψ = j ≫ (Spec.map ψ ∣_ V) ≫ V.ι := by
    rw [morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc]
  exact ⟨by rw [he]; infer_instance, hW⟩

end OpenImmersion

section Model

/-- A finite type open model of an open immersion `ι : V ⟶ S` along a morphism `π : V ⟶ Y`,
with prescribed global functions `T` on `S`: a finite type `ℤ`-algebra `A`, a morphism
`φ : S ⟶ Spec A` and an open immersion `e : Y ⟶ Spec A` such that the square `π, ι, e, φ` is a
pullback, `φ⁻¹(e(Y)) = ι(V)`, and every element of `T` is the image of a global function of
`Spec A`. For an affine `S` this is the datum at one index of Stacks Lemma 32.5.3 (Tag 07RN):
the finite type model `S_j = Spec A` of `S` with its open `V'_j`, the image of `e`. -/
structure FiniteTypeOpenModel {V Y S : Scheme.{u}} (π : V ⟶ Y) (ι : V ⟶ S) [IsOpenImmersion ι]
    (T : Set Γ(S, ⊤)) where
  /-- The finite type `ℤ`-algebra. -/
  A : CommRingCat.{u}
  finiteType : Algebra.FiniteType ℤ A
  /-- The morphism from `S` to `Spec A`. -/
  φ : S ⟶ Spec A
  /-- The open immersion from `Y` to `Spec A`. -/
  e : Y ⟶ Spec A
  isOpenImmersion : IsOpenImmersion e
  isPullback : IsPullback π ι e φ
  preimage_opensRange : φ ⁻¹ᵁ e.opensRange = ι.opensRange
  exists_appTop_eq : ∀ x ∈ T, ∃ a, φ.appTop a = x

attribute [instance] FiniteTypeOpenModel.finiteType FiniteTypeOpenModel.isOpenImmersion

end Model

section Main

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

set_option maxHeartbeats 1000000 in
/-- Stacks Project, Limits, Lemma 32.5.3 (Tag 07RN), for an affine scheme `S`, in cofinal form.
Let `D` be a cofiltered diagram of quasi-compact schemes locally of finite type over `ℤ` with
affine transition maps, with limit cone `c`, and let `ι : c.pt ⟶ S` be an open immersion into an
affine scheme. Then below any index `i₀` there is an index `i` with a finite type open model of
`ι` along `c.π i` in which every element of the finite set `T ⊆ Γ(S, ⊤)` is the image of a global
function of `Spec A`. -/
theorem exists_finiteTypeOpenModel_of_isLimit (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))] (c : Cone D) (hc : IsLimit c)
    {S : Scheme.{u}} [IsAffine S] (ι : c.pt ⟶ S) [IsOpenImmersion ι] (T : Set Γ(S, ⊤))
    (hT : T.Finite) (i₀ : I) :
    ∃ (i : I) (_ : i ⟶ i₀), Nonempty (FiniteTypeOpenModel (c.π.app i) ι T) := by
  classical
  have : Finite T := hT.to_subtype
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by
    have := isLocallyNoetherian_of_locallyOfFiniteType (D.obj i)
    infer_instance
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated ι
  -- Finitely many basic opens `D(g l)` of `S` cover the image of `ι`.
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ := (isBasis_basicOpen S).exists_finite_of_isCompact
    (U := ι.opensRange) (isCompact_range ι.continuous)
  have : Finite Us := hUsfin.to_subtype
  choose g hg using fun U : Us => hUsB U.2
  have hsup : ⨆ l, S.basicOpen (g l) = ι.opensRange := by
    simp_rw [hg]
    rw [hUs, sSup_eq_iSup']
  have hgle : ∀ l, S.basicOpen (g l) ≤ ι.opensRange := fun l => by
    rw [← hsup]; exact le_iSup (fun l => S.basicOpen (g l)) l
  -- Their pullbacks to the limit are affine and cover it.
  let s := ι.appTop.hom
  have hr : ∀ l, IsAffineOpen (c.pt.basicOpen (s (g l))) := fun l => by
    rw [← Scheme.preimage_basicOpen_top]
    exact ((isAffineOpen_top S).basicOpen (g l)).preimage_of_isOpenImmersion ι (hgle l)
  have hcov : ⨆ l, c.pt.basicOpen (s (g l)) = ⊤ := by
    simp_rw [s, ← Scheme.preimage_basicOpen_top, ← Scheme.Hom.preimage_iSup, hsup]
    exact ι.preimage_opensRange
  -- Descend the cover and the prescribed functions to a level `i`.
  obtain ⟨i, fi, r', x', hr', hraff, hrcov, hx'⟩ := exists_level_basicOpen_cover D c hc
    (fun l => s (g l)) hr hcov (fun b : T => s b) i₀
  have : (D.obj i).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen (D.obj i) fun y => by
      have hy : y ∈ ⨆ l, (D.obj i).basicOpen (r' l) := by rw [hrcov]; trivial
      obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hy
      exact ⟨r' l, hraff l, hl⟩
  -- The pinched ring `P = Γ(S) ×_{Γ(c.pt)} Γ(D i)`.
  let t := (c.π.app i).appTop.hom
  let P := pinchedRing s t
  have hmem : ∀ l, (g l, r' l) ∈ P := fun l => mem_pinchedRing.mpr (hr' l).symm
  have hxmem : ∀ b : T, ((b : Γ(S, ⊤)), x' b) ∈ P := fun b => mem_pinchedRing.mpr (hx' b).symm
  let h : Us → P := fun l => ⟨(g l, r' l), hmem l⟩
  -- `Γ(S)_{g} → Γ(c.pt)_{s g}` is bijective since `ι` is an isomorphism over `D(g)`.
  have hs : ∀ l, Function.Bijective (Localization.awayMap s (g l)) := fun l =>
    bijective_awayMap_appTop_of_isOpenImmersion ι (g l) (hgle l)
  -- Hence `P_{h l} ≅ Γ(D i)_{r' l}`, which is of finite type over `ℤ`.
  have hft : ∀ l, Algebra.FiniteType ℤ (Localization.Away (h l)) := fun l => by
    have hb := bijective_awayMap_pinchedRing_snd s t (h l) (hs l)
    have := isLocalization_basicOpen_of_qcqs (X := D.obj i) isCompact_univ
      isQuasiSeparated_univ (r' l)
    let e₁ : Localization.Away (h l) ≃+* Localization.Away (r' l) := RingEquiv.ofBijective _ hb
    let e₂ : Localization.Away (r' l) ≃ₐ[Γ(D.obj i, ⊤)]
        Γ(D.obj i, (D.obj i).basicOpen (r' l)) :=
      IsLocalization.algEquiv (Submonoid.powers (r' l)) _ _
    exact finiteType_int_of_ringEquiv (e₁.trans e₂.toRingEquiv).symm
      (finiteType_of_locallyOfFiniteType (hraff l))
  -- A finite type subring `A ⊆ P` with the same localizations, containing the prescribed data.
  obtain ⟨A, hA, hAft, hTA, hAbij⟩ := exists_finiteType_subalgebra_bijective_awayMap h hft
    (Set.range fun b : T => (⟨((b : Γ(S, ⊤)), x' b), hxmem b⟩ : P)) (Set.finite_range _)
  let ψ : A →+* Γ(D.obj i, ⊤) := (pinchedRing.snd s t).comp (A.val : A →+* P)
  let φ₀ : A →+* Γ(S, ⊤) := (pinchedRing.fst s t).comp (A.val : A →+* P)
  have hψ : ∀ l, Function.Bijective (Localization.awayMap ψ ⟨h l, hA l⟩) := fun l =>
    bijective_awayMap_comp _ _ _ (hAbij l) (bijective_awayMap_pinchedRing_snd s t (h l) (hs l))
  -- The open immersion `e : D i ⟶ Spec Γ(D i) ⟶ Spec A`.
  let e := (D.obj i).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  obtain ⟨he, hW⟩ := isOpenImmersion_toSpecΓ_comp_SpecMap (CommRingCat.ofHom ψ)
    (fun l => (⟨h l, hA l⟩ : A)) hψ hrcov
  let V : (Spec (CommRingCat.of A)).Opens := ⨆ l, PrimeSpectrum.basicOpen (⟨h l, hA l⟩ : A)
  -- The morphism `φ : S ⟶ Spec A` and the commutative square.
  let φ := S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ₀)
  have hring : CommRingCat.ofHom ψ ≫ (c.π.app i).appTop = CommRingCat.ofHom φ₀ ≫ ι.appTop := by
    ext a
    exact (mem_pinchedRing.mp a.1.2).symm
  have hsq : c.π.app i ≫ e = ι ≫ φ := by
    simp only [e, φ]
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hring]
    rfl
  have hpre : ∀ a : A, φ ⁻¹ᵁ (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens) =
      S.basicOpen (φ₀ a) := fun a =>
    S.toSpecΓ_preimage_basicOpen (φ₀ a)
  have hrange : φ ⁻¹ᵁ e.opensRange = ι.opensRange := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      have hV : φ x ∈ V := by rw [← hy]; exact hW y
      obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hV
      exact hgle l ((hpre ⟨h l, hA l⟩).le hl)
    · rintro x ⟨z, rfl⟩
      exact ⟨c.π.app i z, by rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]⟩
  refine ⟨i, fi, ⟨⟨CommRingCat.of A, finiteType_int_of_ringEquiv (RingEquiv.refl A) hAft, φ, e,
    inferInstance, IsOpenImmersion.isPullback _ _ _ _ hsq.symm hrange, hrange, ?_⟩⟩⟩
  intro b hb
  let a : A := ⟨⟨(b, x' ⟨b, hb⟩), hxmem ⟨b, hb⟩⟩, hTA ⟨⟨b, hb⟩, rfl⟩⟩
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv a, ?_⟩
  simp only [φ]
  rw [← CommRingCat.comp_apply, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

/-- `exists_finiteTypeOpenModel_of_isLimit` for an inverse system `D : Iᵒᵖ ⥤ Scheme` indexed by
a nonempty directed preorder `I`: above every index `i₀` there is an index `i` with a finite type
open model of `ι` along `c.π (op i)`. -/
theorem exists_le_finiteTypeOpenModel_of_isLimit {I : Type u} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))] (c : Cone D) (hc : IsLimit c)
    {S : Scheme.{u}} [IsAffine S] (ι : c.pt ⟶ S) [IsOpenImmersion ι] (T : Set Γ(S, ⊤))
    (hT : T.Finite) (i₀ : I) :
    ∃ i, i₀ ≤ i ∧ Nonempty (FiniteTypeOpenModel (c.π.app (Opposite.op i)) ι T) := by
  obtain ⟨i, f, h⟩ := exists_finiteTypeOpenModel_of_isLimit D c hc ι T hT (Opposite.op i₀)
  exact ⟨i.unop, leOfHom f.unop, h⟩

end Main

end Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation
