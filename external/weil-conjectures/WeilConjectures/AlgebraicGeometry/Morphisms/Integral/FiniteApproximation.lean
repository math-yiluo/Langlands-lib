/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Integral morphisms are limits of finite morphisms

Let `S` be a quasi-compact quasi-separated scheme and `F` a quasi-coherent `𝒪_S`-algebra (a
coequifibered presheaf of rings on `S.AffineZariskiSite` under `𝒪_S`) which is integral over
`𝒪_S`. We show that the relative spectrum `Spec_S F` is the cofiltered limit of the relative
spectra of finite quasi-coherent subalgebras of `F`, which are finite over `S`. Applied to the
relative normalization this shows that an integral morphism `X ⟶ S` is a cofiltered limit of
finite `S`-schemes (compare Stacks Project Tag 09YZ, which also asks for the stages to be of
finite presentation; this is not shown here).

The key point is that every section of `F` over an affine open lies in a finite quasi-coherent
subalgebra (Stacks Project Tag 01PG). We deduce this from the corresponding statement for ideal
sheaves (`AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_of_mem`), applied to the
relative spectrum `D` of `𝒪_S + ε F ⊆ F[ε]`: quasi-coherent ideals of `𝒪_D` contained in `ε F` are
the quasi-coherent `𝒪_S`-submodules of `F`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Hom.FiniteApproximation`: a presentation of `f : X ⟶ S` as a
  cofiltered limit of finite `S`-schemes.
- `AlgebraicGeometry.isLimitOfIsLimitOpensCone'`: being a limit cone of schemes is local on a
  stage.
- `AlgebraicGeometry.Scheme.AffineZariskiSite.finiteApproximation`: the relative spectrum of an
  integral quasi-coherent algebra is a limit of finite schemes.
- `AlgebraicGeometry.Scheme.Hom.nonempty_finiteApproximation_of_isIntegralHom`: an integral
  morphism to a quasi-compact quasi-separated scheme is a cofiltered limit of finite morphisms.

## References

* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section IsLimitOfCover

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Two morphisms to the point of a cone `c` over a cofiltered diagram of schemes agree if they
agree after composition with all the projections of `c`, provided that the restrictions of `c`
to the members of an open cover of some stage are limit cones. -/
lemma hom_ext_of_isLimit_opensCone [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a))) {P : Scheme.{u}} (m₁ m₂ : P ⟶ c.pt)
    (hm : ∀ j, m₁ ≫ c.π.app j = m₂ ≫ c.π.app j) : m₁ = m₂ := by
  let q := m₁ ≫ c.π.app i₀
  let 𝒱 : P.OpenCover := Scheme.Cover.mkOfCovers σ (fun a ↦ (q ⁻¹ᵁ U a).toScheme)
    (fun a ↦ Scheme.Opens.ι _) (fun x ↦ by
      have : q x ∈ ⨆ a, U a := by rw [hU]; trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact ⟨a, ⟨x, ha⟩, rfl⟩)
  refine 𝒱.hom_ext _ _ fun a ↦ ?_
  change (q ⁻¹ᵁ U a).ι ≫ m₁ = (q ⁻¹ᵁ U a).ι ≫ m₂
  have hr (m : P ⟶ c.pt) (hm' : m ≫ c.π.app i₀ = q) :
      Set.range ((q ⁻¹ᵁ U a).ι ≫ m) ⊆ Set.range (c.π.app i₀ ⁻¹ᵁ U a).ι := by
    rintro - ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (((q ⁻¹ᵁ U a).ι ≫ m) ≫ c.π.app i₀) t ∈ U a
    rw [Category.assoc, hm']
    exact t.2
  have h₁ := hr m₁ rfl
  have h₂ := hr m₂ (hm i₀).symm
  rw [← IsOpenImmersion.lift_fac (c.π.app i₀ ⁻¹ᵁ U a).ι _ h₁,
    ← IsOpenImmersion.lift_fac (c.π.app i₀ ⁻¹ᵁ U a).ι _ h₂]
  congr 1
  refine (h a).hom_ext fun j ↦ ?_
  rw [← cancel_mono (D.map j.hom ⁻¹ᵁ U a).ι]
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, Category.assoc,
    Category.assoc, hm]


variable {D c} in
lemma lift_opensCone_ι_π_app [IsCofiltered I] {i₀ : I} {V : (D.obj i₀).Opens}
    (hV : IsLimit (opensCone D c i₀ V)) (s : Cone D) (j : I) :
    hV.lift (opensCone D s i₀ V) ≫ (c.π.app i₀ ⁻¹ᵁ V).ι ≫ c.π.app j =
      (s.π.app i₀ ⁻¹ᵁ V).ι ≫ s.π.app j := by
  obtain ⟨k, fkj, fki₀, -⟩ := IsCofilteredOrEmpty.cone_objs j i₀
  have h1 := lift_opensCone_ι_comp D hV s (Over.mk fki₀)
  rw [← c.w fkj, ← s.w fkj]
  simp only [← Category.assoc] at h1 ⊢
  exact congrArg (· ≫ D.map fkj) h1

/-- **Being a limit cone is local on a stage.** Let `{Dᵢ}` be a cofiltered diagram of schemes and
let `c` be a cone over it. Suppose some stage `D.obj i₀` has an open cover `{U a}` such that the
restriction of `c` to every `U a` is a limit cone. Then `c` is a limit cone.

Compared to `AlgebraicGeometry.isLimitOfIsLimitOpensCone`, no hypothesis on the intersections
`U a ⊓ U b` is needed. -/
noncomputable def isLimitOfIsLimitOpensCone' [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a))) : IsLimit c where
  lift s := (preimageCover D i₀ U hU s).glueMorphisms
    (fun a ↦ (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) fun a b ↦
      hom_ext_of_isLimit_opensCone D c i₀ U hU h _ _ fun j ↦ by
        simp only [Category.assoc]
        rw [lift_opensCone_ι_π_app (h a), lift_opensCone_ι_π_app (h b)]
        exact pullback.condition_assoc _
  fac s j := by
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Category.assoc]
    exact lift_opensCone_ι_π_app (h a) s j
  uniq s m hm := by
    refine hom_ext_of_isLimit_opensCone D c i₀ U hU h _ _ fun j ↦ ?_
    rw [hm]
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Category.assoc]
    exact (lift_opensCone_ι_π_app (h a) s j).symm

end IsLimitOfCover
end AlgebraicGeometry

section Ring

open TrivSqZeroExt

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- A ring homomorphism `g : A →+* A'` induces a ring homomorphism `A[ε] →+* A'[ε]` of dual
numbers. -/
def DualNumber.map (g : A →+* A') : DualNumber A →+* DualNumber A' where
  toFun z := inl (g z.fst) + inr (g z.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [add_comm, add_left_comm]

@[simp]
lemma DualNumber.fst_map (g : A →+* A') (z : DualNumber A) :
    (DualNumber.map g z).fst = g z.fst := by
  simp [DualNumber.map]

@[simp]
lemma DualNumber.snd_map (g : A →+* A') (z : DualNumber A) :
    (DualNumber.map g z).snd = g z.snd := by
  simp [DualNumber.map]

/-- For a ring homomorphism `α : R →+* A`, the subring `α(R) + εA` of the dual numbers `A[ε]`.
Its ideals contained in `εA` are the `R`-submodules of `A`. -/
def RingHom.dualSubring (α : R →+* A) : Subring (DualNumber A) :=
  α.range.comap (fstHom ℤ A A).toRingHom

lemma RingHom.mem_dualSubring {α : R →+* A} {z : DualNumber A} :
    z ∈ α.dualSubring ↔ z.fst ∈ α.range :=
  Iff.rfl

lemma RingHom.inr_mem_dualSubring (α : R →+* A) (a : A) : inr a ∈ α.dualSubring := by
  simp [RingHom.mem_dualSubring, zero_mem]

lemma RingHom.inl_mem_dualSubring (α : R →+* A) (r : R) : inl (α r) ∈ α.dualSubring := by
  simp [RingHom.mem_dualSubring]

/-- The inclusion `R →+* α(R) + εA`. -/
def RingHom.toDualSubring (α : R →+* A) : R →+* α.dualSubring :=
  ((inlHom A A).comp α).codRestrict _ fun r ↦ α.inl_mem_dualSubring r

/-- The ring homomorphism `α(R) + εA →+* α'(R') + εA'` induced by a commutative square. -/
def RingHom.dualSubringMap (α : R →+* A) (α' : R' →+* A') (ρR : R →+* R') (ρ : A →+* A')
    (h : ρ.comp α = α'.comp ρR) : α.dualSubring →+* α'.dualSubring :=
  (DualNumber.map ρ).restrict _ _ fun z hz ↦ by
    obtain ⟨r, hr⟩ := RingHom.mem_dualSubring.mp hz
    refine RingHom.mem_dualSubring.mpr ⟨ρR r, ?_⟩
    rw [DualNumber.fst_map, ← hr]
    exact (RingHom.congr_fun h r).symm


@[simp]
lemma RingHom.coe_dualSubringMap (α : R →+* A) (α' : R' →+* A') (ρR : R →+* R') (ρ : A →+* A')
    (h : ρ.comp α = α'.comp ρR) (z : α.dualSubring) :
    (RingHom.dualSubringMap α α' ρR ρ h z : DualNumber A') = DualNumber.map ρ z :=
  rfl

@[simp]
lemma RingHom.coe_toDualSubring (α : R →+* A) (r : R) :
    (α.toDualSubring r : DualNumber A) = inl (α r) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Formation of `α(R) + εA` commutes with localization away from an element of `R`. -/
lemma RingHom.isLocalization_dualSubringMap (α : R →+* A) (α' : R' →+* A') (ρR : R →+* R')
    (ρ : A →+* A') (h : ρ.comp α = α'.comp ρR) (r : R)
    (hR : letI := ρR.toAlgebra; IsLocalization.Away r R')
    (hA : letI := ρ.toAlgebra; IsLocalization.Away (α r) A') :
    letI := (RingHom.dualSubringMap α α' ρR ρ h).toAlgebra
    IsLocalization.Away (α.toDualSubring r) α'.dualSubring := by
  let := ρR.toAlgebra
  let := ρ.toAlgebra
  let := (RingHom.dualSubringMap α α' ρR ρ h).toAlgebra
  have hcomm (t : R) : ρ (α t) = α' (ρR t) := RingHom.congr_fun h t
  have hφ (z : α.dualSubring) : (algebraMap α.dualSubring α'.dualSubring z : DualNumber A') =
      DualNumber.map ρ z := rfl
  have hu : IsUnit (ρR r) := IsLocalization.Away.algebraMap_isUnit (S := R') r
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · refine isUnit_iff_exists_inv.mpr ⟨α'.toDualSubring ↑hu.unit⁻¹, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hφ, RingHom.coe_toDualSubring, RingHom.coe_toDualSubring,
      Subring.coe_one]
    ext
    · simp only [fst_mul, DualNumber.fst_map, fst_inl, fst_one, hcomm, ← map_mul,
        IsUnit.mul_val_inv, map_one]
    · simp
  · intro z
    obtain ⟨t', ht'⟩ := RingHom.mem_dualSubring.mp z.2
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj r t'
    obtain ⟨m, b, hm⟩ := IsLocalization.Away.surj (α r) (z : DualNumber A').snd
    rw [RingHom.algebraMap_toAlgebra] at hn hm
    refine ⟨n + m, ⟨inl (α (a * r ^ m)) + inr (b * α r ^ n), ?_⟩, Subtype.ext ?_⟩
    · exact RingHom.mem_dualSubring.mpr ⟨a * r ^ m, by simp⟩
    rw [Subring.coe_mul, ← map_pow, hφ, hφ, SubmonoidClass.coe_pow, RingHom.coe_toDualSubring]
    ext
    · simp only [fst_mul, fst_pow, DualNumber.fst_map, fst_inl, fst_add, fst_inr, add_zero,
        ← ht', hcomm, map_mul, map_pow, pow_add, ← mul_assoc]
      rw [← map_pow α' (ρR r) n, ← map_mul, hn]
    · simp only [snd_mul, fst_pow, snd_pow, DualNumber.fst_map, DualNumber.snd_map, fst_inl,
        snd_inl, snd_add, snd_inr, smul_zero, map_mul, map_pow,
        smul_eq_mul, op_smul_eq_mul, mul_zero, zero_add, pow_add, ← mul_assoc, ← hm, map_zero]
      ring
  · intro x y hxy
    have h1 := congrArg (fun z : α'.dualSubring ↦ (z : DualNumber A').fst) hxy
    have h2 := congrArg (fun z : α'.dualSubring ↦ (z : DualNumber A').snd) hxy
    simp only [hφ, DualNumber.fst_map, DualNumber.snd_map] at h1 h2
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') (α r) h1
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := A') (α r) h2
    refine ⟨n + m, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, RingHom.coe_toDualSubring]
    ext
    · simp only [fst_mul, fst_pow, fst_inl, pow_add]
      linear_combination (α r) ^ m * hn
    · simp only [snd_mul, fst_mul, fst_pow, snd_pow, fst_inl, snd_inl, smul_zero, add_zero,
        smul_eq_mul, mul_zero, pow_add]
      linear_combination (α r) ^ n * hm


set_option backward.isDefEq.respectTransparency false in
/-- Let `A'` be the localization of `A` away from `s`, let `B ⊆ A` be a subring containing `s`,
and let `B' ⊆ A'` be a subring containing `ρ(B)` and the inverse of `ρ(s)`, every element of which
is a fraction `ρ(b) / ρ(s) ^ n` with `b ∈ B`. Then `B'` is the localization of `B` away from
`s`. -/
lemma Subring.isLocalization_away_of_le (ρ : A →+* A') (s : A)
    (hA : letI := ρ.toAlgebra; IsLocalization.Away s A') (B : Subring A) (B' : Subring A')
    (hs : s ∈ B) (hBB' : ∀ b ∈ B, ρ b ∈ B') (hinv : ∃ u ∈ B', u * ρ s = 1)
    (hfrac : ∀ b' ∈ B', ∃ b ∈ B, ∃ n : ℕ, b' * ρ s ^ n = ρ b) :
    letI := (ρ.restrict B B' hBB').toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : B) B' := by
  let := ρ.toAlgebra
  let := (ρ.restrict B B' hBB').toAlgebra
  have hφ (b : B) : (algebraMap B B' b : A') = ρ b := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · obtain ⟨u, hu, hus⟩ := hinv
    refine isUnit_iff_exists_inv.mpr ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hφ, mul_comm]
    exact hus
  · intro z
    obtain ⟨b, hb, n, hn⟩ := hfrac z z.2
    refine ⟨n, ⟨b, hb⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, ← map_pow, hφ, hφ]
    simpa using hn
  · intro x y hxy
    have h1 : algebraMap A A' x = algebraMap A A' y := congrArg Subtype.val hxy
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s h1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩


/-- If `α : R →+* A` is integral and `s ⊆ A` is finite, then `R →+* closure (α(R) ∪ s)` is
finite. -/
lemma RingHom.finite_codRestrict_closure (α : R →+* A) (hα : α.IsIntegral) (B : Subring A)
    {s : Set A} (hs : s.Finite) (hB : B = Subring.closure (Set.range α ∪ s))
    (h : ∀ r, α r ∈ B) : (α.codRestrict B h).Finite := by
  subst hB
  let := α.toAlgebra
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral hs (fun x _ ↦ hα x)
  have heq : (Algebra.adjoin R s).toSubring = Subring.closure (Set.range α ∪ s) :=
    Algebra.adjoin_eq_ring_closure s
  revert h
  rw [← heq]
  intro h
  exact hfin
end Ring

namespace AlgebraicGeometry.Scheme.AffineZariskiSite

open TrivSqZeroExt

variable {S : Scheme.{u}} {F : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (toOpensFunctor S).op ⋙ S.presheaf ⟶ F}

lemma comp_hom_eq_of_naturality {U V : S.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    (F.map i).hom.comp (α.app U).hom =
      (α.app V).hom.comp (S.presheaf.map ((toOpensFunctor S).op.map i)).hom :=
  congrArg CommRingCat.Hom.hom (α.naturality i).symm

variable (α) in
/-- The quasi-coherent `𝒪_S`-algebra `𝒪_S + ε F ⊆ F[ε]` attached to a quasi-coherent
`𝒪_S`-algebra `F`. Its quasi-coherent ideals contained in `ε F` are the quasi-coherent
`𝒪_S`-submodules of `F`. -/
@[simps]
noncomputable def dualAlg : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (α.app U).hom.dualSubring
  map {U V} i := CommRingCat.ofHom (RingHom.dualSubringMap (α.app U).hom (α.app V).hom
    (S.presheaf.map ((toOpensFunctor S).op.map i)).hom (F.map i).hom
    (comp_hom_eq_of_naturality i))
  map_id U := by
    ext z <;> simp [RingHom.coe_dualSubringMap]
  map_comp {U V W} i j := by
    ext z <;> simp [RingHom.coe_dualSubringMap]

variable (α) in
/-- The structure morphism `𝒪_S ⟶ 𝒪_S + ε F`. -/
@[simps]
noncomputable def dualAlgMap : (toOpensFunctor S).op ⋙ S.presheaf ⟶ dualAlg α where
  app U := CommRingCat.ofHom (α.app U).hom.toDualSubring
  naturality {U V} i := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext (TrivSqZeroExt.ext ?_ ?_))
    · change (α.app V).hom ((S.presheaf.map _).hom r) = (F.map i).hom ((α.app U).hom r) + 0
      rw [add_zero]
      exact ConcreteCategory.congr_hom (α.naturality i) r
    · change (0 : F.obj V) = 0 + (F.map i).hom 0
      simp

variable (α) in
/-- The projection `𝒪_S + ε F ⟶ F` onto the first component. -/
@[simps]
noncomputable def dualAlgFst : dualAlg α ⟶ F where
  app U := CommRingCat.ofHom ((fstHom ℤ _ _).toRingHom.comp (α.app U).hom.dualSubring.subtype)
  naturality {U V} i := by
    refine CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_)
    change (DualNumber.map (F.map i).hom z.1).fst = _
    exact DualNumber.fst_map _ _

lemma dualAlgMap_comp_dualAlgFst : dualAlgMap α ≫ dualAlgFst α = α := by
  ext U r
  rfl

lemma coequifibered_dualAlgMap (H : α.Coequifibered) : (dualAlgMap α).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  have hR : IsLocalization.Away r Γ(S, S.basicOpen r) := U.2.isLocalization_basicOpen r
  exact RingHom.isLocalization_dualSubringMap _ _ _ _ (comp_hom_eq_of_naturality _) r hR
    (coequifibered_iff_forall_isLocalizationAway.mp H U r)


section Approximation

variable (H : α.Coequifibered)

/-- The relative spectrum `D = Spec_S (𝒪_S + ε F)`. -/
noncomputable abbrev dualGlueData :=
  relativeGluingData (coequifibered_dualAlgMap H)

/-- The closed immersion `Spec_S F ⟶ Spec_S (𝒪_S + ε F)` induced by the projection onto the first
component. -/
noncomputable abbrev dualGluedι :
    (relativeGluingData H).glued ⟶ (dualGlueData H).glued :=
  relativeGluingMap (coequifibered_dualAlgMap H) H (dualAlgFst α)

@[reassoc (attr := simp)]
lemma dualGluedι_toBase :
    dualGluedι H ≫ (dualGlueData H).toBase = (relativeGluingData H).toBase :=
  relativeGluingMap_toBase _ _ _ dualAlgMap_comp_dualAlgFst

instance : IsAffineHom (dualGluedι H) := by
  have : IsAffineHom (dualGluedι H ≫ (dualGlueData H).toBase) := by
    rw [dualGluedι_toBase]; infer_instance
  exact IsAffineHom.of_comp _ (dualGlueData H).toBase

/-- The preimage in `D` of an affine open `U` of `S`, as an affine open. -/
noncomputable def dualAffineOpen (U : S.AffineZariskiSite) : (dualGlueData H).glued.affineOpens :=
  ⟨(dualGlueData H).toBase ⁻¹ᵁ U.1, U.2.preimage _⟩

/-- The sections of `D` over the preimage of `U` are `𝒪_S(U) + ε F(U)`. -/
noncomputable def dualSectionsEquiv (U : S.AffineZariskiSite) :
    Γ((dualGlueData H).glued, (dualAffineOpen H U).1) ≃+* (dualAlg α).obj (.op U) :=
  (sectionsIso (coequifibered_dualAlgMap H) U).commRingCatIsoToRingEquiv

lemma mem_ker_dualGluedι_iff (U : S.AffineZariskiSite)
    (z : Γ((dualGlueData H).glued, (dualAffineOpen H U).1)) :
    z ∈ (dualGluedι H).ker.ideal (dualAffineOpen H U) ↔
      (dualSectionsEquiv H U z).1.fst = 0 := by
  have hpre := relativeGluingMap_preimage (coequifibered_dualAlgMap H) H (dualAlgFst α)
    dualAlgMap_comp_dualAlgFst U
  have key := ConcreteCategory.congr_hom
    (relativeGluingMap_appLE_sectionsIso_hom (coequifibered_dualAlgMap H) H
    (dualAlgFst α) dualAlgMap_comp_dualAlgFst U) z
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have hinj : Function.Injective ((relativeGluingData H).glued.presheaf.map
      (homOfLE hpre.ge).op).hom := by
    have : IsIso (homOfLE hpre.ge).op := (eqToIso hpre).op.isIso_inv
    exact (ConcreteCategory.bijective_of_isIso _).1
  have hinj' : Function.Injective (sectionsIso H U).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  change _ ↔ (dualAlgFst α).app (.op U) ((sectionsIso (coequifibered_dualAlgMap H) U).hom z) = 0
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at key
  rw [← key, ← map_zero (sectionsIso H U).hom.hom, hinj'.eq_iff, Scheme.Hom.appLE,
    CommRingCat.comp_apply, ← map_zero ((relativeGluingData H).glued.presheaf.map
      (homOfLE hpre.ge).op).hom, hinj.eq_iff]
  exact Iff.rfl


lemma dualAffineOpen_le {U V : S.AffineZariskiSite} (i : V ⟶ U) :
    dualAffineOpen H V ≤ dualAffineOpen H U :=
  (dualGlueData H).toBase.preimage_mono (toOpens_mono i.le)

lemma dualSectionsEquiv_res {U V : S.AffineZariskiSite} (i : V ⟶ U)
    (z : Γ((dualGlueData H).glued, (dualAffineOpen H U).1)) :
    dualSectionsEquiv H V ((dualGlueData H).glued.presheaf.map
      (homOfLE (dualAffineOpen_le H i)).op z) = (dualAlg α).map i.op (dualSectionsEquiv H U z) :=
  ConcreteCategory.congr_hom (sectionsIso_hom_naturality (coequifibered_dualAlgMap H) i) z

/-- The element `ε m` of `𝒪_S(U) + ε F(U)`. -/
def dualInr {U : S.AffineZariskiSite} (m : F.obj (.op U)) : (dualAlg α).obj (.op U) :=
  ⟨inr m, RingHom.inr_mem_dualSubring _ m⟩

lemma dualAlg_map_dualInr {U V : S.AffineZariskiSite} (i : V ⟶ U) (m : F.obj (.op U)) :
    (dualAlg α).map i.op (dualInr m) = dualInr ((F.map i.op) m) := by
  refine Subtype.ext (TrivSqZeroExt.ext ?_ ?_)
  · change (F.map i.op).hom 0 + 0 = 0
    simp
  · change 0 + (F.map i.op).hom m = (F.map i.op).hom m
    simp

lemma eq_dualInr_of_fst_eq_zero {U : S.AffineZariskiSite} (z : (dualAlg α).obj (.op U))
    (hz : z.1.fst = 0) : z = dualInr z.1.snd :=
  Subtype.ext (TrivSqZeroExt.ext hz rfl)

variable {H} in
/-- The `𝒪_S(U)`-submodule of `F(U)` attached to an ideal sheaf `J` on `D` contained in `ε F`. -/
def subMod (J : (dualGlueData H).glued.IdealSheafData) (U : S.AffineZariskiSite) :
    Set (F.obj (.op U)) :=
  {m | (dualSectionsEquiv H U).symm (dualInr m) ∈ J.ideal (dualAffineOpen H U)}

variable {H} in
/-- The subalgebra of `F(U)` generated by `subMod J U`. -/
def subAlg (J : (dualGlueData H).glued.IdealSheafData) (U : S.AffineZariskiSite) :
    Subring (F.obj (.op U)) :=
  Subring.closure (Set.range (α.app (.op U)) ∪ subMod J U)

lemma subMod_mono {J J' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J')
    (U : S.AffineZariskiSite) : subMod J U ⊆ subMod J' U :=
  fun _ hm ↦ h _ hm

lemma subAlg_mono {J J' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J')
    (U : S.AffineZariskiSite) : subAlg J U ≤ subAlg J' U :=
  Subring.closure_mono (Set.union_subset_union_right _ (subMod_mono H h U))

lemma algebraMap_mem_subAlg (J : (dualGlueData H).glued.IdealSheafData) (U : S.AffineZariskiSite)
    (r : Γ(S, U.1)) : α.app (.op U) r ∈ subAlg J U :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

lemma subMod_subset_subAlg (J : (dualGlueData H).glued.IdealSheafData)
    (U : S.AffineZariskiSite) : subMod J U ⊆ subAlg J U :=
  fun _ hm ↦ Subring.subset_closure (Or.inr hm)

lemma map_mem_subMod (J : (dualGlueData H).glued.IdealSheafData) {U V : S.AffineZariskiSite}
    (i : V ⟶ U) {m : F.obj (.op U)} (hm : m ∈ subMod J U) : F.map i.op m ∈ subMod J V := by
  have h := J.ideal_le_comap_ideal (dualAffineOpen_le H i) hm
  rw [Ideal.mem_comap] at h
  change (dualSectionsEquiv H V).symm _ ∈ J.ideal (dualAffineOpen H V)
  convert h using 1
  apply (dualSectionsEquiv H V).injective
  rw [RingEquiv.apply_symm_apply, ← dualAlg_map_dualInr]
  erw [dualSectionsEquiv_res H i]
  rw [RingEquiv.apply_symm_apply]

lemma map_mem_subAlg (J : (dualGlueData H).glued.IdealSheafData) {U V : S.AffineZariskiSite}
    (i : V ⟶ U) {b : F.obj (.op U)} (hb : b ∈ subAlg J U) : F.map i.op b ∈ subAlg J V := by
  rw [subAlg, ← Subring.mem_comap] at *
  refine (Subring.closure_le.mpr ?_) hb
  rintro x (⟨r, rfl⟩ | hx)
  · rw [SetLike.mem_coe, Subring.mem_comap, ← CommRingCat.comp_apply, ← α.naturality]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subring.subset_closure (Or.inr (map_mem_subMod H J i hx))


lemma snd_dualInr_mul {U : S.AffineZariskiSite} (m : F.obj (.op U)) (y : (dualAlg α).obj (.op U)) :
    (dualInr m * y).1.snd = m * y.1.fst := by
  change (inr m * y.1 : DualNumber (F.obj (.op U))).snd = _
  simp [mul_comm]

lemma fst_dualInr_mul {U : S.AffineZariskiSite} (m : F.obj (.op U)) (y : (dualAlg α).obj (.op U)) :
    (dualInr m * y).1.fst = 0 := by
  change (inr m * y.1 : DualNumber (F.obj (.op U))).fst = _
  simp


lemma exists_mul_pow_eq_of_mem_subMod (J : (dualGlueData H).glued.IdealSheafData)
    (hJ : J ≤ (dualGluedι H).ker) (U : S.AffineZariskiSite) (r : Γ(S, U.1))
    {m' : F.obj (.op (U.basicOpen r))} (hm' : m' ∈ subMod J (U.basicOpen r)) :
    ∃ m ∈ subMod J U, ∃ n : ℕ, m' * (F.map (homOfLE (U.basicOpen_le r)).op (α.app _ r)) ^ n =
      F.map (homOfLE (U.basicOpen_le r)).op m := by
  let i : U.basicOpen r ⟶ U := homOfLE (U.basicOpen_le r)
  let eU := dualSectionsEquiv H U
  let eV := dualSectionsEquiv H (U.basicOpen r)
  let ρ := ((dualAlg α).map i.op).hom
  let res := ((dualGlueData H).glued.presheaf.map (homOfLE (dualAffineOpen_le H i)).op).hom
  have hcomm : eV.toRingHom.comp res = ρ.comp eU.toRingHom :=
    RingHom.ext fun z ↦ dualSectionsEquiv_res H i z
  have h1 : eV.symm (dualInr m') ∈ (J.ideal (dualAffineOpen H U)).map res := by
    rw [J.map_ideal (dualAffineOpen_le H i)]
    exact hm'
  have h2 : dualInr m' ∈ ((J.ideal (dualAffineOpen H U)).map eU.toRingHom).map ρ := by
    rw [Ideal.map_map, ← hcomm, ← Ideal.map_map]
    have := Ideal.mem_map_of_mem eV.toRingHom h1
    rwa [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at this
  let := ρ.toAlgebra
  have hloc := coequifibered_iff_forall_isLocalizationAway.mp (coequifibered_dualAlgMap H) U r
  obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxn⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers
      ((dualAlgMap α).app (.op U) r)) ((dualAlg α).obj (.op (U.basicOpen r)))).mp h2
  rw [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, Ideal.mem_comap] at hx
  obtain ⟨w, rfl⟩ : ∃ w, eU w = x := ⟨eU.symm x, eU.apply_symm_apply x⟩
  rw [RingEquiv.symm_apply_apply] at hx
  have hw := hx
  have hw0 : (eU w).1.fst = 0 := (mem_ker_dualGluedι_iff H U w).mp (hJ _ hw)
  refine ⟨(eU w).1.snd, ?_, n, ?_⟩
  · change eU.symm (dualInr _) ∈ J.ideal (dualAffineOpen H U)
    rwa [← eq_dualInr_of_fst_eq_zero _ hw0, RingEquiv.symm_apply_apply]
  · have := congrArg (fun z : (dualAlg α).obj (.op (U.basicOpen r)) ↦ z.1.snd) hxn
    simp only at this
    rw [snd_dualInr_mul] at this
    convert this using 2
    · change _ = (DualNumber.map (F.map i.op).hom (inl ((α.app (.op U)).hom r) ^ n)).fst
      simp
      rfl
    · change _ = (DualNumber.map (F.map i.op).hom (eU w).1).snd
      simp
      rfl


lemma exists_mul_pow_eq_of_mem_subAlg (J : (dualGlueData H).glued.IdealSheafData)
    (hJ : J ≤ (dualGluedι H).ker) (U : S.AffineZariskiSite) (r : Γ(S, U.1))
    {b' : F.obj (.op (U.basicOpen r))} (hb' : b' ∈ subAlg J (U.basicOpen r)) :
    ∃ b ∈ subAlg J U, ∃ n : ℕ, b' * (F.map (homOfLE (U.basicOpen_le r)).op (α.app _ r)) ^ n =
      F.map (homOfLE (U.basicOpen_le r)).op b := by
  set ρ := (F.map (homOfLE (U.basicOpen_le r)).op).hom
  set s := (α.app (.op U)).hom r
  have hs : s ∈ subAlg J U := algebraMap_mem_subAlg H J U r
  induction hb' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨t', rfl⟩ | hx
    · let := (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom.toAlgebra
      have : IsLocalization.Away r Γ(S, S.basicOpen r) := U.2.isLocalization_basicOpen r
      obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj (S := Γ(S, S.basicOpen r)) r t'
      refine ⟨(α.app (.op U)).hom a, algebraMap_mem_subAlg H J U a, n, ?_⟩
      have hnat (t : Γ(S, U.1)) : ρ ((α.app (.op U)).hom t) =
          (α.app (.op (U.basicOpen r))).hom (S.presheaf.map (homOfLE (S.basicOpen_le r)).op t) :=
        (ConcreteCategory.congr_hom (α.naturality (homOfLE (U.basicOpen_le r)).op) t).symm
      change _ * ρ s ^ n = _
      rw [hnat, hnat, ← map_pow, ← map_mul]
      exact congrArg _ hn
    · obtain ⟨m, hm, n, hn⟩ := exists_mul_pow_eq_of_mem_subMod H J hJ U r hx
      exact ⟨m, subMod_subset_subAlg H J U hm, n, hn⟩
  | zero => exact ⟨0, zero_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b₁, hb₁, n₁, h₁⟩ := hx
    obtain ⟨b₂, hb₂, n₂, h₂⟩ := hy
    refine ⟨b₁ * s ^ n₂ + b₂ * s ^ n₁, add_mem (mul_mem hb₁ (pow_mem hs _))
      (mul_mem hb₂ (pow_mem hs _)), n₁ + n₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
    ring
  | neg x _ hx =>
    obtain ⟨b, hb, n, h⟩ := hx
    exact ⟨-b, neg_mem hb, n, by rw [map_neg, ← h, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b₁, hb₁, n₁, h₁⟩ := hx
    obtain ⟨b₂, hb₂, n₂, h₂⟩ := hy
    refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, n₁ + n₂, ?_⟩
    rw [map_mul, ← h₁, ← h₂]
    ring


variable {H} in
/-- The restriction maps of the subalgebra attached to `J`. -/
noncomputable def subAlgRes (J : (dualGlueData H).glued.IdealSheafData)
    {U V : S.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    CommRingCat.of (subAlg J U.unop) ⟶ CommRingCat.of (subAlg J V.unop) :=
  CommRingCat.ofHom ((F.map i).hom.restrict _ _ fun _ hb ↦ map_mem_subAlg H J i.unop hb)

lemma subAlgRes_apply_coe (J : (dualGlueData H).glued.IdealSheafData)
    {U V : S.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) (b : subAlg J U.unop) :
    ((subAlgRes J i).hom b).1 = (F.map i).hom b.1 :=
  RingHom.coe_restrict_apply (F.map i).hom _ _ (fun _ hb ↦ map_mem_subAlg H J i.unop hb) b

variable {H} in
/-- The quasi-coherent `𝒪_S`-subalgebra of `F` generated by the submodule attached to `J`. -/
noncomputable def subAlgFunctor (J : (dualGlueData H).glued.IdealSheafData) :
    S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (subAlg J U.unop)
  map i := subAlgRes J i
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun b ↦ Subtype.ext ?_)
    rw [subAlgRes_apply_coe, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply,
      CommRingCat.hom_id, RingHom.id_apply]
  map_comp i j := by
    refine CommRingCat.hom_ext (RingHom.ext fun b ↦ Subtype.ext ?_)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, subAlgRes_apply_coe, subAlgRes_apply_coe,
      subAlgRes_apply_coe, CategoryTheory.Functor.map_comp, CommRingCat.hom_comp,
      RingHom.comp_apply]

lemma subAlgFunctor_map (J : (dualGlueData H).glued.IdealSheafData)
    {U V : S.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) : (subAlgFunctor J).map i = subAlgRes J i :=
  rfl


variable {H} in
/-- The components of the structure morphism `𝒪_S ⟶ subAlgFunctor J`. -/
noncomputable def subAlgMapApp (J : (dualGlueData H).glued.IdealSheafData)
    (U : S.AffineZariskiSiteᵒᵖ) : Γ(S, U.unop.1) ⟶ CommRingCat.of (subAlg J U.unop) :=
  CommRingCat.ofHom ((α.app U).hom.codRestrict _ (algebraMap_mem_subAlg H J U.unop))

lemma subAlgMapApp_apply_coe (J : (dualGlueData H).glued.IdealSheafData)
    (U : S.AffineZariskiSiteᵒᵖ) (r : Γ(S, U.unop.1)) :
    ((subAlgMapApp J U).hom r).1 = (α.app U).hom r :=
  RingHom.codRestrict_apply _ _ _ _

variable {H} in
/-- The structure morphism `𝒪_S ⟶ subAlgFunctor J`. -/
noncomputable def subAlgMap (J : (dualGlueData H).glued.IdealSheafData) :
    (toOpensFunctor S).op ⋙ S.presheaf ⟶ subAlgFunctor J where
  app U := subAlgMapApp J U
  naturality {U V} i := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext ?_)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (subAlgMapApp_apply_coe H J V _).trans
      ((ConcreteCategory.congr_hom (α.naturality i) r).trans
      ((congrArg (F.map i).hom (subAlgMapApp_apply_coe H J U r)).symm.trans
        (subAlgRes_apply_coe H J i _).symm))

lemma subAlgMap_app (J : (dualGlueData H).glued.IdealSheafData) (U : S.AffineZariskiSiteᵒᵖ) :
    (subAlgMap J).app U = subAlgMapApp J U :=
  rfl


variable {H} in
/-- The components of the inclusion of the subalgebras attached to `J ≤ J'`. -/
noncomputable def subAlgInclusionApp {J J' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J')
    (U : S.AffineZariskiSiteᵒᵖ) :
    CommRingCat.of (subAlg J U.unop) ⟶ CommRingCat.of (subAlg J' U.unop) :=
  CommRingCat.ofHom ((subAlg J U.unop).subtype.codRestrict _
    fun b ↦ subAlg_mono H h U.unop b.2)

lemma subAlgInclusionApp_apply_coe {J J' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J')
    (U : S.AffineZariskiSiteᵒᵖ) (b : subAlg J U.unop) :
    ((subAlgInclusionApp h U).hom b).1 = b.1 :=
  (RingHom.codRestrict_apply _ _ _ _).trans (Subring.subtype_apply _)

variable {H} in
/-- The inclusion of the subalgebras attached to ideal sheaves `J ≤ J'`. -/
noncomputable def subAlgInclusion {J J' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J') :
    subAlgFunctor J ⟶ subAlgFunctor J' where
  app U := subAlgInclusionApp h U
  naturality {U V} i := by
    refine CommRingCat.hom_ext (RingHom.ext fun b ↦ Subtype.ext ?_)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (subAlgInclusionApp_apply_coe H h V _).trans ((subAlgRes_apply_coe H J i b).trans
      ((congrArg (F.map i).hom (subAlgInclusionApp_apply_coe H h U b)).symm.trans
        (subAlgRes_apply_coe H J' i _).symm))

lemma subAlgInclusion_app {J J' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J')
    (U : S.AffineZariskiSiteᵒᵖ) : (subAlgInclusion h).app U = subAlgInclusionApp h U :=
  rfl


variable {H} in
/-- The components of the inclusion of the subalgebra attached to `J` into `F`. -/
noncomputable def subAlgιApp (J : (dualGlueData H).glued.IdealSheafData)
    (U : S.AffineZariskiSiteᵒᵖ) : CommRingCat.of (subAlg J U.unop) ⟶ F.obj U :=
  CommRingCat.ofHom (subAlg J U.unop).subtype

lemma subAlgιApp_apply (J : (dualGlueData H).glued.IdealSheafData)
    (U : S.AffineZariskiSiteᵒᵖ) (b : subAlg J U.unop) : (subAlgιApp J U).hom b = b.1 :=
  Subring.subtype_apply _

variable {H} in
/-- The inclusion of the subalgebra attached to `J` into `F`. -/
noncomputable def subAlgι (J : (dualGlueData H).glued.IdealSheafData) : subAlgFunctor J ⟶ F where
  app U := subAlgιApp J U
  naturality {U V} i := by
    refine CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (subAlgιApp_apply H J V _).trans ((subAlgRes_apply_coe H J i b).trans
      (congrArg (F.map i).hom (subAlgιApp_apply H J U b)).symm)

lemma subAlgι_app (J : (dualGlueData H).glued.IdealSheafData) (U : S.AffineZariskiSiteᵒᵖ) :
    (subAlgι J).app U = subAlgιApp J U :=
  rfl


lemma subAlgMap_comp_subAlgInclusion {J J' : (dualGlueData H).glued.IdealSheafData}
    (h : J ≤ J') : subAlgMap J ≫ subAlgInclusion h = subAlgMap J' := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
  refine Subtype.ext ?_
  rw [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (subAlgInclusionApp_apply_coe H h U _).trans
    ((subAlgMapApp_apply_coe H J U r).trans (subAlgMapApp_apply_coe H J' U r).symm)

lemma subAlgMap_comp_subAlgι (J : (dualGlueData H).glued.IdealSheafData) :
    subAlgMap J ≫ subAlgι J = α := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
  rw [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (subAlgιApp_apply H J U _).trans (subAlgMapApp_apply_coe H J U r)

lemma subAlgInclusion_comp_subAlgι {J J' : (dualGlueData H).glued.IdealSheafData}
    (h : J ≤ J') : subAlgInclusion h ≫ subAlgι J' = subAlgι J := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_))
  rw [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (subAlgιApp_apply H J' U _).trans
    ((subAlgInclusionApp_apply_coe H h U b).trans (subAlgιApp_apply H J U b).symm)

lemma subAlgInclusion_refl (J : (dualGlueData H).glued.IdealSheafData) :
    subAlgInclusion (le_refl J) = 𝟙 _ := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_))
  refine Subtype.ext ?_
  rw [NatTrans.id_app, CommRingCat.hom_id, RingHom.id_apply]
  exact subAlgInclusionApp_apply_coe H (le_refl J) U b

lemma subAlgInclusion_trans {J J' J'' : (dualGlueData H).glued.IdealSheafData} (h : J ≤ J')
    (h' : J' ≤ J'') : subAlgInclusion (h.trans h') = subAlgInclusion h ≫ subAlgInclusion h' := by
  refine NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_))
  refine Subtype.ext ?_
  rw [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (subAlgInclusionApp_apply_coe H (h.trans h') U b).trans
    ((subAlgInclusionApp_apply_coe H h' U _).trans (subAlgInclusionApp_apply_coe H h U b)).symm

lemma coequifibered_subAlgMap (J : (dualGlueData H).glued.IdealSheafData)
    (hJ : J ≤ (dualGluedι H).ker) : (subAlgMap J).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  set ρ := (F.map (homOfLE (U.basicOpen_le r)).op).hom
  have hA := coequifibered_iff_forall_isLocalizationAway.mp H U r
  let := (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom.toAlgebra
  have hR : IsLocalization.Away r Γ(S, S.basicOpen r) := U.2.isLocalization_basicOpen r
  have hu : IsUnit (S.presheaf.map (homOfLE (S.basicOpen_le r)).op r) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(S, S.basicOpen r)) r
  have hnat : ρ ((α.app (.op U)).hom r) =
      (α.app (.op (U.basicOpen r))).hom (S.presheaf.map (homOfLE (S.basicOpen_le r)).op r) :=
    (ConcreteCategory.congr_hom (α.naturality (homOfLE (U.basicOpen_le r)).op) r).symm
  refine Subring.isLocalization_away_of_le ρ _ hA (subAlg J U) (subAlg J (U.basicOpen r))
    (algebraMap_mem_subAlg H J U r) (fun _ hb ↦ map_mem_subAlg H J _ hb)
    ⟨(α.app (.op (U.basicOpen r))).hom (↑hu.unit⁻¹ : Γ(S, S.basicOpen r)),
      algebraMap_mem_subAlg H J _ _, ?_⟩
    fun b' hb' ↦ exists_mul_pow_eq_of_mem_subAlg H J hJ U r hb'
  rw [hnat, ← map_mul, IsUnit.val_inv_mul, map_one]


lemma exists_finset_subAlg_eq_closure (J : (dualGlueData H).glued.IdealSheafData)
    (hJ : J ≤ (dualGluedι H).ker) (U : S.AffineZariskiSite)
    (hfg : (J.ideal (dualAffineOpen H U)).FG) :
    ∃ s : Finset (F.obj (.op U)),
      subAlg J U = Subring.closure (Set.range (α.app (.op U)) ∪ s) := by
  classical
  obtain ⟨T, hT⟩ := hfg
  let eU := dualSectionsEquiv H U
  have hfst (x : Γ((dualGlueData H).glued, (dualAffineOpen H U).1))
      (hx : x ∈ J.ideal (dualAffineOpen H U)) : (eU x).1.fst = 0 :=
    (mem_ker_dualGluedι_iff H U x).mp (hJ _ hx)
  refine ⟨T.image fun t ↦ (eU t).1.snd, le_antisymm ?_ ?_⟩
  · refine Subring.closure_le.mpr (Set.union_subset (fun x hx ↦
      Subring.subset_closure (Or.inl hx)) fun m hm ↦ ?_)
    let C := Subring.closure (Set.range (α.app (.op U)) ∪
      ↑(T.image fun t ↦ (eU t).1.snd))
    have key : ∀ x ∈ J.ideal (dualAffineOpen H U), (eU x).1.snd ∈ C := by
      intro x hx
      rw [← hT] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Subring.subset_closure (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)))
      | zero => simp [zero_mem C]
      | add x y hx hy hx' hy' =>
        rw [map_add]
        exact add_mem hx' hy'
      | smul a x hx hx' =>
        have h0 := hfst x (hT ▸ hx)
        rw [smul_eq_mul, map_mul]
        change (eU a).1.fst * (eU x).1.snd + (eU a).1.snd * (eU x).1.fst ∈ C
        rw [h0, mul_zero, add_zero]
        obtain ⟨r, hr⟩ := RingHom.mem_dualSubring.mp (eU a).2
        exact mul_mem (Subring.subset_closure (Or.inl ⟨r, hr⟩)) hx'
    have := key _ hm
    rwa [RingEquiv.apply_symm_apply] at this
  · refine Subring.closure_mono (Set.union_subset_union_right _ ?_)
    intro m hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hm)
    have htJ : t ∈ J.ideal (dualAffineOpen H U) := hT ▸ Ideal.subset_span ht
    change eU.symm (dualInr _) ∈ J.ideal (dualAffineOpen H U)
    rwa [← eq_dualInr_of_fst_eq_zero _ (hfst t htJ), RingEquiv.symm_apply_apply]

lemma subAlgMap_app_finite (hα : ∀ U, (α.app U).hom.IsIntegral)
    (J : (dualGlueData H).glued.IdealSheafData) (hJ : J ≤ (dualGluedι H).ker)
    (hfg : ∀ U, (J.ideal U).FG) (U : S.AffineZariskiSiteᵒᵖ) :
    ((subAlgMap J).app U).hom.Finite := by
  obtain ⟨s, hs⟩ := exists_finset_subAlg_eq_closure H J hJ U.unop (hfg _)
  exact RingHom.finite_codRestrict_closure _ (hα U) _ s.finite_toSet hs _

instance [CompactSpace S] : CompactSpace (dualGlueData H).glued :=
  QuasiCompact.compactSpace_of_compactSpace (dualGlueData H).toBase

instance [QuasiSeparatedSpace S] : QuasiSeparatedSpace (dualGlueData H).glued :=
  quasiSeparatedSpace_of_quasiSeparated (dualGlueData H).toBase

/-- Every section of `F` over an affine open lies in the subalgebra attached to some ideal sheaf
of finite type contained in `ε F`. -/
lemma exists_fgSub_mem_subAlg [CompactSpace S] [QuasiSeparatedSpace S] (U : S.AffineZariskiSite)
    (a : F.obj (.op U)) : ∃ J : (dualGluedι H).ker.FGSub, a ∈ subAlg J.1 U := by
  have hs : (dualSectionsEquiv H U).symm (dualInr a) ∈
      (dualGluedι H).ker.ideal (dualAffineOpen H U) := by
    rw [mem_ker_dualGluedι_iff, RingEquiv.apply_symm_apply]
    exact TrivSqZeroExt.fst_inr _ a
  obtain ⟨J, hJK, hJfg, hJ⟩ := (dualGluedι H).ker.exists_finiteType_le_of_mem _ hs
  exact ⟨⟨J, hJK, hJfg⟩, subMod_subset_subAlg H J U hJ⟩


/-- The index category of the finite approximation: the subideal sheaves of finite type of the
kernel of `Spec_S F ⟶ Spec_S (𝒪_S + ε F)`, ordered by reverse inclusion. -/
abbrev ApproxIndex : Type u := ((dualGluedι H).ker.FGSub)ᵒᵖ

example : IsCofiltered (ApproxIndex H) := inferInstance

lemma coequifibered_approx (j : ApproxIndex H) : (subAlgMap (H := H) j.unop.1).Coequifibered :=
  coequifibered_subAlgMap H j.unop.1 j.unop.2.1

/-- The stages `Spec_S B_J` of the finite approximation. -/
noncomputable def approxDiagram : ApproxIndex H ⥤ Scheme.{u} where
  obj j := (relativeGluingData (coequifibered_approx H j)).glued
  map {j j'} f := relativeGluingMap (coequifibered_approx H j') (coequifibered_approx H j)
    (subAlgInclusion (leOfHom f.unop))
  map_id j := by
    rw [show subAlgInclusion (leOfHom (𝟙 j).unop) = subAlgInclusion (le_refl j.unop.1) from rfl,
      subAlgInclusion_refl, relativeGluingMap_id]
  map_comp {j j' j''} f g := by
    rw [show subAlgInclusion (leOfHom (f ≫ g).unop) = subAlgInclusion
        ((leOfHom g.unop).trans (leOfHom f.unop)) from rfl, subAlgInclusion_trans,
      relativeGluingMap_comp]

/-- The structure morphisms of the stages. -/
noncomputable def approxP (j : ApproxIndex H) : (approxDiagram H).obj j ⟶ S :=
  (relativeGluingData (coequifibered_approx H j)).toBase

lemma approxDiagram_map_approxP {j j' : ApproxIndex H} (f : j ⟶ j') :
    (approxDiagram H).map f ≫ approxP H j' = approxP H j :=
  relativeGluingMap_toBase _ _ _ (subAlgMap_comp_subAlgInclusion H _)

/-- The projections from `Spec_S F` to the stages. -/
noncomputable def approxπ : (Functor.const (ApproxIndex H)).obj (relativeGluingData H).glued ⟶
    approxDiagram H where
  app j := relativeGluingMap (coequifibered_approx H j) H (subAlgι j.unop.1)
  naturality {j j'} f := by
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map, approxDiagram]
    rw [Category.id_comp, ← relativeGluingMap_comp, subAlgInclusion_comp_subAlgι]

lemma approxπ_approxP (j : ApproxIndex H) :
    (approxπ H).app j ≫ approxP H j = (relativeGluingData H).toBase :=
  relativeGluingMap_toBase _ _ _ (subAlgMap_comp_subAlgι H _)

lemma isFinite_approxP (hα : ∀ U, (α.app U).hom.IsIntegral) (j : ApproxIndex H) :
    IsFinite (approxP H j) :=
  isFinite_toBase _ fun _ ↦ subAlgMap_app_finite H hα _ j.unop.2.1 j.unop.2.2 _


/-- The diagram of the rings `B_J(U)`, for an affine open `U`. -/
noncomputable def approxRingDiagram (U : S.AffineZariskiSite) :
    ApproxIndex H ⥤ CommRingCat.{u}ᵒᵖ where
  obj j := Opposite.op ((subAlgFunctor j.unop.1).obj (.op U))
  map {j j'} f := ((subAlgInclusion (leOfHom f.unop)).app (.op U)).op
  map_id j := by
    rw [show subAlgInclusion (leOfHom (𝟙 j).unop) = subAlgInclusion (le_refl j.unop.1) from rfl,
      subAlgInclusion_refl]
    rfl
  map_comp {j j' j''} f g := by
    rw [show subAlgInclusion (leOfHom (f ≫ g).unop) = subAlgInclusion
        ((leOfHom g.unop).trans (leOfHom f.unop)) from rfl,
      subAlgInclusion_trans H (leOfHom g.unop) (leOfHom f.unop)]
    rfl

/-- `F(U)` as a cocone over the rings `B_J(U)`. -/
noncomputable def approxRingCocone (U : S.AffineZariskiSite) (j₀ : ApproxIndex H) :
    Cocone (Over.forget j₀ ⋙ approxRingDiagram H U).leftOp where
  pt := F.obj (.op U)
  ι.app j := (subAlgι j.unop.left.unop.1).app (.op U)
  ι.naturality {j j'} f := by
    dsimp [approxRingDiagram]
    rw [Category.comp_id, ← NatTrans.comp_app, subAlgInclusion_comp_subAlgι]

/-- `F(U)` is the filtered union of the subalgebras `B_J(U)`. -/
noncomputable def isColimitApproxRingCocone [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.AffineZariskiSite) (j₀ : ApproxIndex H) : IsColimit (approxRingCocone H U j₀) := by
  have : ReflectsColimit (Over.forget j₀ ⋙ approxRingDiagram H U).leftOp
      (CategoryTheory.forget CommRingCat) := reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat)
    (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro a
    obtain ⟨J, hJ⟩ := exists_fgSub_mem_subAlg H U a
    obtain ⟨k, hk₀, hkJ, -⟩ := IsCofilteredOrEmpty.cone_objs j₀ (Opposite.op J)
    have hb : a ∈ subAlg k.unop.1 U := subAlg_mono H (leOfHom hkJ.unop) U hJ
    refine ⟨Opposite.op (Over.mk hk₀), ⟨a, hb⟩, ?_⟩
    exact (subAlgιApp_apply H k.unop.1 (.op U) ⟨a, hb⟩).symm
  · intro i x y hxy
    refine ⟨i, 𝟙 i, ?_⟩
    have : x = y := Subtype.ext ((subAlgιApp_apply H _ _ x).symm.trans
      (hxy.trans (subAlgιApp_apply H _ _ y)))
    rw [this]


/-- `Spec_S F` as a cone over the stages. -/
noncomputable abbrev approxCone : Cone (approxDiagram H) :=
  ⟨(relativeGluingData H).glued, approxπ H⟩

lemma approxDiagram_map_preimage {j₀ j : ApproxIndex H} (f : j ⟶ j₀) (U : S.AffineZariskiSite) :
    (approxDiagram H).map f ⁻¹ᵁ approxP H j₀ ⁻¹ᵁ U.1 =
      (colimit.ι (relativeGluingData (coequifibered_approx H j)).functor U).opensRange := by
  rw [← Scheme.Hom.comp_preimage, approxDiagram_map_approxP]
  exact toBase_preimage _ U

lemma approxπ_preimage (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) :
    (approxπ H).app j₀ ⁻¹ᵁ approxP H j₀ ⁻¹ᵁ U.1 =
      (colimit.ι (relativeGluingData H).functor U).opensRange := by
  rw [← Scheme.Hom.comp_preimage, approxπ_approxP]
  exact toBase_preimage _ U

lemma approx_ι_map {j j' : ApproxIndex H} (f : j ⟶ j') (U : S.AffineZariskiSite) :
    colimit.ι (relativeGluingData (coequifibered_approx H j)).functor U ≫ (approxDiagram H).map f =
      Scheme.Spec.map ((approxRingDiagram H U).map f) ≫
        colimit.ι (relativeGluingData (coequifibered_approx H j')).functor U :=
  ι_relativeGluingMap _ _ _ U

lemma approx_ι_π (j : ApproxIndex H) (U : S.AffineZariskiSite) :
    colimit.ι (relativeGluingData H).functor U ≫ (approxπ H).app j =
      Spec.map ((subAlgι j.unop.1).app (.op U)) ≫
        colimit.ι (relativeGluingData (coequifibered_approx H j)).functor U :=
  ι_relativeGluingMap _ _ _ U


lemma approx_ι_π' (j₀ : ApproxIndex H) (j : Over j₀) (U : S.AffineZariskiSite) :
    colimit.ι (relativeGluingData H).functor U ≫ (approxπ H).app j.left =
      Scheme.Spec.map ((approxRingCocone H U j₀).ι.app (Opposite.op j)).op ≫
        colimit.ι (relativeGluingData (coequifibered_approx H j.left)).functor U :=
  ι_relativeGluingMap _ _ _ U

/-- The restriction of a stage over an affine open `U` is `Spec B_J(U)`. -/
noncomputable def approxOpensIso (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) (j : Over j₀) :
    (opensDiagram (approxDiagram H) j₀ (approxP H j₀ ⁻¹ᵁ U.1)).obj j ≅
      ((Over.forget j₀ ⋙ approxRingDiagram H U) ⋙ Scheme.Spec).obj j :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _)
    (colimit.ι (relativeGluingData (coequifibered_approx H j.left)).functor U)
    ((Scheme.Opens.range_ι _).trans ((congrArg SetLike.coe
      (approxDiagram_map_preimage H j.hom U)).trans (Scheme.Hom.coe_opensRange _)))

@[reassoc (attr := simp)]
lemma approxOpensIso_hom_ι (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) (j : Over j₀) :
    (approxOpensIso H j₀ U j).hom ≫
      colimit.ι (relativeGluingData (coequifibered_approx H j.left)).functor U =
      Scheme.Opens.ι _ :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The restricted diagram of stages over an affine open `U` is the diagram `Spec B_J(U)`. -/
noncomputable def approxOpensDiagramIso (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) :
    opensDiagram (approxDiagram H) j₀ (approxP H j₀ ⁻¹ᵁ U.1) ≅
      (Over.forget j₀ ⋙ approxRingDiagram H U) ⋙ Scheme.Spec :=
  NatIso.ofComponents (approxOpensIso H j₀ U) fun {j j'} k ↦ by
    rw [← cancel_mono (colimit.ι (relativeGluingData (coequifibered_approx H j'.left)).functor U),
      Category.assoc, approxOpensIso_hom_ι, opensDiagram_map_ι]
    rw [Category.assoc, Functor.comp_map, Functor.comp_map, Over.forget_map, ← approx_ι_map,
      approxOpensIso_hom_ι_assoc]

/-- The restriction of `Spec_S F` over an affine open `U` is `Spec F(U)`. -/
noncomputable def approxConeOpensIso (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) :
    (opensCone (approxDiagram H) (approxCone H) j₀ (approxP H j₀ ⁻¹ᵁ U.1)).pt ≅
      Spec (F.obj (.op U)) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _)
    (colimit.ι (relativeGluingData H).functor U)
    ((Scheme.Opens.range_ι _).trans ((congrArg SetLike.coe
      (approxπ_preimage H j₀ U)).trans (Scheme.Hom.coe_opensRange _)))

lemma approxConeOpensIso_hom_ι (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) :
    (approxConeOpensIso H j₀ U).hom ≫ colimit.ι (relativeGluingData H).functor U =
      Scheme.Opens.ι _ :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The restriction of `Spec_S F` over an affine open `U` is the limit of the restrictions of
the stages. -/
noncomputable def isLimitApproxOpensCone [CompactSpace S] [QuasiSeparatedSpace S]
    (j₀ : ApproxIndex H) (U : S.AffineZariskiSite) :
    IsLimit (opensCone (approxDiagram H) (approxCone H) j₀ (approxP H j₀ ⁻¹ᵁ U.1)) := by
  have hS := isLimitOfPreserves Scheme.Spec
    (isLimitConeOfCoconeLeftOp _ (isColimitApproxRingCocone H U j₀))
  refine (IsLimit.postcomposeHomEquiv (approxOpensDiagramIso H j₀ U) _)
    (hS.ofIsoLimit (Cone.ext (approxConeOpensIso H j₀ U).symm fun j ↦ ?_))
  rw [Iso.symm_hom, Iso.eq_inv_comp]
  rw [← cancel_mono (colimit.ι (relativeGluingData (coequifibered_approx H j.left)).functor U)]
  simp only [Functor.mapCone_π_app, coneOfCoconeLeftOp_π_app, Cone.postcompose_obj_π,
    NatTrans.comp_app, approxOpensDiagramIso, NatIso.ofComponents_hom_app, Category.assoc]
  rw [← approx_ι_π', ← Category.assoc, approxConeOpensIso_hom_ι]
  exact (opensCone_π_ι (approxDiagram H) (approxCone H) j₀ _ j).symm.trans
    (congrArg _ (approxOpensIso_hom_ι H j₀ U j).symm)


/-- The bottom index of the finite approximation. -/
noncomputable abbrev approxBot : ApproxIndex H := Opposite.op ⊥

/-- **`Spec_S F` is the limit of the stages `Spec_S B_J`.** -/
noncomputable def isLimitApproxCone [CompactSpace S] [QuasiSeparatedSpace S] :
    IsLimit (approxCone H) :=
  isLimitOfIsLimitOpensCone' (approxDiagram H) (approxCone H) (approxBot H)
    (fun U : S.AffineZariskiSite ↦ approxP H (approxBot H) ⁻¹ᵁ U.1) (by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (approxP H (approxBot H) x)) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩)
    fun U ↦ isLimitApproxOpensCone H _ U

end Approximation

end AlgebraicGeometry.Scheme.AffineZariskiSite

namespace AlgebraicGeometry

open Scheme.AffineZariskiSite

/-- A **finite approximation** of a morphism `f : X ⟶ S` is a cofiltered system `D` of
schemes finite over `S` together with a limit cone with point `X` whose projections are
compatible with `f`: it presents `X` as a cofiltered limit of finite `S`-schemes. The transition
morphisms are then affine (`Scheme.Hom.FiniteApproximation.isAffineHom_map`). -/
structure Scheme.Hom.FiniteApproximation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of finite `S`-schemes. -/
  D : I ⥤ Scheme.{u}
  /-- The structure morphisms of the stages to `S`. -/
  p (i : I) : D.obj i ⟶ S
  /-- The transition morphisms are `S`-morphisms. -/
  map_p {i j : I} (g : i ⟶ j) : D.map g ≫ p j = p i
  /-- Every stage is finite over `S`. -/
  isFinite_p (i : I) : IsFinite (p i)
  /-- The morphisms from `X` to the stages. -/
  π : (Functor.const I).obj X ⟶ D
  /-- `X` is the limit of the stages. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The morphisms from `X` to the stages are compatible with `f`. -/
  π_p (i : I) : π.app i ≫ p i = f

namespace Scheme.Hom.FiniteApproximation

attribute [instance] smallCategory isCofiltered isFinite_p

variable {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FiniteApproximation)

/-- The transition morphisms of a finite approximation are affine. -/
instance isAffineHom_map {i j : F.I} (g : i ⟶ j) : IsAffineHom (F.D.map g) := by
  have : IsAffineHom (F.D.map g ≫ F.p j) := by rw [F.map_p]; infer_instance
  exact IsAffineHom.of_comp _ (F.p j)

instance compactSpace_obj [CompactSpace S] (i : F.I) : CompactSpace (F.D.obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (F.p i)

instance quasiSeparatedSpace_obj [QuasiSeparatedSpace S] (i : F.I) :
    QuasiSeparatedSpace (F.D.obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (F.p i)

end Scheme.Hom.FiniteApproximation

/-- **The relative spectrum of an integral quasi-coherent algebra is a limit of finite
schemes.** Let `F` be a quasi-coherent `𝒪_S`-algebra on a quasi-compact quasi-separated scheme
`S` which is integral over `𝒪_S`. Then `Spec_S F` is the cofiltered limit of the relative
spectra of the finite quasi-coherent subalgebras `B_J ⊆ F`, which are finite over `S`. -/
noncomputable def Scheme.AffineZariskiSite.finiteApproximation {S : Scheme.{u}}
    {F : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (toOpensFunctor S).op ⋙ S.presheaf ⟶ F} (H : α.Coequifibered)
    (hα : ∀ U, (α.app U).hom.IsIntegral) [CompactSpace S] [QuasiSeparatedSpace S] :
    (relativeGluingData H).toBase.FiniteApproximation where
  I := ApproxIndex H
  D := approxDiagram H
  p := approxP H
  map_p := approxDiagram_map_approxP H
  isFinite_p := isFinite_approxP H hα
  π := approxπ H
  isLimit := isLimitApproxCone H
  π_p := approxπ_approxP H

/-- **An integral morphism is a limit of finite morphisms** (the finite approximation of Stacks
Project Tag 09YZ, without the finite presentation of the stages). If `f : X ⟶ S` is integral and
`S` is quasi-compact and quasi-separated, then `X` is a cofiltered limit of schemes finite over
`S`. -/
theorem Scheme.Hom.nonempty_finiteApproximation_of_isIntegralHom {X S : Scheme.{u}}
    (f : X ⟶ S) [IsIntegralHom f] [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty f.FiniteApproximation := by
  have hα : ∀ U, (f.normalizationDiagramMap.app ((toOpensFunctor S).op.obj U)).hom.IsIntegral := by
    intro U
    let := (f.app U.unop.1).hom.toAlgebra
    change (algebraMap Γ(S, U.unop.1)
      (integralClosure Γ(S, U.unop.1) Γ(X, f ⁻¹ᵁ U.unop.1))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  let G := finiteApproximation f.coequifibered_normalizationDiagramMap hα
  let e := asIso f.toNormalization
  refine ⟨{ G with
    π := (Functor.const _).map e.hom ≫ G.π
    isLimit := G.isLimit.ofIsoLimit (Cone.ext e.symm fun i ↦ by simp)
    π_p i := by
      change e.hom ≫ G.π.app i ≫ G.p i = f
      rw [G.π_p]
      exact f.toNormalization_fromNormalization }⟩

end AlgebraicGeometry
