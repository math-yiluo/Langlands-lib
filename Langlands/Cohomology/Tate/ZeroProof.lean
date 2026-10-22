import Langlands.Cohomology.Tate.ZeroStatement

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable {A B C : Rep R G}

@[simp]
lemma zeroEquiv_zeroClass (a : A.ρ.invariants) :
    (zeroEquiv A).hom (zeroClass A a) = (normImage A).mkQ a := by
  simp [zeroClass, LinearMap.comp_apply]

lemma zeroClass_surjective (A : Rep R G) : Function.Surjective (zeroClass A) := by
  intro x
  obtain ⟨a, ha⟩ := (normImage A).mkQ_surjective ((zeroEquiv A).hom x)
  refine ⟨a, ?_⟩
  apply (ModuleCat.mono_iff_injective (zeroEquiv A).hom).mp inferInstance
  rw [zeroEquiv_zeroClass]
  exact ha

lemma zeroClass_eq_zero_iff (a : A.ρ.invariants) :
    zeroClass A a = 0 ↔ a ∈ normImage A := by
  constructor
  · intro h
    have hh : (zeroEquiv A).hom (zeroClass A a) = 0 := by rw [h, map_zero]
    rw [zeroEquiv_zeroClass] at hh
    exact (Submodule.Quotient.mk_eq_zero (normImage A)).mp hh
  · intro h
    apply (ModuleCat.mono_iff_injective (zeroEquiv A).hom).mp inferInstance
    rw [zeroEquiv_zeroClass, map_zero]
    exact (Submodule.Quotient.mk_eq_zero (normImage A)).mpr h

@[simp]
lemma cupZero_zeroClass (φ : Pairing A B C) (a : A.ρ.invariants) (b : B.ρ.invariants) :
    cupZero φ (zeroClass A a) (zeroClass B b) = zeroClass C (φ.onInvariants a b) := by
  simp [cupZero, Pairing.quotientProduct, Pairing.onInvariantClasses,
    zeroClass, LinearMap.comp_apply]

/-- The class map is natural for Mathlib's actual Tate coefficient functor. -/
lemma zeroClass_naturality_hom (f : A ⟶ B) :
    ModuleCat.ofHom (zeroClass A) ≫ (tateCohomologyFunctor 0).map f =
      (Rep.invariantsFunctor R G).map f ≫ ModuleCat.ofHom (zeroClass B) := by
  let ψ : zeroShortComplex A ⟶ zeroShortComplex B :=
    (zeroShortComplexIso A).inv ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).map
        (tateComplex.map f) ≫ (zeroShortComplexIso B).hom
  let γ := ShortComplex.leftHomologyMapData ψ (zeroHomologyData A) (zeroHomologyData B)
  have hψ : ψ.τ₂ = f.toModuleCatHom := by
    change (groupCohomology.cochainsIso₀ A).inv ≫
      (groupCohomology.cochainsMap (MonoidHom.id G) f).f 0 ≫
        (groupCohomology.cochainsIso₀ B).hom = f.toModuleCatHom
    rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]
    simp
  have hK : γ.φK = (Rep.invariantsFunctor R G).map f := by
    apply (cancel_mono (zeroHomologyData B).i).mp
    rw [γ.commi, hψ]
    rfl
  have hmap : (tateCohomologyFunctor 0).map f =
      (zeroEquiv A).hom ≫ γ.φH ≫ (zeroEquiv B).inv := by
    apply (cancel_mono (zeroEquiv B).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg
      (fun z => (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫ z)
      γ.homologyMap_comm
    simp only [ψ, ShortComplex.homologyMap_comp, Category.assoc] at hh
    change (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫
      (ShortComplex.homologyMapIso (zeroShortComplexIso A)).inv ≫
      (tateCohomologyFunctor 0).map f ≫
      (ShortComplex.homologyMapIso (zeroShortComplexIso B)).hom ≫
      (zeroHomologyData B).homologyIso.hom =
      (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫
      (zeroHomologyData A).homologyIso.hom ≫ γ.φH at hh
    simpa only [Iso.hom_inv_id_assoc, zeroEquiv, Iso.trans_hom, Category.assoc] using hh
  have hπ : ModuleCat.ofHom (normImage A).mkQ ≫ γ.φH =
      (Rep.invariantsFunctor R G).map f ≫ ModuleCat.ofHom (normImage B).mkQ := by
    simpa only [hK, zeroHomologyData] using γ.commπ
  change (ModuleCat.ofHom (normImage A).mkQ ≫ (zeroEquiv A).inv) ≫
    (tateCohomologyFunctor 0).map f =
      (Rep.invariantsFunctor R G).map f ≫
        (ModuleCat.ofHom (normImage B).mkQ ≫ (zeroEquiv B).inv)
  rw [hmap]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun z => z ≫ (zeroEquiv B).inv) hπ

lemma zeroClass_naturality (f : A ⟶ B) (a : A.ρ.invariants) :
    (tateCohomologyFunctor 0).map f (zeroClass A a) =
      zeroClass B ((Rep.invariantsFunctor R G).map f a) := by
  exact ConcreteCategory.congr_hom (zeroClass_naturality_hom f) a

lemma cupZero_naturality {A' B' C' : Rep R G}
    (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (hφ : ∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b))
    (a : tateCohomology A 0) (b : tateCohomology B 0) :
    (tateCohomologyFunctor 0).map h (cupZero φ a b) =
      cupZero φ' ((tateCohomologyFunctor 0).map f a)
        ((tateCohomologyFunctor 0).map g b) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A a
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  rw [cupZero_zeroClass, zeroClass_naturality, zeroClass_naturality,
    zeroClass_naturality, cupZero_zeroClass]
  congr 1
  exact Subtype.ext (hφ a b)

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

@[simp]
lemma restrictionZero_zeroClass (a : A.ρ.invariants) :
    restrictionZero H A (zeroClass A a) =
      zeroClass (Rep.res H.subtype A) (invariantRestriction H A a) := by
  simp [restrictionZero, quotientRestriction, zeroClass, LinearMap.comp_apply]

@[simp]
lemma corestrictionZero_zeroClass (a : (Rep.res H.subtype A).ρ.invariants) :
    corestrictionZero H A (zeroClass (Rep.res H.subtype A) a) =
      zeroClass A (cosetNorm H A a) := by
  simp [corestrictionZero, quotientCorestriction, zeroClass, LinearMap.comp_apply]

omit [Fintype G] [Fintype H] in
lemma cosetNorm_invariantRestriction (a : A.ρ.invariants) :
    cosetNorm H A (invariantRestriction H A a) = H.index • a := by
  apply Subtype.ext
  change (∑ q : G ⧸ H, cosetAction H A (invariantRestriction H A a) q) =
    H.index • (a : A)
  simp only [cosetAction_out]
  change (∑ q : G ⧸ H, A.ρ q.out a) = H.index • (a : A)
  have ha (g : G) : A.ρ g a = a := a.property g
  simp only [ha, Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]

lemma corestrictionZero_restrictionZero (x : tateCohomology A 0) :
    corestrictionZero H A (restrictionZero H A x) = H.index • x := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A x
  rw [restrictionZero_zeroClass, corestrictionZero_zeroClass,
    cosetNorm_invariantRestriction, map_nsmul]

lemma restrictionZero_cupZero (φ : Pairing A B C)
    (a : tateCohomology A 0) (b : tateCohomology B 0) :
    restrictionZero H C (cupZero φ a b) =
      cupZero (φ.restrict H) (restrictionZero H A a) (restrictionZero H B b) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A a
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  rw [cupZero_zeroClass, restrictionZero_zeroClass, restrictionZero_zeroClass,
    restrictionZero_zeroClass, cupZero_zeroClass]
  rfl

omit [Fintype G] [Fintype H] in
lemma cosetNorm_pairing (φ : Pairing A B C)
    (a : (Rep.res H.subtype A).ρ.invariants) (b : B.ρ.invariants) :
    cosetNorm H C ((φ.restrict H).onInvariants a (invariantRestriction H B b)) =
      φ.onInvariants (cosetNorm H A a) b := by
  apply Subtype.ext
  change (∑ q : G ⧸ H, cosetAction H C
    ((φ.restrict H).onInvariants a (invariantRestriction H B b)) q) =
    φ.bilinear (∑ q : G ⧸ H, cosetAction H A a q) b
  simp only [cosetAction_out, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  symm
  change φ.bilinear (A.ρ q.out a) b = C.ρ q.out (φ.bilinear a b)
  simpa only [b.property q.out] using φ.equivariant q.out a b

lemma corestrictionZero_projection (φ : Pairing A B C)
    (a : tateCohomology (Rep.res H.subtype A) 0) (b : tateCohomology B 0) :
    corestrictionZero H C (cupZero (φ.restrict H) a (restrictionZero H B b)) =
      cupZero φ (corestrictionZero H A a) b := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective (Rep.res H.subtype A) a
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  rw [restrictionZero_zeroClass, cupZero_zeroClass, corestrictionZero_zeroClass,
    corestrictionZero_zeroClass, cupZero_zeroClass, cosetNorm_pairing]

lemma restrictionZero_naturality (f : A ⟶ B) (a : tateCohomology A 0) :
    (tateCohomologyFunctor 0).map ((Rep.resFunctor H.subtype).map f)
        (restrictionZero H A a) =
      restrictionZero H B ((tateCohomologyFunctor 0).map f a) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A a
  rw [restrictionZero_zeroClass, zeroClass_naturality, zeroClass_naturality,
    restrictionZero_zeroClass]
  rfl

omit [Fintype G] [Fintype H] in
lemma cosetNorm_naturality (f : A ⟶ B) (a : (Rep.res H.subtype A).ρ.invariants) :
    (Rep.invariantsFunctor R G).map f (cosetNorm H A a) =
      cosetNorm H B ((Rep.invariantsFunctor R H).map ((Rep.resFunctor H.subtype).map f) a) := by
  apply Subtype.ext
  change f.hom (∑ q : G ⧸ H, cosetAction H A a q) =
    ∑ q : G ⧸ H, cosetAction H B
      ((Rep.invariantsFunctor R H).map ((Rep.resFunctor H.subtype).map f) a) q
  simp only [map_sum, cosetAction_out]
  apply Finset.sum_congr rfl
  intro q _
  exact Rep.hom_comm_apply f q.out a

lemma corestrictionZero_naturality (f : A ⟶ B)
    (a : tateCohomology (Rep.res H.subtype A) 0) :
    (tateCohomologyFunctor 0).map f (corestrictionZero H A a) =
      corestrictionZero H B
        ((tateCohomologyFunctor 0).map ((Rep.resFunctor H.subtype).map f) a) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective (Rep.res H.subtype A) a
  rw [corestrictionZero_zeroClass, zeroClass_naturality, zeroClass_naturality,
    corestrictionZero_zeroClass, cosetNorm_naturality]

/-- The complete degree-zero target, preserving the full carrier universe. -/
theorem zeroLaws : ZeroLaws.{u} := by
  intro R G _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact ⟨zeroClass_surjective A, zeroEquiv_zeroClass, zeroClass_eq_zero_iff⟩
  · intro A B f a
    exact zeroClass_naturality f a
  · intro A B C φ a b
    exact cupZero_zeroClass φ a b
  · intro A B C A' B' C' φ φ' f g h hφ a b
    exact cupZero_naturality φ φ' f g h hφ a b
  · intro H _ _
    refine ⟨?_, ?_, ?_⟩
    · intro A
      exact ⟨restrictionZero_zeroClass H, corestrictionZero_zeroClass H,
        corestrictionZero_restrictionZero H⟩
    · intro A B C φ
      exact ⟨restrictionZero_cupZero H φ, corestrictionZero_projection H φ⟩
    · intro A B f
      exact ⟨restrictionZero_naturality H f, corestrictionZero_naturality H f⟩

/-- Check the complete, unapplied theorem at the arbitrary carrier universe. -/
example : ZeroLaws.{u} := @zeroLaws.{u}

end Langlands.Tate
