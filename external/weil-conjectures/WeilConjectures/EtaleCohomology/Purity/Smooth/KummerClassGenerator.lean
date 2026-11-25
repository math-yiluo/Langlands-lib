/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine

/-!
# The Kummer class of the coordinate generates `H¹(𝔾_m, Λ(1))`

Let `k` be an algebraically closed field, `Λ` a finite ring whose characteristic `n` is invertible
in `k`, and `G = 𝔾_{m,k}` the complement of the zero section of `𝔸¹_k`, with coordinate `t`. The
Kummer class `κ(t) : Λ_G ⟶ Λ_G(1)[1]` (`AlgebraicGeometry.Etale.kummerClassOf`) is a free
generator: `c ↦ c • κ(t)` is a bijection
(`AlgebraicGeometry.Etale.bijective_smul_kummerClassOf`).

The proof compares `Ext¹(Λ_G, Λ(1))` with the cohomology `H¹(G, μₙ ⊗ Λ)` of the underlying
abelian sheaf (`AlgebraicGeometry.Etale.extToSheafH`); there the image of `κ(t)` is, up to a
scalar, the image of the Kummer class `δ(t) ∈ H¹(G, μₙ)` under `μₙ ⟶ μₙ ⊗ Λ`, and the
classical Kummer computation `H¹(G, μₙ) = ℤ/n · δ(t)` together with `End(Λ_G) = Λ` gives the
claim.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- On a connected scheme every endomorphism of the constant sheaf `Λ` is a scalar. -/
lemma exists_eq_smul_id_constantSheaf {X : Scheme.{u}} [ConnectedSpace X]
    (g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) :
    ∃ c : Λ, g = c • 𝟙 _ := by
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  obtain ⟨c, hc⟩ : ∃ c : Λ, adj.unit.app (ModuleCat.of Λ Λ) c = (adj.homEquiv _ _ g) (1 : Λ) :=
    (bijective_constantSheafΓAdj_unit_app Λ X).2 _
  refine ⟨c, (adj.homEquiv _ _).injective ?_⟩
  have h1 : c • 𝟙 ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) = (constantSheaf _ _).map (c • 𝟙 (ModuleCat.of Λ Λ)) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have key : adj.homEquiv _ _ ((constantSheaf _ _).map (c • 𝟙 (ModuleCat.of Λ Λ))) =
      (c • 𝟙 (ModuleCat.of Λ Λ)) ≫ adj.unit.app _ := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality (c • 𝟙 (ModuleCat.of Λ Λ))).symm
  rw [h1, key, Linear.smul_comp, Category.id_comp]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  rw [ModuleCat.hom_smul, LinearMap.smul_apply, ← map_smul, smul_eq_mul, mul_one]
  exact hc.symm

/-- An endomorphism of a sheaf isomorphic to the constant sheaf `Λ` on a connected scheme is a
scalar. -/
lemma exists_eq_smul_id_of_iso {X : Scheme.{u}} [ConnectedSpace X]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (σ : F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
    (g : F ⟶ F) : ∃ c : Λ, g = c • 𝟙 F := by
  obtain ⟨c, hc⟩ := exists_eq_smul_id_constantSheaf Λ (σ.inv ≫ g ≫ σ.hom)
  refine ⟨c, ?_⟩
  have : g = σ.hom ≫ (σ.inv ≫ g ≫ σ.hom) ≫ σ.inv := by simp
  rw [this, hc, Linear.smul_comp, Linear.comp_smul, Category.id_comp, σ.hom_inv_id]

section Comparison

variable {X : Scheme.{u}} {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
  (ε : (freeSheaf Λ X).obj (finalObject X) ≅ M)

omit [Finite Λ] in
/-- `Extⁿ(M, N) ⟶ Hⁿ(X, N)` for `M ≅ Λ[X]`: precompose with `ε` and compare with the cohomology
of the underlying abelian sheaf. -/
noncomputable def extToSheafH (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Abelian.Ext.{u + 1} M N n →+ Sheaf.H ((forget₂Sheaf Λ X).obj N) n :=
  (extFreeSheafToH Λ N n).comp ((Abelian.Ext.mk₀ ε.hom).precomp N (zero_add n))

omit [Finite Λ] in
lemma extToSheafH_apply (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (x : Abelian.Ext.{u + 1} M N n) :
    extToSheafH Λ ε N n x = extFreeSheafToH Λ N n ((Abelian.Ext.mk₀ ε.hom).comp x (zero_add n)) :=
  rfl

omit [Finite Λ] in
lemma bijective_extToSheafH [CompactSpace X] [QuasiSeparatedSpace X]
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Function.Bijective (extToSheafH Λ ε N n) :=
  (bijective_extFreeSheafToH Λ n N).comp (Abelian.Ext.precompAddEquiv ε N n).bijective

omit [Finite Λ] in
lemma extToSheafH_comp_mk₀ {N N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : N ⟶ N') (n : ℕ) (x : Abelian.Ext.{u + 1} M N n) :
    extToSheafH Λ ε N' n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map ((forget₂Sheaf Λ X).map g) n (extToSheafH Λ ε N n x) := by
  rw [extToSheafH_apply, extToSheafH_apply, ← extFreeSheafToH_comp_mk₀,
    ]
  congr 1
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

omit [Finite Λ] in
lemma extToSheafH_extClass {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) (ε : (freeSheaf Λ X).obj (finalObject X) ≅ S.X₃) :
    extToSheafH Λ ε S.X₁ 1 hS.extClass =
      (extFreeSheafToH Λ S.X₃ 0 (Abelian.Ext.mk₀ ε.hom)).comp
        (hS.map_of_exact (forget₂Sheaf Λ X)).extClass (zero_add 1) := by
  rw [extToSheafH_apply, ← extFreeSheafToH_comp_extClass]

end Comparison

section Kummer

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}}
  (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1))
    (Spec (.of k))).base)ᶜ) [HasInvertibleExponent Λ G] [NeZero (ringChar Λ)]

omit [Finite Λ] [IsAlgClosed k] [NeZero (ringChar Λ)] in
include hj in
lemma ringChar_natCast_ne_zero_of_multiplicativeGroup : ((ringChar Λ : ℕ) : k) ≠ 0 := by
  have := (connectedSpace_of_range_eq_compl_zeroSection j hj).toNonempty
  have := HasInvertibleExponent.of_hom_of_nonempty
    (j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) (Λ := Λ)
  have h := (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) (Spec (.of k))).map
    (Scheme.ΓSpecIso (.of k)).hom.hom
  rw [map_natCast] at h
  exact h.ne_zero

include hj in
/-- **The Kummer class of the coordinate generates `H¹(𝔾_{m,k}, Λ(1))`**: `c ↦ c • κ(t)` is a
bijection `Λ ≅ Hom(Λ, Λ(1)[1])`. -/
theorem bijective_smul_kummerClassOf :
    Function.Bijective (fun c : Λ ↦ c • kummerClassOf G Λ (AffineSpace.unitLineCoord j hj)) := by
  have hN := ringChar_natCast_ne_zero_of_multiplicativeGroup Λ j hj
  have := connectedSpace_of_range_eq_compl_zeroSection j hj
  have := AffineSpace.isAffine_of_range_eq_compl_zeroSection j hj
  let t := AffineSpace.unitLineCoord j hj
  let φ := Scheme.unitToGmSheaf t
  have hC : ∀ x : G, Projective ((G.uliftPointSmallEtale x).sheafFiber.obj G.constantSheafInt) :=
    fun x ↦ projective_sheafFiber_constantSheafInt (G.uliftPointSmallEtale x)
  have hT := shortExact_kummerSequence_pullback_map_extendScalars Λ φ hC
  set T := ((G.kummerSequence (ringChar Λ)).pullback φ).map (extendScalars Λ G) with hTdef
  -- Step A: reduce to the extension class
  let α := constantComplexIsoSingleFunctorExtendScalarsInt G Λ
  let β := (shiftFunctor _ (1 : ℤ)).mapIso (tateTwistObjectOneIso G Λ)
  have hκ : ∀ c : Λ, c • kummerClassOf G Λ t =
      (α.symm.homCongr β.symm) (Abelian.Ext.homLinearEquiv (R := Λ) (c • hT.extClass)) := by
    intro c
    rw [map_smul]
    simp only [Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom, Linear.smul_comp,
      Linear.comp_smul]
    congr 1
    rw [kummerClassOf, kummerδ, ← hT.extClass_hom]
    rfl
  suffices hB : Function.Bijective (fun c : Λ ↦ c • hT.extClass) by
    have h := (α.symm.homCongr β.symm).bijective.comp
      ((Abelian.Ext.homLinearEquiv (R := Λ)).bijective.comp hB)
    convert h using 1
    funext c
    exact hκ c
  -- Step B: compare with the cohomology of the underlying abelian sheaf
  let ε : (freeSheaf Λ G).obj (finalObject G) ≅ T.X₃ :=
    (constantSheafIsoFreeSheafFinalObject Λ G).symm ≪≫
      (extendScalarsConstantZModIso G (n := 0) (by simp)).symm
  have hΨ := bijective_extToSheafH Λ ε T.X₁ 1
  have hΨc : ∀ c : Λ, extToSheafH Λ ε T.X₁ 1 (c • hT.extClass) =
      Sheaf.H.map ((forget₂Sheaf Λ G).map (c • 𝟙 T.X₁)) 1 (extToSheafH Λ ε T.X₁ 1 hT.extClass) := by
    intro c
    rw [Abelian.Ext.smul_eq_comp_mk₀, extToSheafH_comp_mk₀]
  refine (Function.Bijective.of_comp_iff' hΨ _).1 ?_
  change Function.Bijective (fun c : Λ ↦ extToSheafH Λ ε T.X₁ 1 (c • hT.extClass))
  simp_rw [hΨc]
  set y₀ := extToSheafH Λ ε T.X₁ 1 hT.extClass with hy₀
  -- Step C
  let p := j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)
  let ζ := (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf p hN).some
  let σ : T.X₁ ≅ (constantSheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ) :=
    (extendScalars Λ G).mapIso ζ.symm ≪≫ extendScalarsConstantZModIso G ringChar.Nat.cast_ringChar
  let A := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (ModuleCat.of Λ Λ)
  have hA : ∀ a : A, ringChar Λ • a = 0 := fun a ↦ by
    simp
  let τ := (forget₂Sheaf Λ G).mapIso σ ≪≫ forget₂SheafConstantSheafIso Λ G
  let η := sheafHConstantSheafNatTrans G (ringChar Λ) 1 (AffineSpace.kummerClassZMod j hj hN)
  have hη := AffineSpace.bijective_sheafHConstantSheafNatTrans j hj hN A hA
  let δt := G.kummerδ₀ (ringChar Λ) (AffineSpace.isUnit_natCast_of_ne_zero p hN)
    (Additive.ofMul t)
  have hgen : ∀ y : Sheaf.H ((forget₂Sheaf Λ G).obj T.X₁) 1,
      ∃ f : G.rootsOfUnitySheaf (ringChar Λ) ⟶ (forget₂Sheaf Λ G).obj T.X₁,
        y = Sheaf.H.map f 1 δt := by
    intro y
    obtain ⟨φ', hφ'⟩ := hη.2 (Sheaf.H.map τ.hom 1 y)
    refine ⟨ζ.inv ≫ (constantSheaf _ _).map φ' ≫ τ.inv, ?_⟩
    change Sheaf.H.map ((constantSheaf _ _).map φ') 1 (Sheaf.H.map ζ.inv 1 δt) = _ at hφ'
    rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply, hφ', ← Sheaf.H.map_comp_apply,
      τ.hom_inv_id, Sheaf.H.map_id_apply]
  let E : Sheaf.H ((forget₂Sheaf Λ G).obj T.X₁) 1 ≃ Λ :=
    ((Sheaf.functorH _ 1).mapIso τ).addCommGroupIsoToAddEquiv.toEquiv.trans
      ((Equiv.ofBijective _ hη).symm.trans (AddCommGrpCat.zmodHomEquiv A hA))
  have : Finite (Sheaf.H ((forget₂Sheaf Λ G).obj T.X₁) 1) := Finite.of_equiv _ E.symm
  have h5 : ∃ c₁ : Λ, Sheaf.H.map ((extendScalarsAdjunction Λ G).unit.app
      (G.rootsOfUnitySheaf (ringChar Λ))) 1 δt =
        Sheaf.H.map ((forget₂Sheaf Λ G).map (c₁ • 𝟙 T.X₁)) 1 y₀ := by
    let adj := extendScalarsAdjunction Λ G
    set S := (G.kummerSequence (ringChar Λ)).pullback φ with hSdef
    have hK := G.kummerSequence_shortExact (ringChar Λ)
      (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) G)
    have hS : S.ShortExact := hK.pullback φ
    have hTf := hT.map_of_exact (forget₂Sheaf Λ G)
    -- the Kummer class of `t` is the extension class of the pulled back Kummer sequence
    have h1 : δt = (Abelian.Ext.mk₀ (G.constantSheafULiftIntIso).hom).comp hS.extClass
        (zero_add 1) := by
      have hn := hS.extClass_naturality hK ((G.kummerSequence (ringChar Λ)).pullbackHom φ)
      change G.kummerδ₀ _ _ _ = _
      rw [Scheme.kummerδ₀_eq_comp_extClass, ← Abelian.Ext.mk₀_comp_mk₀_assoc]
      congr 1
      exact hn.symm.trans (Abelian.Ext.comp_mk₀_id _)
    -- the unit of extension of scalars maps the Kummer sequence to the underlying sequence of `T`
    let m : S ⟶ T.map (forget₂Sheaf Λ G) :=
      { τ₁ := adj.unit.app S.X₁
        τ₂ := adj.unit.app S.X₂
        τ₃ := adj.unit.app S.X₃
        comm₁₂ := (adj.unit.naturality S.f).symm
        comm₂₃ := (adj.unit.naturality S.g).symm }
    have h2 := hS.extClass_naturality hTf m
    have h3 : Sheaf.H.map (adj.unit.app (G.rootsOfUnitySheaf (ringChar Λ))) 1 δt =
        (Abelian.Ext.mk₀ ((G.constantSheafULiftIntIso).hom ≫ adj.unit.app S.X₃)).comp
          hTf.extClass (zero_add 1) := by
      rw [Sheaf.H.map_apply, h1, Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by omega)]
      erw [h2]
      rw [← Abelian.Ext.mk₀_comp_mk₀_assoc]
    set s₀ := extFreeSheafToH Λ T.X₃ 0 (Abelian.Ext.mk₀ ε.hom)
    have h4 : ∃ c₁ : Λ, Abelian.Ext.mk₀ ((G.constantSheafULiftIntIso).hom ≫ adj.unit.app S.X₃) =
        Sheaf.H.map ((forget₂Sheaf Λ G).map (c₁ • 𝟙 T.X₃)) 0 s₀ := by
      obtain ⟨g', hg'⟩ := (bijective_extFreeSheafToH Λ 0 T.X₃).2
        (Abelian.Ext.mk₀ ((G.constantSheafULiftIntIso).hom ≫ adj.unit.app S.X₃))
      obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 g'
      obtain ⟨c₁, hc⟩ := exists_eq_smul_id_of_iso Λ (constantSheafIsoFreeSheafFinalObject Λ G).symm
        (g ≫ ε.inv)
      have hg : g = ε.hom ≫ (c₁ • 𝟙 T.X₃) := by
        calc g = (g ≫ ε.inv) ≫ ε.hom := by simp
          _ = ε.hom ≫ (c₁ • 𝟙 T.X₃) := by
            rw [hc, Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id]
      refine ⟨c₁, ?_⟩
      rw [← hg', hg, ← Abelian.Ext.mk₀_comp_mk₀, extFreeSheafToH_comp_mk₀]
    obtain ⟨c₁, hc₁⟩ := h4
    have h6 := hTf.extClass_naturality hTf ((forget₂Sheaf Λ G).mapShortComplex.map (c₁ • 𝟙 T))
    refine ⟨c₁, ?_⟩
    rw [h3, hc₁, hy₀, extToSheafH_extClass Λ hT ε, Sheaf.H.map_apply, Sheaf.H.map_apply,
      Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by omega),
      Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by omega)]
    congr 1
    simp only [Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃,
      ShortComplex.smul_τ₁, ShortComplex.smul_τ₃, ShortComplex.id_τ₁, ShortComplex.id_τ₃] at h6
    exact h6.symm
  obtain ⟨c₁, hc₁⟩ := h5
  refine Function.Surjective.bijective_of_nat_card_le (fun y ↦ ?_)
    (le_of_eq (Nat.card_congr E).symm)
  obtain ⟨f, rfl⟩ := hgen y
  have hf : f = (extendScalarsAdjunction Λ G).unit.app _ ≫ (forget₂Sheaf Λ G).map
      (((extendScalarsAdjunction Λ G).homEquiv _ _).symm f) := by
    conv_lhs => rw [← ((extendScalarsAdjunction Λ G).homEquiv _ _).apply_symm_apply f]
    exact Adjunction.homEquiv_unit _ _ _ _
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_iso Λ σ
    (((extendScalarsAdjunction Λ G).homEquiv (G.rootsOfUnitySheaf (ringChar Λ)) T.X₁).symm f)
  rw [hc] at hf
  refine ⟨c * c₁, ?_⟩
  rw [hf, Sheaf.H.map_comp_apply]
  erw [hc₁]
  change Sheaf.H.map ((forget₂Sheaf Λ G).map ((c * c₁) • 𝟙 T.X₁)) 1 y₀ =
    Sheaf.H.map ((forget₂Sheaf Λ G).map (c • 𝟙 T.X₁)) 1
      (Sheaf.H.map ((forget₂Sheaf Λ G).map (c₁ • 𝟙 T.X₁)) 1 y₀)
  rw [← Sheaf.H.map_comp_apply, ← Functor.map_comp]
  congr 3
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_comm]

end Kummer

section Node

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (ringChar Λ)]

omit [Finite Λ] in
/-- Over an algebraically closed field, the Tate twist `Λ(1) = μₙ ⊗ Λ` is isomorphic to `Λ`: a
primitive `n`-th root of unity identifies `μₙ` with `ℤ/n`. -/
lemma nonempty_tateTwistObject_one_iso_constantComplex {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ (Spec (.of k))] :
    Nonempty (tateTwistObject Λ X 1 ≅ constantComplex Λ X) := by
  have hN : ((ringChar Λ : ℕ) : k) ≠ 0 := by
    have h := (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) (Spec (.of k))).map
      (Scheme.ΓSpecIso (.of k)).hom.hom
    rw [map_natCast] at h
    exact h.ne_zero
  let ζ := (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf f hN).some
  exact ⟨tateTwistObjectOneIso X Λ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    ((extendScalars Λ X).mapIso ζ.symm ≪≫
      extendScalarsConstantZModIso X ringChar.Nat.cast_ringChar) ≪≫
    (constantComplexIsoSingleFunctorConstantSheaf Λ X).symm⟩

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1))
    (Spec (.of k))).base)ᶜ) [HasInvertibleExponent Λ G]
  [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k))]

include hj in
/-- Blueprint `thm-pur-kummer-affine-line`: Kummer computations on the line and the punctured line.

Let `k` be an algebraically closed field and `Λ` a finite coefficient ring whose exponent is
invertible in `k`, with Tate twist `Λ(1) = μₙ ⊗ Λ` (`n` the characteristic of `Λ`). Let
`G = 𝔾_{m,k}` be the complement of the zero section of `𝔸¹_k`, with coordinate `t`. Then

1. `Hᵠ(𝔸¹_k, Λ(1)) = 0` for `q ≠ 0` and `H⁰(𝔸¹_k, Λ(1)) ≅ Λ`;
2. `H⁰(𝔾_{m,k}, Λ(1)) ≅ Λ` and `Hᵠ(𝔾_{m,k}, Λ(1)) = 0` for `q ∉ {0, 1}`;
3. `H¹(𝔾_{m,k}, Λ(1)) = Hom(Λ, Λ(1)[1])` is free of rank one over `Λ` on the Kummer class
   `κ(t)` of the coordinate.

In particular all these cohomology groups are finite. The blueprint takes `Λ = A` free over
`ℤ/ℓ^N`; here `Λ` is any finite commutative ring with invertible exponent, so the statements
hold after any change of finite coefficients. -/
theorem kummer_affineLine_multiplicativeGroup :
    (∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
        𝔸(ULift.{u} (Fin 1); Spec (.of k)) q).obj
          (tateTwistObject Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 1))) ∧
      Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 0).obj
        (tateTwistObject Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 1) ≅ ModuleCat.of Λ Λ) ∧
      Nonempty ((cohomology (ModuleCat.{u + 1} Λ) G 0).obj (tateTwistObject Λ G 1) ≅
        ModuleCat.of Λ Λ) ∧
      (∀ q : ℤ, q ≠ 0 → q ≠ 1 →
        IsZero ((cohomology (ModuleCat.{u + 1} Λ) G q).obj (tateTwistObject Λ G 1))) ∧
      Function.Bijective (fun c : Λ ↦ c • kummerClassOf G Λ (AffineSpace.unitLineCoord j hj)) := by
  have := (connectedSpace_of_range_eq_compl_zeroSection j hj).toNonempty
  have : HasInvertibleExponent Λ (Spec (.of k)) := HasInvertibleExponent.of_hom_of_nonempty
    (j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) (Λ := Λ)
  obtain ⟨eA⟩ := nonempty_tateTwistObject_one_iso_constantComplex Λ
    (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨eG⟩ := nonempty_tateTwistObject_one_iso_constantComplex Λ
    (j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  have := connectedSpace_of_range_eq_compl_zeroSection j hj
  exact ⟨fun q hq ↦ (isZero_cohomology_affineLine Λ q hq).of_iso ((cohomology _ _ q).mapIso eA),
    ⟨(cohomology _ _ 0).mapIso eA ≪≫ cohomologyZeroConstantComplexIso Λ _⟩,
    ⟨(cohomology _ _ 0).mapIso eG ≪≫ cohomologyZeroConstantComplexIso Λ _⟩,
    fun q hq0 hq1 ↦ (isZero_cohomology_multiplicativeGroup Λ j hj q hq0 hq1).of_iso
      ((cohomology _ _ q).mapIso eG), bijective_smul_kummerClassOf Λ j hj⟩

omit [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k))] in
include hj in
/-- Untwisted form of `H¹(𝔾_{m,k}, Λ) ≅ Λ`: `Hom(Λ, Λ[1])` is free of rank one over `Λ`. -/
theorem exists_bijective_smul_constantComplex_shift_one :
    ∃ y₀ : constantComplex Λ G ⟶ (constantComplex Λ G)⟦(1 : ℤ)⟧,
      Function.Bijective (fun c : Λ ↦ c • y₀) := by
  have := (connectedSpace_of_range_eq_compl_zeroSection j hj).toNonempty
  have : HasInvertibleExponent Λ (Spec (.of k)) := HasInvertibleExponent.of_hom_of_nonempty
    (j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) (Λ := Λ)
  obtain ⟨eG⟩ := nonempty_tateTwistObject_one_iso_constantComplex Λ
    (j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  refine ⟨kummerClassOf G Λ (AffineSpace.unitLineCoord j hj) ≫ eG.hom⟦(1 : ℤ)⟧', ?_⟩
  have h := ((Iso.refl _).homCongr ((shiftFunctor _ (1 : ℤ)).mapIso eG)).bijective.comp
    (bijective_smul_kummerClassOf Λ j hj)
  convert h using 1
  funext c
  simp [Linear.smul_comp]

end Node

end AlgebraicGeometry.Etale
