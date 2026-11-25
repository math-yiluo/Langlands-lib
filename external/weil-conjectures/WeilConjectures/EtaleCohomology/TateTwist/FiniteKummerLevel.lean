/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.RingTheory.DiscreteValuationRing.FiniteKummerLevel

/-!
# The finite Kummer level of the Tate twist: sheaves

Let `Λ` be a commutative ring of characteristic `n ≠ 0`, for instance `A = 𝒪_E / ϖ^m` with
`n = ℓ^N` (`WeilConjectures.RingTheory.DiscreteValuationRing.FiniteKummerLevel`). The sheaf
`μₙ` of `n`-th roots of unity is killed by `n`, so it is a sheaf of `ℤ/n`-modules
(`AlgebraicGeometry.Scheme.rootsOfUnityModuleSheaf`), and the Tate sheaf
`Λ(1) = μₙ ⊗_ℤ Λ` (`AlgebraicGeometry.Etale.tateSheaf`) is canonically the tensor product
`μₙ ⊗_{ℤ/n} Λ` over `ℤ/n` (`AlgebraicGeometry.Etale.extendScalarsIsoExtendScalarsAlong`): both are
left adjoint objects corepresenting the additive maps `μₙ ⟶ G` into sheaves of `Λ`-modules, an
additive map of `ℤ/n`-modules being `ℤ/n`-linear.

## Main definitions

- `AlgebraicGeometry.Scheme.rootsOfUnityModuleSheaf`: `μₙ` as a sheaf of `ℤ/n`-modules.
- `AlgebraicGeometry.Etale.extendScalarsAlong`: extension of scalars `F ↦ Λ ⊗_R F` of étale
  sheaves along a ring map `R ⟶ Λ`.
- `AlgebraicGeometry.Etale.extendScalarsIsoExtendScalarsAlong`: `μₙ ⊗_ℤ Λ ≅ μₙ ⊗_{ℤ/n} Λ`.
- `AlgebraicGeometry.Etale.tateTwistSheafOneIsoExtendScalarsAlong`: `Λ(1) ≅ μₙ ⊗_{ℤ/n} Λ`.

## Main statements

- `AlgebraicGeometry.Etale.tateTwistSheafOneIsoQuotientSpanPow`: blueprint
  `lem-pur-finite-kummer-level`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- The sections of `μₙ` are killed by `n`. -/
lemma nsmul_rootsOfUnitySheaf_eq_zero (U : X.Etaleᵒᵖ)
    (x : ((X.rootsOfUnitySheaf n).obj.obj U : Type (u + 1))) : n • x = 0 := by
  have hmono : Mono ((kernel.ι (n • 𝟙 X.gmSheaf)).hom.app U) := by
    have : Mono (kernel.ι (n • 𝟙 X.gmSheaf)).hom :=
      (sheafToPresheaf _ _).map_mono (kernel.ι (n • 𝟙 X.gmSheaf))
    infer_instance
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 hmono
  apply hinj
  have h := congr_arg (fun f ↦ (f.hom.app U).hom x) (kernel.condition (n • 𝟙 X.gmSheaf))
  simp only [Preadditive.comp_nsmul, Category.comp_id] at h
  rw [map_nsmul, map_zero]
  exact h

end Scheme

end AlgebraicGeometry

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- The `ℤ/n`-module structure on the sections of `μₙ`, which are killed by `n`. -/
noncomputable instance rootsOfUnityZModModule (U : X.Etaleᵒᵖ) :
    Module (ZMod n) ((X.rootsOfUnitySheaf n).obj.obj U) :=
  AddCommGroup.zmodModule (nsmul_rootsOfUnitySheaf_eq_zero X n U)

/-- The presheaf of `ℤ/n`-modules underlying `μₙ`. -/
noncomputable def rootsOfUnityModulePresheaf : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n) where
  obj U := ModuleCat.of (ZMod n) ((X.rootsOfUnitySheaf n).obj.obj U)
  map f := ModuleCat.ofHom
    { toFun := (X.rootsOfUnitySheaf n).obj.map f
      map_add' := map_add ((X.rootsOfUnitySheaf n).obj.map f).hom
      map_smul' := fun c x ↦ ZMod.map_smul ((X.rootsOfUnitySheaf n).obj.map f).hom c x }
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom ((X.rootsOfUnitySheaf n).obj.map_id U) x
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom ((X.rootsOfUnitySheaf n).obj.map_comp f g) x

/-- `μₙ` as an étale sheaf of `ℤ/n`-modules: the sheaf of abelian groups `μₙ`, which is killed
by `n`, with its unique `ℤ/n`-module structure. -/
noncomputable def rootsOfUnityModuleSheaf :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)) :=
  ⟨rootsOfUnityModulePresheaf X n, by
    have : ReflectsLimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}) :=
      reflectsLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    exact Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})
      (X.rootsOfUnitySheaf n).property⟩

end Scheme

namespace Etale

variable {R : Type} [CommRing R] (Λ : Type (u + 1)) [CommRing Λ] (φ : R →+* Λ)
  (X : Scheme.{u})

/-- Extension of scalars `F ↦ Λ ⊗_R F` from étale sheaves of `R`-modules to étale sheaves of
`Λ`-modules along a ring map `φ : R →+* Λ`: extension of scalars on sections followed by
sheafification. -/
noncomputable def extendScalarsAlong :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{0, u + 1, u + 1} φ)

/-- Extension of scalars along `φ` is left adjoint to restriction of scalars. -/
noncomputable def extendScalarsAlongAdjunction :
    extendScalarsAlong Λ φ X ⊣
      sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} φ)

section Comparison

variable {n : ℕ} [CharP Λ n]

/-- For a sheaf `G` of `Λ`-modules, with `Λ` of characteristic `n`, the `ℤ/n`-linear maps from
`μₙ` to `G` are the additive maps from `μₙ` to `G`. -/
noncomputable def rootsOfUnityModuleSheafHomEquiv (G : Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) :
    (X.rootsOfUnityModuleSheaf n ⟶ (sheafCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom (dvd_refl n) Λ))).obj G) ≃
      (X.rootsOfUnitySheaf n ⟶ (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) where
  toFun f := ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (f.hom.app U).hom.toAddMonoidHom
      naturality U V g := by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  invFun f := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u + 1}
          (ZMod.castHom (dvd_refl n) Λ)).obj (G.obj.obj U))
        { toFun := (f.hom.app U).hom
          map_add' := map_add _
          map_smul' c x := by
            obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
            rw [Int.cast_smul_eq_zsmul, map_zsmul, RingHom.id_apply,
              ModuleCat.restrictScalars.smul_def, map_intCast, Int.cast_smul_eq_zsmul] }
      naturality U V g := by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by
    ext U x
    rfl
  right_inv f := by
    ext U x
    rfl

lemma rootsOfUnityModuleSheafHomEquiv_naturality {G G' : Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)} (f : X.rootsOfUnityModuleSheaf n ⟶ (sheafCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom (dvd_refl n) Λ))).obj G) (g : G ⟶ G') :
    rootsOfUnityModuleSheafHomEquiv Λ X G' (f ≫ (sheafCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom (dvd_refl n) Λ))).map g) =
      rootsOfUnityModuleSheafHomEquiv Λ X G f ≫ (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map g := by
  ext U x
  simp [rootsOfUnityModuleSheafHomEquiv]
  rfl

variable (n) in
/-- Extension of scalars of `μₙ` to `Λ` over `ℤ` and over `ℤ/n` agree, `Λ ⊗_ℤ μₙ ≅ Λ ⊗_{ℤ/n} μₙ`,
for `Λ` of characteristic `n`: both corepresent the additive maps from `μₙ` to sheaves of
`Λ`-modules. -/
noncomputable def extendScalarsIsoExtendScalarsAlong :
    (extendScalars Λ X).obj (X.rootsOfUnitySheaf n) ≅
      (extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) X).obj (X.rootsOfUnityModuleSheaf n) :=
  Coyoneda.ext _ _
    (fun f ↦ ((extendScalarsAlongAdjunction Λ _ X).homEquiv _ _).symm
      ((rootsOfUnityModuleSheafHomEquiv Λ X _).symm ((extendScalarsAdjunction Λ X).homEquiv _ _ f)))
    (fun f ↦ ((extendScalarsAdjunction Λ X).homEquiv _ _).symm
      (rootsOfUnityModuleSheafHomEquiv Λ X _ ((extendScalarsAlongAdjunction Λ _ X).homEquiv _ _ f)))
    (fun f ↦ by simp) (fun f ↦ by simp)
    (fun f g ↦ by
      rw [Adjunction.homEquiv_naturality_right, rootsOfUnityModuleSheafHomEquiv_naturality,
        Adjunction.homEquiv_naturality_right_symm])

/-- The identification `Λ ⊗_ℤ μₙ ≅ Λ ⊗_{ℤ/n} μₙ` is canonical: it is compatible with the canonical
additive maps `μₙ ⟶ Λ ⊗_ℤ μₙ` and `μₙ ⟶ Λ ⊗_{ℤ/n} μₙ`, the units of the extension of scalars
adjunctions. -/
lemma unit_comp_extendScalarsIsoExtendScalarsAlong_hom :
    (extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf n) ≫
        (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          (extendScalarsIsoExtendScalarsAlong Λ X n).hom =
      rootsOfUnityModuleSheafHomEquiv Λ X _
        ((extendScalarsAlongAdjunction Λ (ZMod.castHom (dvd_refl n) Λ) X).unit.app
          (X.rootsOfUnityModuleSheaf n)) := by
  refine ((extendScalarsAdjunction Λ X).homEquiv_unit _ _ _).symm.trans ?_
  change (extendScalarsAdjunction Λ X).homEquiv _ _
    (((extendScalarsAdjunction Λ X).homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_id]

end Comparison

section FiniteLevel

variable (n : ℕ) [NeZero (ringChar Λ)] [CharP Λ n] {X} [HasInvertibleExponent Λ X]

/-- The finite-level Tate twist `Λ_X(1)` (`AlgebraicGeometry.Etale.tateTwistSheaf`) of a ring `Λ`
of characteristic `n` is `μₙ ⊗_{ℤ/n} Λ`. -/
noncomputable def tateTwistSheafOneIsoExtendScalarsAlong :
    tateTwistSheaf Λ X 1 ≅
      (extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) X).obj (X.rootsOfUnityModuleSheaf n) := by
  obtain rfl : n = ringChar Λ := (ringChar.eq Λ n).symm
  exact tateTwistSheafOneIso X Λ ≪≫ extendScalarsIsoExtendScalarsAlong Λ X (ringChar Λ)

/-- The finite-level Tate twist object `Λ_X(1) ∈ D(X_ét, Λ)` is `μₙ ⊗_{ℤ/n} Λ` placed in degree
zero. -/
noncomputable def tateTwistObjectOneIsoExtendScalarsAlong :
    tateTwistObject Λ X 1 ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) X).obj
        (X.rootsOfUnityModuleSheaf n)) :=
  tateTwistObjectIsoSingleFunctor Λ X 1 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tateTwistSheafOneIsoExtendScalarsAlong Λ n)

/-- The twist `K(1) = K ⊗^L Λ_X(1)` of a complex is `K ⊗^L (μₙ ⊗_{ℤ/n} Λ)`: the identification of
`Λ_X(1)` with `μₙ ⊗_{ℤ/n} Λ` is compatible with the derived tensor product. -/
noncomputable def tateTwistObjIsoExtendScalarsAlong
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj (tateTwistObject Λ X 1) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) X).obj
            (X.rootsOfUnityModuleSheaf n))) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
    (tateTwistObjectOneIsoExtendScalarsAlong Λ n)

end FiniteLevel

section ValuationRing

variable {R : Type (u + 1)} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  (hϖ : Irreducible ϖ) {ℓ : ℕ} (hℓ : ℓ.Prime) {e : ℕ} (he : 0 < e)
  (hℓe : Associated (ℓ : R) (ϖ ^ e)) (N : ℕ)

/-- Blueprint `lem-pur-finite-kummer-level`: Finite Kummer level of the Tate twist

Let `R = 𝒪_E` be a discrete valuation ring with uniformizer `ϖ` and ramification index `e ≥ 1`
over the prime `ℓ`, i.e. `ℓ = (unit) · ϖ^e`, and let `n = e N`, so that `N = n / e = n v_ℓ(ϖ)`.
Then `A = A_{E,n} = 𝒪_E / ϖ^n` has characteristic `ℓ^N` (`ϖ^n 𝒪_E = ℓ^N 𝒪_E`, and `N` is the
smallest exponent with `ℓ^N A = 0`; this is
`IsDiscreteValuationRing.ringChar_quotient_span_pow`), and on every scheme `T` on which `ℓ` is
invertible the finite-level twist `A(1)_T` (`AlgebraicGeometry.Etale.tateTwistSheaf`, the Tate
sheaf `μ_{ℓ^N} ⊗_ℤ A` of `definition-tate-twists`) is canonically

`A(1)_T ≅ μ_{ℓ^N,T} ⊗_{ℤ/ℓ^N} A`

(this definition, an instance of `AlgebraicGeometry.Etale.tateTwistSheafOneIsoExtendScalarsAlong`),
the tensor product being over `ℤ/ℓ^N`, with `μ_{ℓ^N}` viewed as a sheaf of `ℤ/ℓ^N`-modules.
Its compatibility with the derived tensor product is
`AlgebraicGeometry.Etale.tateTwistObjIsoExtendScalarsAlong`, and its compatibility with base
change is `AlgebraicGeometry.Etale.upperStar_map_tateSheafIso_hom`
(`WeilConjectures.EtaleCohomology.TateTwist.FiniteKummerLevelBaseChange`).

The blueprint clause that `A` is free of rank `ef` over `ℤ/ℓ^N`, `A ≅ (ℤ/ℓ^N)^{ef}`, is
`IsDiscreteValuationRing.free_quotient_span_pow`
(`WeilConjectures.RingTheory.DiscreteValuationRing.FiniteKummerLevelFree`).

The blueprint states the isomorphism on the small pro-étale site; as throughout the purity
chapter (`def-pur-conventions`, `AlgebraicGeometry.Etale.tateTwist`) the sheaves here are on the
small étale site, the pro-étale form being transported by the pro-étale comparison
(`WeilConjectures.SixFunctors.ProEtale.Comparison`). -/
noncomputable def tateTwistSheafOneIsoQuotientSpanPow (T : Scheme.{u})
    [HasInvertibleExponent (R ⧸ Ideal.span {ϖ ^ (e * N)}) T] :
    haveI := IsDiscreteValuationRing.charP_quotient_span_pow hϖ hℓ he hℓe N
    haveI : NeZero (ringChar (R ⧸ Ideal.span {ϖ ^ (e * N)})) := ⟨by
      rw [ringChar.eq _ (ℓ ^ N)]
      exact pow_ne_zero _ hℓ.ne_zero⟩
    tateTwistSheaf (R ⧸ Ideal.span {ϖ ^ (e * N)}) T 1 ≅
      (extendScalarsAlong (R ⧸ Ideal.span {ϖ ^ (e * N)})
        (ZMod.castHom (dvd_refl (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)})) T).obj
          (T.rootsOfUnityModuleSheaf (ℓ ^ N)) :=
  haveI := IsDiscreteValuationRing.charP_quotient_span_pow hϖ hℓ he hℓe N
  haveI : NeZero (ringChar (R ⧸ Ideal.span {ϖ ^ (e * N)})) := ⟨by
    rw [ringChar.eq _ (ℓ ^ N)]
    exact pow_ne_zero _ hℓ.ne_zero⟩
  tateTwistSheafOneIsoExtendScalarsAlong _ _

end ValuationRing

end Etale

end AlgebraicGeometry
