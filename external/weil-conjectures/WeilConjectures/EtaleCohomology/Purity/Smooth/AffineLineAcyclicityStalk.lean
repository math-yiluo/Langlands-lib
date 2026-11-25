/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
import WeilConjectures.AlgebraicGeometry.ModuleAbelianStalkExchange
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues

/-!
# The exchange morphism of the affine line at a geometric point

Let `p : 𝔸¹_S ⟶ S` be the affine line and

```
X' --g'--> 𝔸¹_S
|            |
f'           p
v            v
T ----g----> S
```

a cartesian square. At a geometric point `t̄` of `T` with image `s̄` in `S`, the stalk of the
degree-`q` exchange morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is the pullback map
`Hᵠ(𝔸¹_A, F|) ⟶ Hᵠ(𝔸¹_B, F|)`, where `A ⟶ B` is the induced local homomorphism of the strict
henselisations of `S` at `s̄` and of `T` at `t̄`
(`AlgebraicGeometry.Etale.affineLine_originalStalk_totalCohomologyExchange`). This is the
argument of the proof of the proper base change theorem for `ℙ¹`
(`WeilConjectures.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange`), which
only uses that the projection is quasi-compact and quasi-separated; for `𝔸¹` it stops at the
strictly henselian rings, since the cohomology of `𝔸¹_A` is not that of its closed fibre for
arbitrary coefficients.

Consequently the exchange morphism of `𝔸¹` at a sheaf `F` is an isomorphism as soon as these
pullback maps between strictly henselian affine lines are bijective
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_affineLine_of_strictLocal`).

## References

- Stacks Project, Tag 03Q9 and the proof of Theorem 59.91.11,
  <https://stacks.math.columbia.edu/tag/095T>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- The original stalk exchange of the affine line with abelian coefficients: the stalk at a
geometric point of the degree-`q` exchange morphism of a cartesian square over `𝔸¹_S ⟶ S` is
the pullback map between the cohomologies of the affine lines over the strict henselisations.
The proof is that of `AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange`.
-/
theorem Etale.affineLine_abelian_originalStalk_totalExchange
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ 𝔸(ULift.{u} (Fin 1); S)}
    (sq : IsPullback g' f' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (G : Sheaf 𝔸(ULift.{u} (Fin 1); S).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (AffineSpace.map (ULift.{u} (Fin 1))
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))^*[
      AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((𝔸(ULift.{u} (Fin 1); S) ↘ S)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (a₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+ Sheaf.H G₀ q)
      (a₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        Sheaf.H ((AffineSpace.map (ULift.{u} (Fin 1)) g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        Etale.cohomologyMap (AffineSpace.map (ULift.{u} (Fin 1)) g₀) G₀ q (a₁ x) := by
  let jA := eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  let G₀ := (AffineSpace.map (ULift.{u} (Fin 1)) jA)^*[AddCommGrpCat.{u + 1}].obj G
  obtain ⟨c₁, c₂, hc⟩ :=
    Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange
      sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ
      (AffineSpace.map (ULift.{u} (Fin 1)) jA)
      (𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) jA)
      (AffineSpace.map (ULift.{u} (Fin 1)) g₀)
      (𝔸(ULift.{u} (Fin 1); Spec (.of B)) ↘ Spec (.of B))
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g₀) G q
  obtain ⟨b₁, b₂, hb⟩ :=
    Etale.exists_addEquiv_strictLocal_abelian_total_exchange φ
      (𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))
      (𝔸(ULift.{u} (Fin 1); Spec (.of B)) ↘ Spec (.of B))
      (AffineSpace.map (ULift.{u} (Fin 1)) g₀)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g₀) G₀ q
  refine ⟨c₁.trans b₁, c₂.trans b₂, fun x ↦ ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [hc]
  exact hb (c₁ x)

/-- The original stalk exchange of the affine line: the stalk at a geometric point `τ` of `T`
of the degree-`q` exchange morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` of a cartesian square over
`p : 𝔸¹_S ⟶ S` is, up to isomorphisms of its source and target, the pullback map
`Hᵠ(𝔸¹_A, F|) ⟶ Hᵠ(𝔸¹_B, F|)` along the local homomorphism `A ⟶ B` of the strict
henselisations. The proof is that of
`AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange`. -/
theorem Etale.affineLine_originalStalk_totalCohomologyExchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ 𝔸(ULift.{u} (Fin 1); S)}
    (sq : IsPullback g' f' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    (F : Sheaf 𝔸(ULift.{u} (Fin 1); S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    let F₀ := (AffineSpace.map (ULift.{u} (Fin 1))
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))^*[
      ModuleCat.{u + 1} Λ].obj F
    let G₀ := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F₀
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    ∃ (c₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (𝔸(ULift.{u} (Fin 1); S) ↘ S) q).obj F) ≃+
        Sheaf.H G₀ q)
      (c₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((AffineSpace.map (ULift.{u} (Fin 1)) g₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q),
      ∀ x, c₂ ((((pointSmallEtale τ).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (AffineSpace.map (ULift.{u} (Fin 1)) g₀) G₀ q (c₁ x) := by
  let p := AffineSpace.map (ULift.{u} (Fin 1))
    (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ))
  let G := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  let h := AffineSpace.map (ULift.{u} (Fin 1)) g₀
  obtain ⟨b₁, b₂, hb⟩ := Etale.exists_addEquiv_module_abelian_stalk_exchange
    Λ (𝔸(ULift.{u} (Fin 1); S) ↘ S) f' g' g sq τ F q
  obtain ⟨a₁, a₂, ha⟩ := Etale.affineLine_abelian_originalStalk_totalExchange
    sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ G q
  obtain ⟨d⟩ := Etale.pullback_forget_modules_iso Λ p F
  let c₁ := ((Sheaf.functorH _ q).mapIso d.symm).addCommGroupIsoToAddEquiv
  let c₂ := ((Sheaf.functorH _ q).mapIso
    (((h)^*[AddCommGrpCat.{u + 1}]).mapIso d.symm)).addCommGroupIsoToAddEquiv
  refine ⟨(b₁.trans a₁).trans c₁, (b₂.trans a₂).trans c₂, fun x ↦ ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [hb x, ha (b₁ x)]
  exact (Etale.cohomologyMap_map h q d.inv (a₁ (b₁ x))).symm


/-- **The exchange morphism of `𝔸¹` and the strictly henselian affine lines.** For a cartesian
square

```
X' --g'--> 𝔸¹_S
|            |
f'           p
v            v
T ----g----> S
```

a sheaf `F` of `Λ`-modules on `𝔸¹_S` and `q ≥ 0`, suppose that for every local homomorphism
`φ : A ⟶ B` of strictly henselian local rings and every `j : Spec A ⟶ S` the pullback map
`Hᵠ(𝔸¹_A, F|) ⟶ Hᵠ(𝔸¹_B, F|)` along `𝔸¹_B ⟶ 𝔸¹_A` is bijective. Then the degree-`q` exchange
morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is an isomorphism: at every geometric point of `T` it is
such a pullback map (`AlgebraicGeometry.Etale.affineLine_originalStalk_totalCohomologyExchange`),
and geometric stalks are conservative. -/
theorem Etale.isIso_baseChangeHomologyMap_affineLine_of_strictLocal (Λ : Type (u + 1))
    [CommRing Λ] {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T}
    {g' : X' ⟶ 𝔸(ULift.{u} (Fin 1); S)} (sq : IsPullback g' f' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g)
    (F : Sheaf 𝔸(ULift.{u} (Fin 1); S).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (hF : ∀ (A B : Type u) [CommRing A] [HenselianLocalRing A]
      [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
      [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B) [IsLocalHom φ]
      (j : Spec (.of A) ⟶ S),
      Function.Bijective (Etale.cohomologyMap
        (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((AffineSpace.map (ULift.{u} (Fin 1)) j)^*[ModuleCat.{u + 1} Λ].obj F)) q)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun t ↦ ?_
  rw [uliftPointSmallEtale, NatIso.isIso_map_iff ((pointSmallEtale _).uliftSheafFiberIso _)]
  let κs := S.residueField (g.base t)
  let κt := T.residueField t
  let : Algebra κs (AlgebraicClosure κt) :=
    ((algebraMap κt (AlgebraicClosure κt)).comp (g.residueFieldMap t).hom).toAlgebra
  let ψ : AlgebraicClosure κs →ₐ[κs] AlgebraicClosure κt := IsAlgClosed.lift
  let ι : Spec (.of (AlgebraicClosure κt)) ⟶ Spec (.of (AlgebraicClosure κs)) :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hι : ι ≫ S.algClosurePoint (g.base t) = T.algClosurePoint t ≫ g := by
    rw [Scheme.algClosurePoint_eq, Scheme.algClosurePoint_eq, Category.assoc,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    ext x
    exact ψ.commutes x
  obtain ⟨A, B, cA, cB, hA, hB, sA, sB, φ, hφ, eA, eB, ρA, ρB, -, -, hbase, hρA, hρB, hρ⟩ :=
    Etale.projectiveLine_compatibleStrictHenselizationResidues
      (S.algClosurePoint (g.base t)) (T.algClosurePoint t) ι hι
      ⟨g.base t, CommRingCat.ofHom (algebraMap κs (AlgebraicClosure κs)),
        Algebra.IsIntegral.isIntegral (R := κs), rfl⟩
      ⟨t, CommRingCat.ofHom (algebraMap κt (AlgebraicClosure κt)),
        Algebra.IsIntegral.isIntegral (R := κt), rfl⟩ (𝟙 _)
  let := cA
  let := cB
  have : HenselianLocalRing A := hA
  have : HenselianLocalRing B := hB
  have : IsSepClosed (IsLocalRing.ResidueField A) := sA
  have : IsSepClosed (IsLocalRing.ResidueField B) := sB
  have := hφ
  obtain ⟨c₁, c₂, hc⟩ := Etale.affineLine_originalStalk_totalCohomologyExchange Λ sq
    (S.algClosurePoint (g.base t)) (T.algClosurePoint t) ι hι (𝟙 _) eA eB φ ρA ρB hbase hρA
    hρB hρ F q
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hfun : ⇑(((pointSmallEtale (T.algClosurePoint t)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ sq q F)).hom =
      c₂.symm ∘ _ ∘ c₁ :=
    funext fun x ↦ (c₂.symm_apply_apply _).symm.trans (congrArg c₂.symm (hc x))
  exact hfun ▸ c₂.symm.bijective.comp
    ((hF A B φ (eA.hom ≫ strictLocalizationToBase _)).comp c₁.bijective)

end AlgebraicGeometry
