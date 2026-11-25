/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.PuncturedLine
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineKunneth

/-!
# The affine line and the punctured line over a base

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, `Y`
a separated `k`-scheme of finite type, `p : 𝔸¹_Y ⟶ Y` the projection and `π : G ⟶ Y` the
complement of the zero section (`G = 𝔾_{m,Y}`). By the Künneth formula
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_constantFunctor_of_isPullback`),
the direct images of complexes pulled back from `Y` are computed by the cohomology of `𝔸¹_k`
and `𝔾_{m,k}`:

* if `H^q(𝔸¹_k, Λ)` is `Λ` for `q = 0` and vanishes otherwise, then `Rp_* Lp^* Q ≅ Q`;
* if `H^q(𝔾_{m,k}, Λ)` is `Λ` for `q = 0, 1` and vanishes otherwise, then
  `Rπ_* Lπ^* Q ≅ Q ⊕ Q[-1]`,

for every `Q ∈ Dctf(Y, Λ)`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_affineLine_of_cohomology`,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology`).
The cohomology of `𝔸¹_k` and `𝔾_{m,k}` itself is computed in
`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine`.

We also record that the unit `M ⟶ Rπ_* Lπ^* M` of a morphism `π` with a section is a split
monomorphism (`AlgebraicGeometry.Etale.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app`),
which is how the units of `p` and `π` are seen to be isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Section

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ π = 𝟙 Y)

include hσ in
/-- For a morphism `π : X ⟶ Y` with a section `σ`, the unit `M ⟶ Rπ_* Lπ^* M` is a split
monomorphism: composed with `Rπ_*` of the unit of `σ` it is the unit of the composite adjunction
`L(σ ≫ π)^* ⊣ R(σ ≫ π)_*`, whose left adjoint is isomorphic to the identity. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app M) := by
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) σ)
  let e : L((π)^*[ModuleCat.{u + 1} Λ]) ⋙ L((σ)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
    (leftDerivedUpperStarComp _ σ π (𝟙 Y) hσ.symm).symm ≪≫ leftDerivedUpperStarId _ Y
  have : (L((π)^*[ModuleCat.{u + 1} Λ]) ⋙ L((σ)^*[ModuleCat.{u + 1} Λ])).Full :=
    Functor.Full.of_iso e.symm
  have : (L((π)^*[ModuleCat.{u + 1} Λ]) ⋙ L((σ)^*[ModuleCat.{u + 1} Λ])).Faithful :=
    Functor.Faithful.of_iso e.symm
  have h := Adjunction.comp_unit_app (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) σ) M
  refine ⟨⟨(R((π)_*[ModuleCat.{u + 1} Λ])).map
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) σ).unit.app _) ≫
      inv (adj.unit.app M), ?_⟩⟩
  rw [← Category.assoc, ← h, IsIso.hom_inv_id]

end Section

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

section Biprod

variable (Y : Scheme.{u})

/-- `(Λ ⊕ Λ[-1])_Y ⊗ᴸ Q ≅ Q ⊕ Q[-1]`. -/
noncomputable def constantFunctorBiprodTensorIso
    (Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((constantFunctor Λ Y).obj
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj (ModuleCat.of Λ Λ) ⊞
        (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 1).obj
          (ModuleCat.of Λ Λ)))).obj Q ≅ Q ⊞ Q⟦(-1 : ℤ)⟧ :=
  let Φ := constantFunctor Λ Y ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj Q
  let e₀ : Φ.obj ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ Λ)) ≅ Q :=
    ((derivedTensor _ Y).mapIso (constantFunctorObjSingleIso Λ Y)).app Q ≪≫
      derivedTensorLeftUnitor _ Y Q
  Φ.mapBiprod _ _ ≪≫ biprod.mapIso e₀
    (Φ.mapIso (((_root_.DerivedCategory.singleFunctors (ModuleCat.{u + 1} Λ)).shiftIso (-1) 1 0
      (by norm_num)).app _).symm ≪≫ (Φ.commShiftIso (-1 : ℤ)).app _ ≪≫
        (shiftFunctor _ (-1 : ℤ)).mapIso e₀)

end Biprod

section Homology

variable {Y : Scheme.{u}}
  (Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  (hQ : ∀ m : ℤ, m ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj Q))

/-- `H^m(Q[-1]) ≅ H^{m-1}(Q)`. -/
noncomputable def homologyShiftNegOneIso (m : ℤ) :
    (_root_.DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) m).obj (Q⟦(-1 : ℤ)⟧) ≅
      (_root_.DerivedCategory.homologyFunctor _ (m - 1)).obj Q :=
  ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso (-1) m (m - 1) (by omega)).app Q

include hQ

/-- For `Q` concentrated in degree zero, `H⁰(Q ⊕ Q[-1]) ≅ H⁰(Q)`. -/
noncomputable def homologyZeroBiprodShiftIso :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj (Q ⊞ Q⟦(-1 : ℤ)⟧) ≅
      (_root_.DerivedCategory.homologyFunctor _ 0).obj Q :=
  (_root_.DerivedCategory.homologyFunctor _ 0).mapBiprod _ _ ≪≫
    (isoBiprodZero ((hQ (0 - 1) (by omega)).of_iso (homologyShiftNegOneIso Λ Q 0))).symm


/-- For `Q` concentrated in degree zero, `H¹(Q ⊕ Q[-1]) ≅ H⁰(Q)`. -/
noncomputable def homologyOneBiprodShiftIso :
    (_root_.DerivedCategory.homologyFunctor _ 1).obj (Q ⊞ Q⟦(-1 : ℤ)⟧) ≅
      (_root_.DerivedCategory.homologyFunctor _ 0).obj Q :=
  (_root_.DerivedCategory.homologyFunctor _ 1).mapBiprod _ _ ≪≫
    (isoZeroBiprod (hQ 1 (by omega))).symm ≪≫ homologyShiftNegOneIso Λ Q 1

/-- For `Q` concentrated in degree zero, `H^m(Q ⊕ Q[-1]) = 0` for `m ∉ {0, 1}`. -/
lemma isZero_homology_biprodShift (m : ℤ) (h₀ : m ≠ 0) (h₁ : m ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj (Q ⊞ Q⟦(-1 : ℤ)⟧)) :=
  ((biprod_isZero_iff _ _).2 ⟨hQ m h₀, (hQ (m - 1) (by omega)).of_iso
    (homologyShiftNegOneIso Λ Q m)⟩).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ m).mapBiprod _ _)

end Homology

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY]

include aY in
/-- If `H^q(𝔸¹_k, Λ)` is `Λ` for `q = 0` and vanishes for `q ≠ 0`, then for every separated
`k`-scheme `Y` of finite type and every `Q ∈ Dctf(Y, Λ)`, `Rp_* Lp^* Q ≅ Q` for the projection
`p : 𝔸¹_Y ⟶ Y`. -/
theorem nonempty_iso_rightDerivedLowerStar_affineLine_of_cohomology
    (hA : ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) q).obj (constantComplex Λ _)))
    (eA : (cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 0).obj
      (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y Q) :
    Nonempty ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj Q) ≅ Q) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerStar_constantFunctor_of_isPullback Λ
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) aY) hQ
  obtain ⟨e₂⟩ := nonempty_iso_singleFunctor_of_homology
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).obj (constantComplex Λ _)) hA eA
  exact ⟨e₁ ≪≫ ((derivedTensor _ Y).mapIso ((constantFunctor Λ Y).mapIso e₂ ≪≫
    constantFunctorObjSingleIso Λ Y)).app Q ≪≫ derivedTensorLeftUnitor _ Y Q⟩

include aY in
/-- If `H^q(𝔾_{m,k}, Λ)` is `Λ` for `q = 0, 1` and vanishes for the other `q`, then for every
separated `k`-scheme `Y` of finite type and every `Q ∈ Dctf(Y, Λ)`, `Rπ_* Lπ^* Q ≅ Q ⊕ Q[-1]`
for the projection `π : 𝔾_{m,Y} ⟶ Y`. Here `𝔾_{m,k}` and `𝔾_{m,Y}` are the complements of the
zero sections, given by open immersions `j₀` and `j`. -/
theorem nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology
    {G₀ : Scheme.{u}} (j₀ : G₀ ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j₀]
    (hj₀ : Set.range j₀.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ)
    (hG : ∀ q : ℤ, q ≠ 0 → q ≠ 1 →
      IsZero ((cohomology (ModuleCat.{u + 1} Λ) G₀ q).obj (constantComplex Λ _)))
    (eG₀ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 0).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    (eG₁ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 1).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    {Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y Q) :
    Nonempty ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj Q) ≅
        Q ⊞ Q⟦(-1 : ℤ)⟧) := by
  have : IsAffine G₀ := AffineSpace.isAffine_of_range_eq_compl_zeroSection j₀ hj₀
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerStar_constantFunctor_of_isPullback Λ
    (AffineSpace.isPullback_complementMap_over aY j₀ j hj₀ hj) hQ
  obtain ⟨e₂⟩ := nonempty_iso_biprod_singleFunctor_of_homology
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).obj (constantComplex Λ _)) hG eG₀ eG₁
  exact ⟨e₁ ≪≫ ((derivedTensor _ Y).mapIso ((constantFunctor Λ Y).mapIso e₂)).app Q ≪≫
    constantFunctorBiprodTensorIso Λ Y Q⟩

end Kunneth

section Cardinality

/-- A split monomorphism `φ : F ⟶ G` of étale sheaves of `Λ`-modules is an isomorphism if `G` is
isomorphic to `F` and the geometric stalks of `F` are finite: each stalk map is then an
injective map between finite sets of the same cardinality. -/
theorem isIso_of_isSplitMono_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) [IsSplitMono φ]
    (e : G ≅ F)
    (hF : ∀ x : X, Finite ↑(((X.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F)) :
    IsIso φ := by
  refine isIso_of_isIso_sheafFiber_map φ fun x ↦ ?_
  let Φ := (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : Finite (Φ.obj F) := hF x
  let eF : Φ.obj G ≃ Φ.obj F := (Φ.mapIso e).toLinearEquiv.toEquiv
  have : Finite (Φ.obj G) := Finite.of_equiv _ eF.symm
  have hinj : Function.Injective (Φ.map φ) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hbij : Function.Bijective (Φ.map φ) :=
    hinj.bijective_of_nat_card_le (Nat.card_congr eF).le
  exact (LinearEquiv.ofBijective (Φ.map φ).hom hbij).toModuleIso.isIso_hom

/-- The geometric stalks of the constant sheaf `Λ` are finite when `Λ` is. -/
lemma finite_sheafFiber_homology_constantComplex [Finite Λ] {X : Scheme.{u}} (x : X) :
    Finite ↑(((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ X))) :=
  Finite.of_equiv _ ((X.uliftPointSmallEtale x).sheafFiber.mapIso
    (homologyZeroConstantComplexIso Λ X) ≪≫
      (X.uliftPointSmallEtale x).sheafFiberConstantSheafIso _).toLinearEquiv.toEquiv.symm

/-- A split monomorphism `φ : M ⟶ K` in `D(X_ét, Λ)` out of a complex `M` concentrated in degree
zero is an isomorphism if `K ≅ M` and the geometric stalks of `H⁰(M)` are finite. -/
theorem isIso_of_isSplitMono_of_iso_of_homology {X : Scheme.{u}}
    {M K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ K) [IsSplitMono φ] (e : K ≅ M)
    (hM : ∀ n : ℤ, n ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj M))
    (hM₀ : ∀ x : X, Finite ↑(((X.uliftPointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj M))) :
    IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    exact isIso_of_isSplitMono_of_iso Λ _
      ((_root_.DerivedCategory.homologyFunctor _ 0).mapIso e) hM₀
  · have h₁ := hM n hn
    have h₂ := h₁.of_iso ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e)
    exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

/-- A complex isomorphic to a sheaf `L` in degree zero, all of whose geometric stalks are
isomorphic to `Λ`, is concentrated in degree zero with finite geometric stalks. -/
lemma homology_props_of_iso_singleFunctor [Finite Λ] {X : Scheme.{u}}
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : M ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    (∀ n : ℤ, n ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj M)) ∧
      ∀ x : X, Finite ↑(((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        ((_root_.DerivedCategory.homologyFunctor _ 0).obj M)) := by
  refine ⟨fun n hn ↦ _root_.DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor e hn,
    fun x ↦ ?_⟩
  obtain ⟨eL⟩ := hL _ (X.algClosurePoint x)
  exact Finite.of_equiv _ ((X.uliftPointSmallEtale x).sheafFiber.mapIso
    (_root_.DerivedCategory.homologyFunctorObjIsoOfIsoSingleFunctor e) ≪≫
      (GrothendieckTopology.Point.uliftSheafFiberIso _ _).app L ≪≫ eL).toLinearEquiv.toEquiv.symm

/-- The geometric stalks of the constant sheaf `Λ` are `Λ`. -/
lemma nonempty_sheafFiber_unit_iso {X : Scheme.{u}} (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    Nonempty ((pointSmallEtale s).sheafFiber.obj (𝟙_ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) ≅ ModuleCat.of Λ Λ) :=
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  ⟨(pointSmallEtale s).sheafFiberConstantSheafIso _⟩

end Cardinality

section Unit

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY]

include aY in
/-- If `H^q(𝔸¹_k, Λ)` is `Λ` for `q = 0` and vanishes for `q ≠ 0`, then for every complex `M`
of `Dctf(Y, Λ)` isomorphic to a sheaf with geometric stalks `Λ` in degree zero, the unit
`M ⟶ Rp_* Lp^* M` of the projection `p : 𝔸¹_Y ⟶ Y` is an isomorphism. -/
theorem isIso_unit_affineLine_of_cohomology
    (hA : ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) q).obj (constantComplex Λ _)))
    (eA : (cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 0).obj
      (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y M)
    {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : M ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app M) := by
  have := isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app Λ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
    (AffineSpace.zeroSection _ Y) (AffineSpace.zeroSection_comp_over _ Y) M
  obtain ⟨i⟩ := nonempty_iso_rightDerivedLowerStar_affineLine_of_cohomology Λ aY hA eA hM
  obtain ⟨h₁, h₂⟩ := homology_props_of_iso_singleFunctor Λ e hL
  exact isIso_of_isSplitMono_of_iso_of_homology Λ _ i h₁ h₂

/-- The unit section `t = 1` of the complement `G` of the zero section of `𝔸¹_Y`. -/
noncomputable def complementOneSection {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y))
    [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    Y ⟶ G :=
  IsOpenImmersion.lift j (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y) (by
    rintro _ ⟨y, rfl⟩
    rw [hj]
    exact AffineSpace.oneSection_apply_notMem_range_zeroSection _ Y y)

omit [Finite Λ] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))] in
@[reassoc (attr := simp)]
lemma complementOneSection_comp {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y))
    [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ) :
    complementOneSection j hj ≫ j = AffineSpace.oneSection (ULift.{u} (Fin 1)) Y :=
  IsOpenImmersion.lift_fac _ _ _

include aY in
/-- If `H^q(𝔾_{m,k}, Λ)` is `Λ` for `q = 0, 1` and vanishes for the other `q`, then for every
complex `M` of `Dctf(Y, Λ)` isomorphic to a sheaf with geometric stalks `Λ` in degree zero, the
unit `M ⟶ Rπ_* Lπ^* M` of the projection `π : 𝔾_{m,Y} ⟶ Y` is an isomorphism on `H⁰`. -/
theorem isIso_homology_zero_unit_multiplicativeGroup_of_cohomology
    {G₀ : Scheme.{u}} (j₀ : G₀ ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j₀]
    (hj₀ : Set.range j₀.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ)
    (hG : ∀ q : ℤ, q ≠ 0 → q ≠ 1 →
      IsZero ((cohomology (ModuleCat.{u + 1} Λ) G₀ q).obj (constantComplex Λ _)))
    (eG₀ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 0).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    (eG₁ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 1).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y M)
    {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : M ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app M)) := by
  have := isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app Λ
    (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y) (complementOneSection j hj)
    (by simp [AffineSpace.oneSection_comp_over]) M
  obtain ⟨i⟩ := nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀
    hG eG₀ eG₁ j hj hM
  obtain ⟨h₁, h₂⟩ := homology_props_of_iso_singleFunctor Λ e hL
  exact isIso_of_isSplitMono_of_iso Λ _
    ((_root_.DerivedCategory.homologyFunctor _ 0).mapIso i ≪≫ homologyZeroBiprodShiftIso Λ M h₁) h₂

end Unit

section Localization

variable {X Y Z U : Scheme.{u}} (p : X ⟶ Y) (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i]
  [HasCompactification i] [Finite Λ] [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)
  (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The direct image along `p : X ⟶ Y` of the supported localization triangle
`Ri_* Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶` of a closed–open pair `(i, j)` of `X`. -/
noncomputable abbrev localizationTriangleLowerStar :
    Pretriangulated.Triangle
      (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  (R((p)_*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
    (supportedLocalizationTriangle _ i j L (supportedLocalizationBoundary _ i j hij L))

lemma localizationTriangleLowerStar_mem_distTriang :
    localizationTriangleLowerStar Λ p i j hij L ∈ distTriang _ :=
  (R((p)_*[ModuleCat.{u + 1} Λ])).map_distinguished _
    (supportedLocalizationTriangle_mem_distTriang _ i j hij L)

/-- The first term of `AlgebraicGeometry.Etale.localizationTriangleLowerStar` is
`R(i ≫ p)_* Ri^! L`. -/
noncomputable def localizationTriangleLowerStarObj₁Iso :
    (localizationTriangleLowerStar Λ p i j hij L).obj₁ ≅
      (R((i ≫ p)_*[ModuleCat.{u + 1} Λ])).obj ((R(i)^![Λ]).obj L) :=
  (R((p)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app _) ≪≫
    (rightDerivedLowerStarComp _ i p).app _

/-- The third term of `AlgebraicGeometry.Etale.localizationTriangleLowerStar` is
`R(j ≫ p)_* Lj^* L`. -/
noncomputable def localizationTriangleLowerStarObj₃Iso :
    (localizationTriangleLowerStar Λ p i j hij L).obj₃ ≅
      (R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) :=
  (rightDerivedLowerStarComp _ j p).app _

include hij in
/-- In the direct image along `p` of the localization triangle of `(i, j)`, if `Hⁿ(Rp_* L)` and
`Hⁿ⁺¹(Rp_* L)` vanish, the boundary is an isomorphism
`Hⁿ(R(j ≫ p)_* Lj^* L) ≅ Hⁿ⁺¹(R(i ≫ p)_* Ri^! L)`. -/
theorem nonempty_iso_homology_of_localizationTriangleLowerStar (n : ℤ)
    (h₁ : IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj L)))
    (h₂ : IsZero ((_root_.DerivedCategory.homologyFunctor _ (n + 1)).obj
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj L))) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L)) ≅
      (_root_.DerivedCategory.homologyFunctor _ (n + 1)).obj
        ((R((i ≫ p)_*[ModuleCat.{u + 1} Λ])).obj ((R(i)^![Λ]).obj L))) := by
  let T := localizationTriangleLowerStar Λ p i j hij L
  have hT := localizationTriangleLowerStar_mem_distTriang Λ p i j hij L
  let δ := _root_.DerivedCategory.HomologySequence.δ T n (n + 1) rfl
  have : Mono δ := (_root_.DerivedCategory.HomologySequence.exact₃ T hT n (n + 1) rfl).mono_g
    (h₁.eq_of_src _ _)
  have : Epi δ := (_root_.DerivedCategory.HomologySequence.exact₁ T hT n (n + 1) rfl).epi_f
    (h₂.eq_of_tgt _ _)
  have : IsIso δ := isIso_of_mono_of_epi δ
  exact ⟨(_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (localizationTriangleLowerStarObj₃Iso Λ p i j hij L).symm ≪≫ asIso δ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ (n + 1)).mapIso
      (localizationTriangleLowerStarObj₁Iso Λ p i j hij L)⟩

end Localization

end Etale

end AlgebraicGeometry
