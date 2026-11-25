/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizationCover
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.ConstructibleSheaf.LisseTrivialization
public import WeilConjectures.ConstructibleSheaf.NormalGenericConstant
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Direct images of lisse sheaves along normal open immersions

Let `Λ` be a finite commutative ring.

- `AlgebraicGeometry.Etale.isIso_constantSheafToLowerStar_of_isOpenImmersion` (blueprint
  `lem-fin-normal-constant-open-image`): on a locally Noetherian normal integral scheme `Y`, the
  map `M_Y ⟶ v_* M_V` is an isomorphism for every nonempty open immersion `v : V ⟶ Y`.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_constantSheaf_of_isFinite` (blueprint
  `lem-fin-finite-constant-pushforward`): finite direct images of finite constant sheaves over a
  base of finite type over a field are constructible.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFiniteLocallyConstantSheaf`
  (blueprint `lem-fin-normal-open-lisse-image`): for a nonempty normal open `k : V ⟶ X` of an
  integral scheme of finite type over a field and a finite locally constant sheaf `L` on `V`, the
  direct image `k_* L` is constructible. A connected finite étale cover `p : P ⟶ V` trivializes
  `L` (`AlgebraicGeometry.Scheme.exists_isConstant_upperStar_of_connectedSpace`), so that `k_* L`
  embeds into `(p ≫ k)_* M_P = g_* v_* M_P = g_* M_Y`, where `P ⟶ Y ⟶ X` is the normalization of
  `X` in `P` (`AlgebraicGeometry.Scheme.normalization_comp_of_finite_etale`), with `g` finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-fin-normal-constant-open-image`: A constant sheaf across a dense normal open.

Let `Y` be a locally Noetherian normal integral scheme (integral, with integrally closed local
rings), `v : V ⟶ Y` an open immersion with `V` nonempty and `M` a module. The canonical map
`M_Y ⟶ v_* M_V` of étale sheaves is an isomorphism. The blueprint states this for a finite
module; finiteness is not needed. -/
theorem isIso_constantSheafToLowerStar_of_isOpenImmersion {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (v : V ⟶ Y) [IsOpenImmersion v] [Nonempty V] (M : ModuleCat.{u + 1} Λ) :
    IsIso (constantSheafToLowerStar v M) := by
  have hX (W : Y.Etale) (w : W.left) : IsDomain (W.left.presheaf.stalk w) := by
    have : AlgebraicGeometry.Etale W.hom := W.prop
    exact (Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale (Y := Y) W.hom hY w).1
  have hd : Dense (Set.range v.base) :=
    v.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have := isIso_unit_upperStarLowerStarAdjunction_of_isDomain_stalk v hX hd
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance

variable [Finite Λ]

omit [Finite Λ] in
/-- The constant sheaf of a finite module over a finite ring is constructible, being finite
locally constant. -/
lemma isConstructibleSheaf_constantSheaf {V : Scheme.{u}} (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsConstructibleSheaf ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : IsFiniteSheaf ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    ⟨fun Ω _ _ s ↦ (ConcreteCategory.IsFinitelyGenerated.of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm
      ((ModuleCat.isFinitelyGenerated_iff M).2 inferInstance))⟩
  exact IsFiniteLocallyConstantSheaf.isConstructibleSheaf {}

/-- Blueprint `lem-fin-finite-constant-pushforward`: Finite pushforwards of constant sheaves.

Let `g : V ⟶ S` be finite with `S` of finite type over a field `k`, and `M` a finite module over
the finite ring `Λ` (e.g. a finite abelian group, `Λ = ℤ/N`). Then `g_* M_V` is constructible
on `S_ét`: the constant sheaf `M_V` is constructible, and so are finite direct images of
constructible sheaves (`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFinite`). -/
theorem isConstructibleSheaf_lowerStar_constantSheaf_of_isFinite {k : Type u} [Field k]
    {V S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (g : V ⟶ S) [IsFinite g] (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsConstructibleSheaf ((g)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have := isConstructibleSheaf_constantSheaf (V := V) M
  exact (isConstructibleSheaf_lowerStar_of_isFinite aS g _).1

/-- Blueprint `lem-fin-normal-open-lisse-image`: A lisse sheaf on a normal open has constructible
direct image.

Let `X` be an integral scheme of finite type over a field `k`, `kV : V ⟶ X` an open immersion with
`V` nonempty and normal (its local rings are integrally closed), and `L` a finite locally
constant sheaf of modules over a finite ring `Λ` on `V_ét`. Then `kV_* L` is constructible.

Choose a connected finite étale surjective `p : P ⟶ V` with `p^* L ≅ M_P` constant. The unit
`L ⟶ p_* p^* L` is injective, `p` being surjective, so `kV_* L` embeds into
`(p ≫ kV)_* M_P`. Factoring `p ≫ kV` through the normalization `Y` of `X` in `P` as an open
immersion `v` followed by the finite `g`, with `Y` normal integral, gives
`(p ≫ kV)_* M_P ≅ g_* v_* M_P ≅ g_* M_Y`, which is constructible; so is its subsheaf
`kV_* L` (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`). -/
theorem isConstructibleSheaf_lowerStar_of_isFiniteLocallyConstantSheaf {k : Type u} [Field k]
    {V X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsIntegral X] (kV : V ⟶ X) [IsOpenImmersion kV] [Nonempty V]
    (hV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf L] :
    IsConstructibleSheaf ((kV)_*[ModuleCat.{u + 1} Λ].obj L) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  have : IsIntegral V := isIntegral_of_isOpenImmersion kV
  -- a connected finite étale cover trivializing `L`
  obtain ⟨P, p, hpf, hpe, hps, hPc, M, hM, ⟨eM⟩⟩ :=
    Scheme.exists_isConstant_upperStar_of_connectedSpace L
  -- the normalization of `X` in `P`
  obtain ⟨hPi, hPn, hv, hg, hYi, hYn, -⟩ :=
    Scheme.normalization_comp_of_finite_etale aX kV hV p
  let f := p ≫ kV
  let v := f.toNormalization
  let g := f.fromNormalization
  have : IsLocallyNoetherian f.normalization := by
    have : LocallyOfFiniteType (g ≫ aX) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (g ≫ aX)
  have : Nonempty P := inferInstance
  -- `kV_* L` embeds into `kV_* p_* p^* L`
  have : Mono ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app L) :=
    mono_unit_app_of_surjective Λ p hps.surj L
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) kV).isRightAdjoint
  let ι := (kV)_*[ModuleCat.{u + 1} Λ].map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app L)
  -- `kV_* p_* p^* L ≅ g_* M_Y`
  have : IsIso (constantSheafToLowerStar v M) :=
    isIso_constantSheafToLowerStar_of_isOpenImmersion hYn v M
  let e : (kV)_*[ModuleCat.{u + 1} Λ].obj ((p)_*[ModuleCat.{u + 1} Λ].obj
      ((p)^*[ModuleCat.{u + 1} Λ].obj L)) ≅ (g)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf f.normalization.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    (lowerStarComp (ModuleCat.{u + 1} Λ) p kV).app _ ≪≫ (f)_*[ModuleCat.{u + 1} Λ].mapIso eM ≪≫
      ((lowerStarComp (ModuleCat.{u + 1} Λ) v g f
        (f.toNormalization_fromNormalization).symm).app _).symm ≪≫
      (g)_*[ModuleCat.{u + 1} Λ].mapIso (asIso (constantSheafToLowerStar v M)).symm
  have := isConstructibleSheaf_lowerStar_constantSheaf_of_isFinite aX g M
  have : IsConstructibleSheaf ((kV)_*[ModuleCat.{u + 1} Λ].obj
      (((p)^*[ModuleCat.{u + 1} Λ] ⋙ (p)_*[ModuleCat.{u + 1} Λ]).obj L)) :=
    IsConstructibleSheaf.of_iso e.symm
  exact Scheme.IsConstructibleSheaf.of_mono ι

end Etale

end AlgebraicGeometry

end
