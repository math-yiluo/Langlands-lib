/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.NormalGenericConstant
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# The normalisation of a curve and constant sheaves

Let `ν : X' ⟶ X` be a finite morphism (e.g. the normalisation of a reduced curve) and `M` a
`Λ`-module. The natural map `M_X ⟶ ν_* M_{X'}`
(`AlgebraicGeometry.Etale.constantSheafToLowerStar`) is the unit of `ν^* ⊣ ν_*` followed by the
identification `ν^* M_X ≅ M_{X'}`. On the stalk at a geometric point `y` of `X` it is the
diagonal `M ⟶ M^b`, where `b` is the number of geometric points of `X'` over `y`: the number of
geometric branches of `X` at `y` when `ν` is the normalisation. Hence its cokernel has stalk
`M^b / ΔM`.

## Main statements

- `AlgebraicGeometry.Etale.mono_constantSheafToLowerStar`: the natural map
  `M_X ⟶ ν_* M_{X'}` (`AlgebraicGeometry.Etale.constantSheafToLowerStar`) is injective for
  surjective `ν`.
- `AlgebraicGeometry.IsCurve.constantSheafToLowerStar_of_isIso_restrict`: for a finite surjective
  `ν` which is an isomorphism over a dense open of a curve, this map is injective, its cokernel
  is supported on finitely many points and has stalk `M^b / ΔM` at a point with `b` geometric
  branches.
- `AlgebraicGeometry.Etale.exists_upperStar_constantSheafToLowerStar_iso`: the map, its cokernel
  and the resulting exact sequence commute with base change, e.g. along an algebraically closed
  field extension.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

section Map

variable {X X' : Scheme.{u}} (ν : X' ⟶ X) (M : ModuleCat.{u + 1} Λ)

/-- `AlgebraicGeometry.Etale.constantSheafToLowerStar` unfolded, with the constant sheaf kept
folded. -/
lemma Etale.constantSheafToLowerStar_eq :
    constantSheafToLowerStar ν M =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
        (ν)_*[ModuleCat.{u + 1} Λ].map
          ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) ν).hom.app M) :=
  rfl

/-- For a surjective `ν`, the natural map `M_X ⟶ ν_* M_{X'}` is a monomorphism. -/
theorem Etale.mono_constantSheafToLowerStar (hν : Function.Surjective ν.base) :
    Mono (constantSheafToLowerStar ν M) := by
  exact mono_comp' (mono_unit_app_of_surjective Λ ν hν _) inferInstance

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X)

/-- On stalks at `y`, each component `M_y ⟶ M_t` of the natural map `M_X ⟶ ν_* M_{X'}`, indexed
by a geometric point `t` of `X'` over `y`, is an isomorphism. -/
lemma Etale.isIso_sheafFiber_map_constantSheafToLowerStar_comp_stalkRestrict
    (t : ν.GeometricFiber y) :
    IsIso ((pointSmallEtale y).sheafFiber.map (constantSheafToLowerStar ν M) ≫
      stalkRestrict (ModuleCat.{u + 1} Λ) ν y t
        ((constantSheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  obtain ⟨s, hs⟩ := t
  subst hs
  have h := sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso_moduleCat ν
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) s
  rw [← Iso.app_hom, ← Category.assoc, Iso.comp_hom_eq_id] at h
  rw [constantSheafToLowerStar_eq, Functor.map_comp, Category.assoc,
    ← stalkRestrict_naturality, ← Category.assoc, h]
  infer_instance

/-- **The stalks of the cokernel of `M_X ⟶ ν_* M_{X'}`.** For a finite `ν : X' ⟶ X` and a
geometric point `y` of `X`, the stalk at `y` of the cokernel of the natural map
`M_X ⟶ ν_* M_{X'}` is `M^b / ΔM`, where `b` runs over the geometric points of `X'` over `y` and
`Δ` is the diagonal. -/
theorem Etale.nonempty_sheafFiber_cokernel_constantSheafToLowerStar_iso [IsFinite ν] :
    Nonempty ((pointSmallEtale y).sheafFiber.obj (cokernel (constantSheafToLowerStar ν M)) ≅
      ModuleCat.of.{u + 1} Λ ((ν.GeometricFiber y → M) ⧸
        LinearMap.range (LinearMap.pi fun _ ↦ (LinearMap.id : M →ₗ[Λ] M)))) := by
  classical
  let S := (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let G := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let G' := (constantSheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let α := constantSheafToLowerStar ν M
  let ψ (t : ν.GeometricFiber y) := S.map α ≫ stalkRestrict (ModuleCat.{u + 1} Λ) ν y t G'
  have (t : ν.GeometricFiber y) : IsIso (ψ t) :=
    isIso_sheafFiber_map_constantSheafToLowerStar_comp_stalkRestrict ν M y t
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u, u + 1}
  let p : S.obj G ≅ M :=
    (((pointSmallEtale y).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G).symm ≪≫
      ((pointSmallEtale y).ulift.{u + 1}).sheafFiberConstantSheafIso M
  let d : M ⟶ ModuleCat.of.{u + 1} Λ (ν.GeometricFiber y → M) :=
    ModuleCat.ofHom (LinearMap.pi fun _ ↦ LinearMap.id)
  let q : S.obj ((ν)_*[ModuleCat.{u + 1} Λ].obj G') ≅
      ModuleCat.of.{u + 1} Λ (ν.GeometricFiber y → M) :=
    stalkIsoPi (ModuleCat.{u + 1} Λ) ν y G' ≪≫ Pi.mapIso (fun t ↦ (asIso (ψ t)).symm ≪≫ p) ≪≫
      ModuleCat.piIsoPi.{u + 1, u, u + 1} (fun _ ↦ M)
  have w : S.map α ≫ q.hom = p.hom ≫ d := by
    rw [← cancel_mono (ModuleCat.piIsoPi.{u + 1, u, u + 1} (fun _ : ν.GeometricFiber y ↦ M)).inv]
    refine Pi.hom_ext _ _ fun t ↦ ?_
    have h₁ : S.map α ≫ stalkRestrict (ModuleCat.{u + 1} Λ) ν y t G' ≫ inv (ψ t) = 𝟙 _ := by
      rw [← Category.assoc]
      exact IsIso.hom_inv_id (ψ t)
    simp only [q, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [Pi.mapIso_hom_π, stalkIsoPi_hom, Pi.lift_comp_π_assoc, Iso.trans_hom, Iso.symm_hom,
      asIso_inv, reassoc_of% h₁, ModuleCat.piIsoPi_inv_kernel_ι]
    ext x
    rfl
  exact ⟨PreservesCokernel.iso S α ≪≫ cokernel.mapIso _ d p q w ≪≫
    ModuleCat.cokernelIsoRangeQuotient d⟩

end Map

/-- Let `X` be a curve over a field `k`, `ν : X' ⟶ X` a finite surjective morphism which is an
isomorphism over a dense open `V ⊆ X` and `M` a `Λ`-module. Then the natural map
`M_X ⟶ ν_* M_{X'}` is injective, its cokernel vanishes at every geometric point outside a finite
set, and at a geometric point `y` the cokernel has stalk `M^b / ΔM`, where `b` runs over the
geometric points of `X'` over `y` and `Δ` is the diagonal. -/
theorem IsCurve.constantSheafToLowerStar_of_isIso_restrict {k : Type u} [Field k]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] (ν : X' ⟶ X) [IsFinite ν]
    [Surjective ν] (V : X.Opens) (hV : Dense (V : Set X)) [IsIso (ν ∣_ V)]
    (M : ModuleCat.{u + 1} Λ) :
    Mono (constantSheafToLowerStar ν M) ∧
      (∃ Z : Set X, Z.Finite ∧ ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ X), y default ∉ Z →
          IsZero ((pointSmallEtale y).sheafFiber.obj (cokernel (constantSheafToLowerStar ν M)))) ∧
      ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale y).sheafFiber.obj (cokernel (constantSheafToLowerStar ν M)) ≅
          ModuleCat.of.{u + 1} Λ ((ν.GeometricFiber y → M) ⧸
            LinearMap.range (LinearMap.pi fun _ ↦ (LinearMap.id : M →ₗ[Λ] M)))) := by
  classical
  refine ⟨mono_constantSheafToLowerStar ν M ν.surjective, ⟨(V : Set X)ᶜ, ?_, ?_⟩,
    fun y ↦ nonempty_sheafFiber_cokernel_constantSheafToLowerStar_iso ν M y⟩
  · have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
    exact finite_compl_of_dense_of_topologicalKrullDim_le_one
      (IsCurve.krullDim_le_one (f := f)) hV V.isOpen
  · intro Ω _ _ y hy
    rw [Set.notMem_compl_iff] at hy
    obtain ⟨s, rfl⟩ : ∃ s : Spec (.of Ω) ⟶ V, s ≫ V.ι = y := by
      refine ⟨IsOpenImmersion.lift V.ι y ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim z default]
      exact hy
    have : IsIso (pullback.snd ν V.ι) := by
      rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
      infer_instance
    have := uniqueGeometricFiberOfIsIsoPullbackSnd ν V.ι this s
    obtain ⟨e⟩ := nonempty_sheafFiber_cokernel_constantSheafToLowerStar_iso ν M (s ≫ V.ι)
    refine IsZero.of_iso (@ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b ↦ ?_⟩) e
    induction a using Submodule.Quotient.induction_on with | H a => ?_
    induction b using Submodule.Quotient.induction_on with | H b => ?_
    rw [Submodule.Quotient.eq]
    refine ⟨a default - b default, funext fun t ↦ ?_⟩
    rw [Subsingleton.elim t default]
    simp

/-- The identifications `f^* A_Y ≅ A_X` are compatible with composition, for any choice of the
composite `h₁₂ = g ≫ h`. -/
private lemma upperStarConstantSheafIso_comp_of_eq {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) (h₁₂ : X ⟶ Z) (hh : h₁₂ = g ≫ h) (M : ModuleCat.{u + 1} Λ) :
    (upperStarComp (ModuleCat.{u + 1} Λ) g h h₁₂ hh).hom.app
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
      (g)^*[ModuleCat.{u + 1} Λ].map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) h).hom.app M) ≫
        (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M =
      (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) h₁₂).hom.app M := by
  subst hh
  exact upperStarConstantSheafIso_comp (ModuleCat.{u + 1} Λ) g h M

/-- For a cartesian square
```
Y' --g'--> X'
|          |
ν'         ν
v          v
Y  --g-->  X
```
with `ν` finite, there are isomorphisms `a : g^* M_X ≅ M_Y`, `b : g^* ν_* M_{X'} ≅ ν'_* M_{Y'}`
and `c : g^* Q ≅ Q'` of the cokernels `Q`, `Q'` of the natural maps `M_X ⟶ ν_* M_{X'}` and
`M_Y ⟶ ν'_* M_{Y'}`, commuting with these maps and the projections to the cokernels. -/
theorem Etale.exists_upperStar_constantSheafToLowerStar_iso {X X' Y Y' : Scheme.{u}}
    {ν : X' ⟶ X} {g : Y ⟶ X} {g' : Y' ⟶ X'} {ν' : Y' ⟶ Y} [IsFinite ν]
    (h : IsPullback g' ν' ν g) (M : ModuleCat.{u + 1} Λ) :
    ∃ (a : (g)^*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
      (b : (g)^*[ModuleCat.{u + 1} Λ].obj ((ν)_*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
        (ν')_*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
      (c : (g)^*[ModuleCat.{u + 1} Λ].obj (cokernel (constantSheafToLowerStar ν M)) ≅
        cokernel (constantSheafToLowerStar ν' M)),
      (g)^*[ModuleCat.{u + 1} Λ].map (constantSheafToLowerStar ν M) ≫ b.hom =
          a.hom ≫ constantSheafToLowerStar ν' M ∧
        (g)^*[ModuleCat.{u + 1} Λ].map (cokernel.π (constantSheafToLowerStar ν M)) ≫ c.hom =
          b.hom ≫ cokernel.π (constantSheafToLowerStar ν' M) := by
  let A := ModuleCat.{u + 1} Λ
  let cst (Z : Scheme.{u}) := (constantSheaf Z.smallEtaleTopology A).obj M
  have := isIso_baseChangeMap_of_isFinite A h
  let a : (g)^*[A].obj (cst X) ≅ cst Y := (upperStarConstantSheafIso A g).app M
  let b : (g)^*[A].obj ((ν)_*[A].obj (cst X')) ≅ (ν')_*[A].obj (cst Y') :=
    asIso ((baseChangeMap A h.toCommSq).app (cst X')) ≪≫
      (ν')_*[A].mapIso ((upperStarConstantSheafIso A g').app M)
  -- the two identifications `ν'^* g^* M_X ≅ M_{Y'}` agree
  have key : (squareUpperStarIso A h.toCommSq).hom.app (cst X) ≫
      (g')^*[A].map ((upperStarConstantSheafIso A ν).hom.app M) ≫
        (upperStarConstantSheafIso A g').hom.app M =
      (ν')^*[A].map ((upperStarConstantSheafIso A g).hom.app M) ≫
        (upperStarConstantSheafIso A ν').hom.app M := by
    have h₁ := upperStarConstantSheafIso_comp_of_eq ν' g (g' ≫ ν) h.w M
    have h₂ := upperStarConstantSheafIso_comp A g' ν M
    rw [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      h₂, ← h₁, Iso.inv_hom_id_app_assoc]
  have w : (g)^*[A].map (constantSheafToLowerStar ν M) ≫ b.hom =
      a.hom ≫ constantSheafToLowerStar ν' M := by
    have hn := (baseChangeMap A h.toCommSq).naturality
      ((upperStarConstantSheafIso A ν).hom.app M)
    simp only [Functor.comp_map] at hn
    simp only [b, a, constantSheafToLowerStar_eq, Functor.map_comp, Category.assoc, Iso.trans_hom,
      asIso_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [reassoc_of% hn, reassoc_of% (map_unit_baseChangeMap_app A h.toCommSq (cst X)),
      ← Functor.map_comp, ← Functor.map_comp, key]
    have hu := (upperStarLowerStarAdjunction A ν').unit.naturality
      ((upperStarConstantSheafIso A g).hom.app M)
    simp only [Functor.id_map, Functor.comp_map] at hu
    rw [reassoc_of% hu, Functor.map_comp]
  refine ⟨a, b, PreservesCokernel.iso (g)^*[A] _ ≪≫ cokernel.mapIso _ _ a b w, w, ?_⟩
  simp only [Iso.trans_hom, cokernel.mapIso_hom]
  rw [← π_comp_cokernelComparison, ← PreservesCokernel.iso_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact cokernel.π_desc _ _ _

end AlgebraicGeometry
