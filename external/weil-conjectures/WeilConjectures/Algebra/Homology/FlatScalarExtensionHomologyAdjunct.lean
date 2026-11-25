/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Cohomology of flat extension of coefficients

Source: Stacks Project, Tags 00HD and 0A1D, lemma-base-change-tensor.
(blueprint: lem-pc-flat-scalar-extension-homology-adjunct).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

/-- The cohomology adjunct of the canonical coefficient map is an isomorphism
when the final extension is flat. Source: Stacks Project, Tag 00HD (lemma-flat)
and the coefficient associativity used in Tag 0A1D (lemma-base-change-tensor).
(blueprint: lem-pc-flat-scalar-extension-homology-adjunct).

Proof: Flatness makes extension E to D exact by tensoring exact sequences
(Tag 00HD). Applying it to the cycle and boundary sequences gives the canonical
isomorphism from D tensor E H(K) to H(D tensor E K). The transposition of the
termwise unit K to restriction of D tensor E K induces precisely this
isomorphism on cohomology, by naturality of the homology comparison with respect
to the adjunction unit. Here K is E tensor A Q. Tensor associativity identifies
D tensor E K with D tensor A Q; it sends d tensor (e tensor q) to d*g(e)
tensor q, commuting with differentials. The specified pure-tensor formula
uniquely fixes φ as the unit followed by this associativity isomorphism.
Functoriality of homology and adjunction thus identify the stated adjunct with
the composite of the exact homology isomorphism and homology of associativity.
Both factors are invertible. This also covers zero rings and zero complexes,
and does not require A to be flat over any ring. -/
theorem flatScalarExtensionHomologyAdjunct_isIso
    {A E D : Type u} [CommRing A] [CommRing E] [CommRing D]
    (f : A →+* E) (g : E →+* D) [Algebra E D]
    (hg : g = algebraMap E D) (hD : Module.Flat E D)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hφ : ∀ (j : ℤ) (e : E) (q : Q.X j),
      φ.f j (e ⊗ₜ[A,f] q) = g e ⊗ₜ[A,g.comp f] q) (i : ℤ) :
    IsIso (((extendRestrictScalarsAdj g).homEquiv _ _).symm
      (HomologicalComplex.homologyMap φ i ≫
        (((((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q).sc i
          ).mapHomologyIso (restrictScalars g)).hom))  := by
  subst hg
  let g := algebraMap E D
  have : Module.Flat E D := hD
  have : PreservesFiniteLimits (extendScalars g) :=
    preservesFiniteLimits_extendScalars_of_flat (RingHom.flat_algebraMap_iff.mpr hD)
  let F := extendScalars g
  let G := restrictScalars g
  let adj := extendRestrictScalarsAdj g
  let K := ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q
  let T := ((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj Q
  let e : ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅ T :=
    (Functor.mapHomologicalComplexCompIso (extendScalarsComp f g).symm (.up ℤ)).app Q
  have htrans (j : ℤ) : φ.f j = (adj.homEquiv _ _) (e.hom.f j) := by
    apply ExtendScalars.hom_ext
    intro q
    erw [hφ j 1 q, map_one]
    change (1 : D) ⊗ₜ[A, g.comp f] q =
      ((extendScalarsComp f g).inv.app (Q.X j))
        ((1 : D) ⊗ₜ[E,g] ((1 : E) ⊗ₜ[A,f] q))
    rw [← extendScalarsComp_hom_app_one_tmul f g (Q.X j) q]
    exact ((extendScalarsComp f g).app (Q.X j)).toLinearEquiv.symm_apply_apply _ |>.symm
  let S := K.sc i
  let U := T.sc i
  let ψ : S.map F ⟶ U := (HomologicalComplex.shortComplexFunctor _ _ i).map e.hom
  have : IsIso ψ := inferInstance
  let τ : S ⟶ U.map G := (HomologicalComplex.shortComplexFunctor _ _ i).map φ
  let h := S.homologyData.left
  let k := U.homologyData.left
  let γ : ShortComplex.LeftHomologyMapData ψ (h.map F) k := default
  let δ : ShortComplex.LeftHomologyMapData τ h (k.map G) :=
    { φK := (adj.homEquiv _ _) γ.φK
      φH := (adj.homEquiv _ _) γ.φH
      commi := by
        change (adj.homEquiv _ _) γ.φK ≫ G.map k.i = h.i ≫ τ.τ₂
        rw [← adj.homEquiv_naturality_right]
        change _ = h.i ≫ φ.f i
        rw [htrans i]
        change _ = h.i ≫ (adj.homEquiv S.X₂ U.X₂) ψ.τ₂
        erw [← adj.homEquiv_naturality_left]
        exact congrArg (adj.homEquiv _ _) γ.commi
      commf' := by
        rw [ShortComplex.LeftHomologyData.map_f']
        change h.f' ≫ (adj.homEquiv _ _) γ.φK = τ.τ₁ ≫ G.map k.f'
        rw [← adj.homEquiv_naturality_left]
        change _ = φ.f ((ComplexShape.up ℤ).prev i) ≫ G.map k.f'
        rw [htrans, ← adj.homEquiv_naturality_right]
        change (adj.homEquiv S.X₁ k.K) (F.map h.f' ≫ γ.φK) =
          (adj.homEquiv S.X₁ k.K) (ψ.τ₁ ≫ k.f')
        apply congrArg (adj.homEquiv S.X₁ k.K)
        simpa only [ShortComplex.LeftHomologyData.map_f'] using γ.commf'
      commπ := by
        change h.π ≫ (adj.homEquiv _ _) γ.φH =
          (adj.homEquiv _ _) γ.φK ≫ G.map k.π
        rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        exact congrArg (adj.homEquiv _ _) γ.commπ }
  have hγ : IsIso γ.φH :=
    (γ.quasiIso_iff).1 inferInstance
  have heq : ((adj.homEquiv _ _).symm
      (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom)) =
      F.map h.homologyIso.hom ≫ γ.φH ≫ k.homologyIso.inv := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left,
      adj.homEquiv_naturality_right]
    change ShortComplex.homologyMap τ ≫ (U.mapHomologyIso G).hom = _
    rw [δ.homologyMap_eq, k.mapHomologyIso_eq G]
    simp [δ, Category.assoc]
    rfl
  change IsIso ((adj.homEquiv _ _).symm
    (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom))
  rw [heq]
  infer_instance

end ModuleCat
