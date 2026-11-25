/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyPullbackComparison

/-! # Untensored comparison of additive etale and Zariski pullback -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Natural section coordinates identify additive etale cohomology with ordinary
structure-module cohomology, compatibly with the untensored pullback.
Source: Stacks Project, Tag 03P2, Theorem etale-cohomology-theorem-zariski-fpqc-quasi-coherent,
and Tag 02KH, the canonical cohomology comparison before tensor extension.
(blueprint: lem-pbc-additive-cohomology-base-change-square)

Proof: Take the coordinate-normalized additive comparisons. For every c choose
mu from hscalar c. Its section formula lets the comparison's scalar identity
apply, while its cohomology formula identifies H(mu) with the supplied c-action.
This proves scalar compatibility of the first additive equivalence. Repeat with
hscalar' for the second. Upgrade the two additive equivalences to linear ones;
their underlying functions are unchanged, so the untensored pullback square is
the additive square supplied by the comparison theorem. -/
theorem exists_additive_cohomology_baseChange_square
    {k k' : Type u}
    [CommRing k] [CommRing k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [CompactSpace C] [IsSeparated f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ)
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
    (hq : (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)))
    [Module k (Sheaf.H G n)] [Module k' (Sheaf.H G' n)]
    (hscalar : ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G n,
          Sheaf.H.map μ n x = c • x)
    (hscalar' : ∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' n,
          Sheaf.H.map μ n x = c • x) :
    ∃ e : Sheaf.H G n ≃ₗ[k] HOver f (SheafOfModules.unit C.ringCatSheaf) n,
      ∃ e' : Sheaf.H G' n ≃ₗ[k']
        HOver (baseChangeSnd (S := k') f)
          (baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf)) n,
        ∀ x, e' (Sheaf.H.map q n (Etale.cohomologyMap ι' G n x)) =
          H.baseChangeLinear (S := k') f (SheafOfModules.unit C.ringCatSheaf) n (e x) := by
  obtain ⟨e, e', hs, hs', he⟩ := exists_additive_cohomology_pullback_comparison
    f h n G G' a a' ha ha' q hq
  have es (c : k) (x : Sheaf.H G n) : e (c • x) = c • e x := by
    obtain ⟨μ, hμ, hμH⟩ := hscalar c
    rw [← hμH x]
    exact hs c μ hμ x
  have es' (c : k') (x : Sheaf.H G' n) : e' (c • x) = c • e' x := by
    obtain ⟨μ, hμ, hμH⟩ := hscalar' c
    rw [← hμH x]
    exact hs' c μ hμ x
  exact ⟨{ e with map_smul' := es }, { e' with map_smul' := es' }, he⟩

end AlgebraicGeometry.Scheme.Modules
