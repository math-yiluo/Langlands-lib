/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport

/-! # Untensored comparison of additive etale and Zariski pullback -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def coordinateIso {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    G ≅ X.etaleAdditiveSheaf :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦ ((a U).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun g ↦ by ext x; apply ULift.ext; exact ha _ _ g x))

private theorem coordinateIso_smul {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (r : Γ(X, ⊤)) (μ : G ⟶ G)
    (hμ : ∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (μ.hom.app U x) = a U x * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) :
    μ ≫ (coordinateIso G a ha).hom =
      (coordinateIso G a ha).hom ≫ etaleAdditiveSmul X r := by
  ext U x
  apply ULift.ext
  exact hμ U x

private theorem coordinateIso_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : Y.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : X.Etaleᵒᵖ) (s : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map s x) = s.unop.left.appTop (a U x))
    (ha' : ∀ (U V : Y.Etaleᵒᵖ) (s : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map s x) = s.unop.left.appTop (a' U x))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} g).obj G ⟶ G')
    (hq : ∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
      a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U.unop))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
          G G' q).hom.app U x) = (Limits.pullback.fst U.unop.hom g).appTop (a U x)) :
    q ≫ (coordinateIso G' a' ha').hom =
      (Etale.upperStar AddCommGrpCat.{u + 1} g).map (coordinateIso G a ha).hom ≫
        etaleAdditivePullback g := by
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  apply (adj.homEquiv _ _).injective
  have he : adj.homEquiv X.etaleAdditiveSheaf Y.etaleAdditiveSheaf
      (etaleAdditivePullback g) = Scheme.etaleAdditiveSheafToLowerStar g :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, he]
  ext U x
  apply ULift.ext
  exact hq U x

/-- Coordinate-normalized additive comparisons commute with structural scalar
endomorphisms and untensored pullback. No module actions on G.H or G'.H are inputs.
Source: Stacks Project, Tag 03P2, Theorem etale-cohomology-theorem-zariski-fpqc-quasi-coherent,
and Tag 02KH, the canonical cohomology comparison before tensor extension.
(blueprint: lem-pbc-additive-cohomology-pullback-comparison)

Proof: Use natural section coordinates for the associated etale unit module to
identify G with its coefficient lift: on U send x to the lift of the inverse
unit coordinate applied to a U x. Naturality of both coordinate families gives
an isomorphism of sheaves. Do the same for G'. Compose their cohomology maps
with the natural coefficient-lift, etale/Zariski, and ordinary Ext comparisons.
Transport the target unit module through the pullback-unit isomorphism and the
unique isomorphism between the displayed cartesian square and the categorical
pullback. These give additive equivalences e and e'. For each scalar, the
section-coordinate formula determines its endomorphism uniquely. Naturality
of all comparisons for these endomorphisms therefore give the two scalar
endomorphism identities, in the ordinary structural module actions.
For pullback compatibility choose a finite affine cover of C and a finite
affine cover of C' refining its inverse image cover. The refinement exists by
quasi-compactness of C'. Tuple intersections within either affine cover are
affine by separatedness. The section formula hq identifies the coefficient
map with structural pullback on the refined intersections. The natural affine
Cech inverse-image comparison thus gives the same map on cycle classes as
H.baseChangeLinear. Every cohomology class is
represented by such a cycle, giving the stated equality. Transport the equality
through the displayed-pullback isomorphism. No tensor exactness, flatness,
injectivity, surjectivity, dimension bound or properness is used. Empty schemes
and degree zero are included by the same section complexes. -/
theorem exists_additive_cohomology_pullback_comparison
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
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x))) :
    ∃ e : Sheaf.H G n ≃+ HOver f (SheafOfModules.unit C.ringCatSheaf) n,
      ∃ e' : Sheaf.H G' n ≃+
        HOver (baseChangeSnd (S := k') f)
          (baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf)) n,
      (∀ (c : k) (μ : G ⟶ G),
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) →
        ∀ x, e (Sheaf.H.map μ n x) = c • e x) ∧
      (∀ (c : k') (μ : G' ⟶ G'),
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) →
        ∀ x, e' (Sheaf.H.map μ n x) = c • e' x) ∧
      ∀ x, e' (Sheaf.H.map q n (Etale.cohomologyMap ι' G n x)) =
        H.baseChangeLinear (S := k') f (SheafOfModules.unit C.ringCatSheaf) n (e x) := by
  classical
  let : C.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from f]
    infer_instance
  let : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  let : C'.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from f']
    infer_instance
  let : CompactSpace C' := by
    have : QuasiCompact f := inferInstance
    have : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace f'
  obtain ⟨b, b', hb, hb', hbb'⟩ := exists_canonical_additive_cohomology_square ι' n
  obtain ⟨t, ht⟩ := exists_cartesian_unit_cohomology_transport f h n
  let i := coordinateIso G a ha
  let i' := coordinateIso G' a' ha'
  let d : Sheaf.H G n ≃+ Sheaf.H C.etaleAdditiveSheaf n :=
    ((Sheaf.functorH.{u + 1} C.smallEtaleTopology n).mapIso i).addCommGroupIsoToAddEquiv
  let d' : Sheaf.H G' n ≃+ Sheaf.H C'.etaleAdditiveSheaf n :=
    ((Sheaf.functorH.{u + 1} C'.smallEtaleTopology n).mapIso i').addCommGroupIsoToAddEquiv
  refine ⟨d.trans b, (d'.trans b').trans t.toAddEquiv, ?_, ?_, ?_⟩
  · intro c μ hμ x
    let r : Γ(C, ⊤) := (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) c
    have hi := coordinateIso_smul G a ha r μ hμ
    change b (Sheaf.H.map i.hom n (Sheaf.H.map μ n x)) = _
    rw [← Sheaf.H.map_comp_apply, hi, Sheaf.H.map_comp_apply, hb]
    rfl
  · intro c μ hμ x
    let r : Γ(C', ⊤) := (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom) c
    have hi' := coordinateIso_smul G' a' ha' r μ hμ
    change t (b' (Sheaf.H.map i'.hom n (Sheaf.H.map μ n x))) = _
    rw [← Sheaf.H.map_comp_apply, hi', Sheaf.H.map_comp_apply, hb']
    exact t.map_smul c _
  · intro x
    have hiq := coordinateIso_pullback ι' G G' a a' ha ha' q hq
    change t (b' (Sheaf.H.map i'.hom n
      (Sheaf.H.map q n (Etale.cohomologyMap ι' G n x)))) = _
    rw [← Sheaf.H.map_comp_apply, hiq, Sheaf.H.map_comp_apply,
      ← Etale.cohomologyMap_map, hbb', ht]
    rfl

end AlgebraicGeometry.Scheme.Modules
