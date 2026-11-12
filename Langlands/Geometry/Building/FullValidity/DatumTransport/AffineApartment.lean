import Langlands.Geometry.Building.FullValidity.DatumTransport.Building
import Langlands.Geometry.Building.FullValidity.AffineApartment
import Langlands.Geometry.Building.ValuationBuildingAffineApartmentTransport
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.CorepresentedComultiplication

/-!
# Axiom 4.1.4 under based group isomorphisms

The supplied splitting of Axiom 4.1.4 for `G` (derived subgroup `d : D → G`, torus `j : S' → D`
with `e : S' → S`, central torus `a : A_G → S`) is carried to `H` by keeping `D`, `S'`, `A_G`
and `j`, composing `d` with `f` and `e`, `a` with `σ`. Every clause of
`SatisfiesAffineApartmentAxiom` is preserved: the derived subgroup and split component are
invariant under `f`, the decomposition `V(S) = V(S') ⊕ V(A_G)` is carried by `V(σ)`, and the
normalizer `N(F)` and its actions on `S` and on `A(S)` are carried by `f` and `σ`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace DatumTransport

/-- Postcomposing a split component with an isomorphism gives a split component. -/
theorem isSplitComponent_comp_iso {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G}
    (hi : IsSplitComponent i) (e : G ≅ G') : IsSplitComponent (i ≫ e.hom) := by
  refine ⟨⟨(IsSplitSubtorus.comp_iso_iff i e).mpr hi.1.1, hi.1.2.comp_iso e⟩, ?_⟩
  intro A' i' hi' g hg
  apply hi.2 A' (i' ≫ e.inv)
    ⟨(IsSplitSubtorus.comp_iso_iff i' e.symm).mpr hi'.1, hi'.2.comp_iso e.symm⟩ g
  rw [← Category.assoc, hg, Category.assoc, e.hom_inv_id, Category.comp_id]

end DatumTransport

open DatumTransport

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : ValuationBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : B.S ≅ S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- The splitting of Axiom 4.1.4 for `H`: the same derived subgroup `D`, tori `S'` and `A_G` and
torus `j : S' → D`, with `d` composed with `f` and `e`, `a` composed with `σ`. -/
def ApartmentSplitting.basedTransport (T : B.ApartmentSplitting) :
    (B.basedTransport σ f h).ApartmentSplitting where
  D := T.D
  d := T.d ≫ f.hom
  derivedTorus := T.derivedTorus
  j := T.j
  e := T.e ≫ σ.hom
  centralTorus := T.centralTorus
  a := T.a ≫ σ.hom

omit [IsAffineHom H.X.hom] in
include h in
/-- The normalizing automorphism of `f(n)` on `S` is that of `n` conjugated by `σ`. -/
theorem normalizingAut_basedTransport (n : normalizerPoints B.i) :
    (normalizingAut j (normalizerPointsTransportEquiv σ f h n)).hom =
      σ.inv ≫ (normalizingAut B.i n).hom ≫ σ.hom := by
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  have hn := (isNormalizingPoint_normalizingAut B.i n).transport σ f h
  rw [(isNormalizingPoint_normalizingAut j (normalizerPointsTransportEquiv σ f h n)).unique j hn]
  rfl

/-- The comparison of apartments intertwines the actions of `N(F)` and of its image under `f`. -/
theorem normalizerAction_basedTransport (n : normalizerPoints B.i) (x : B.Apartment) :
    B.basedApartmentEquiv σ f h (B.normalizerAction n x) =
      (B.basedTransport σ f h).normalizerAction (normalizerPointsTransportEquiv σ f h n)
        (B.basedApartmentEquiv σ f h x) :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.apartmentTransportEquiv_smul σ f h n x

/-- KP Axiom 4.1.4 for `G` gives Axiom 4.1.4 for `H` with the transported splitting. -/
theorem SatisfiesAffineApartmentAxiom.basedTransport {T : B.ApartmentSplitting}
    (hT : B.SatisfiesAffineApartmentAxiom T) :
    (B.basedTransport σ f h).SatisfiesAffineApartmentAxiom (T.basedTransport B σ f h) where
  isDerivedSubgroup := hT.isDerivedSubgroup.comp_iso f
  isMaximalSplitTorus_j := hT.isMaximalSplitTorus_j
  isClosedSubgroup_e := by
    change IsClosedSubgroup (CommGroupScheme.groupHom T.e ≫ (torusGrpIso σ).hom)
    exact hT.isClosedSubgroup_e.comp (IsClosedSubgroup.of_iso (torusGrpIso σ))
  j_comp_d := by
    change T.j ≫ T.d ≫ f.hom = CommGroupScheme.groupHom (T.e ≫ σ.hom) ≫ j
    rw [← Category.assoc, hT.j_comp_d, Category.assoc, h]
    rfl
  isSplitComponent := by
    change IsSplitComponent (CommGroupScheme.groupHom (T.a ≫ σ.hom) ≫ j)
    have hc : CommGroupScheme.groupHom (T.a ≫ σ.hom) ≫ j =
        (CommGroupScheme.groupHom T.a ≫ B.i) ≫ f.hom := by
      rw [Category.assoc, h]
      rfl
    rw [hc]
    exact isSplitComponent_comp_iso hT.isSplitComponent f
  isCompl := by
    change IsCompl (LinearMap.range (cocharacterMapReal (T.e ≫ σ.hom)))
      (LinearMap.range (cocharacterMapReal (T.a ≫ σ.hom)))
    rw [range_cocharacterMapReal_comp_iso, range_cocharacterMapReal_comp_iso]
    exact (Submodule.orderIsoMapComap (cocharacterRealCongr σ)).isCompl hT.isCompl
  normalizer_derivedTorus := by
    intro n
    let N := normalizerPointsTransportEquiv σ f h
    obtain ⟨τ, hτ⟩ := hT.normalizer_derivedTorus (N.symm n)
    refine ⟨τ, ?_⟩
    change τ.hom ≫ (T.e ≫ σ.hom) = (T.e ≫ σ.hom) ≫ (normalizingAut j n).hom
    have hN := normalizingAut_basedTransport B σ f h (N.symm n)
    rw [show normalizerPointsTransportEquiv σ f h (N.symm n) = n from N.apply_symm_apply n] at hN
    rw [hN]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hτ]
  center_acts_trivially := by
    intro n hn
    let N := normalizerPointsTransportEquiv σ f h
    have hn' : ((N.symm n : normalizerPoints B.i) : rationalPoints G) ∈
        (center G).carrier (Over.mk (𝟙 _)) := by
      apply (mem_center_comp_iso_iff f _).1
      have he : ((N.symm n : normalizerPoints B.i) : rationalPoints G) ≫ f.hom.hom.hom =
          (n : rationalPoints H) :=
        map_hom_map_inv f n
      rw [he]
      exact hn
    have hc := hT.center_acts_trivially (N.symm n) hn'
    apply AffineEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := (B.basedApartmentEquiv σ f h).surjective y
    have hy := normalizerAction_basedTransport B σ f h (N.symm n) x
    rw [show normalizerPointsTransportEquiv σ f h (N.symm n) = n from N.apply_symm_apply n,
      hc] at hy
    simpa only [AffineEquiv.coe_one, id_eq] using hy.symm
  affineConjugations := (B.basedTransport σ f h).hasAffineConjugations

end ValuationBuildingData

end Langlands.Geometry.Building
