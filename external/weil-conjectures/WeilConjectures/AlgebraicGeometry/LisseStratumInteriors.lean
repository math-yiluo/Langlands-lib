/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-! Lissity on the union of the interiors of lisse strata. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Transport finite local constancy along a set-sheaf isomorphism. -/
private theorem finiteLisse_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
    (hF : IsFiniteLocallyConstantSheafOfTypes F) :
    IsFiniteLocallyConstantSheafOfTypes G := by
  obtain ⟨⟨𝒰, h𝒰⟩, hf⟩ := hF
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ?_⟩
  · have := h𝒰 i
    exact Sheaf.isConstant_congr _ ((X.smallEtaleTopology.overPullback _ _).mapIso e)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
      (hf.isFinitelyGenerated_sheafFiber Ω s)
    exact Finite.of_equiv _ (((pointSmallEtale s).sheafFiber.mapIso e).toEquiv)

/-- Lissity of an abelian restriction depends only on containment in an immersed image. -/
private theorem finiteLisse_of_range_subset {X Y Z : Scheme.{u}}
    (a : Y ⟶ X) (b : Z ⟶ X) [IsImmersion b]
    (hr : Set.range a ⊆ Set.range b)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hb : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Z.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} b).obj E))) :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E)) := by
  have : Surjective (Limits.pullback.fst a b) :=
    surjective_pullback_fst_of_range_subset a b hr
  have : IsClosedImmersion (Limits.pullback.fst a b) :=
    IsClosedImmersion.of_isImmersion_of_surjective _
  have hp := (pullback_finite_locally_constant (Limits.pullback.snd a b) b E hb).2
  rw [← Limits.pullback.condition] at hp
  let c := (Etale.upperStarComp AddCommGrpCat.{u + 1}
    (Limits.pullback.fst a b) a).app E
  have hp' := finiteLisse_of_iso
    ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso c) hp
  have hlc : IsLocallyConstantSheaf
      ((Etale.upperStar AddCommGrpCat.{u + 1} (Limits.pullback.fst a b)).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E)) :=
    ((finite_local_abelian_forget_iff _).mp hp').1
  have hfin := ((finite_local_abelian_forget_iff _).mp hp').2
  have hlocal : IsLocallyConstantSheaf ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E) :=
    IsLocallyConstantSheaf.of_upperStar (Limits.pullback.fst a b) _
  apply (finite_local_abelian_forget_iff _).mpr
  refine ⟨hlocal, ?_⟩
  intro Ω _ _ s
  obtain ⟨t, rfl⟩ := exists_comp_eq_of_surjective (Limits.pullback.fst a b) s
  have hfinite : Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} (Limits.pullback.fst a b)).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E))) := hfin Ω t
  exact @Finite.of_equiv _ _ hfinite
    ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (Limits.pullback.fst a b) t).app
        ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj E)).addCommGroupIsoToAddEquiv.toEquiv

/-- Finite set-stalk lissity on each stratum implies lissity on the union of their interiors.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof paragraphs 1--3 of
`lem-weil-pbc-finite-pushforward-generic-constructible`; the Zariski gluing argument
is also written in `WeilConjectures/ConstructibleSheaf/GenericConstancy.lean`.
(blueprint: lem-weil-pbc-lisse-stratum-interiors).

Proof: Cover the union W of the interiors by the open subschemes V_i = interior(T_i).
For each i form P_i = V_i x_Z T.domain i. The first projection is an immersion
and is surjective because the image of V_i is contained in the i-th stratum.
A surjective immersion is a closed immersion, hence a universal homeomorphism.
Pull back the lisse restriction on T.domain i along the second projection.
Composition of inverse images identifies the result with the restriction of
E to P_i. Universal-homeomorphism invariance of the etale site then descends
lissity to V_i: the site equivalence transports etale trivializations, and its
geometric points identify the finite stalks. The comparison of set inverse image
and underlying abelian inverse image justifies each use of the displayed set
restriction. This fibre-product argument does not assume that the map V_i -> Z
factors through the chosen scheme structure on the stratum.
The trivializing etale covers on all V_i compose with the open cover of W to
trivialize the restriction on W. Every geometric point of W lifts to a member
of this open cover, and inverse image identifies its stalk with that finite
stalk. Thus both local constancy and finite geometric stalks hold. When W is
empty, the empty etale covering trivializes the sheaf and the stalk condition
is vacuous. -/
theorem lisse_on_stratum_interiors
    {Z : Scheme.{u}} (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (T : Stratification Z)
    (hT : ∀ i : Fin T.n, IsFiniteLocallyConstantSheafOfTypes
      ((etaleSetPullback (T.immersion i)).obj
        ((sheafCompose Z.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose T.interiorUnion.toScheme.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} T.interiorUnion.ι).obj E)) := by
  classical
  have hstratum (i : Fin T.n) : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose (T.domain i).smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (T.immersion i)).obj E)) := by
    let e := (AlgebraicGeometry.etaleInverseImageAlgebraicStructures
      (T.domain i) Z (T.immersion i)).2.choose
    exact finiteLisse_of_iso (e.app E).symm (hT i)
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} T.interiorUnion.ι).obj E
  have hcover (i : ULift.{u} (Fin T.n)) : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose (T.interiorOpens i.down).toScheme.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (T.interiorUnionCover.f i)).obj G)) := by
    have hi : IsFiniteLocallyConstantSheafOfTypes
        ((sheafCompose (T.interiorOpens i.down).toScheme.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (T.interiorOpens i.down).ι).obj E)) := by
      apply finiteLisse_of_range_subset _ (T.immersion i.down) _ E (hstratum i.down)
      rw [Scheme.Opens.range_ι, T.range_immersion]
      exact interior_subset
    let e := eqToIso (congrArg (fun m ↦ (Etale.upperStar AddCommGrpCat.{u + 1} m).obj E)
      (Scheme.homOfLE_ι Z (le_iSup T.interiorOpens i.down)).symm) ≪≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1}
          (T.interiorUnionCover.f i) T.interiorUnion.ι).app E
    exact finiteLisse_of_iso
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e) hi
  have hlocal (i : ULift.{u} (Fin T.n)) :
      IsLocallyConstantSheaf
        ((Etale.upperStar AddCommGrpCat.{u + 1} (T.interiorUnionCover.f i)).obj G) :=
    ((finite_local_abelian_forget_iff _).mp (hcover i)).1
  apply (finite_local_abelian_forget_iff G).mpr
  refine ⟨?_, ?_⟩
  · let 𝒰 : Cover.{u} etalePrecoverage T.interiorUnion.toScheme :=
      T.interiorUnionCover.changeProp (Q := @Etale) fun _ ↦ inferInstance
    have : ∀ i : 𝒰.I₀,
        IsLocallyConstantSheaf ((Etale.upperStar AddCommGrpCat.{u + 1} (𝒰.f i)).obj G) :=
      hlocal
    exact IsLocallyConstantSheaf.of_cover 𝒰 G
  · intro Ω _ _ s
    obtain ⟨i, x, hx⟩ := T.interiorUnionCover.exists_eq (s (IsLocalRing.closedPoint _))
    obtain ⟨t, rfl⟩ := exists_comp_eq_of_mem_range (T.interiorUnionCover.f i) s ⟨x, hx⟩
    have hfinite : Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (T.interiorUnionCover.f i)).obj G)) :=
      ((finite_local_abelian_forget_iff _).mp (hcover i)).2 Ω t
    exact @Finite.of_equiv _ _ hfinite
      ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
        (T.interiorUnionCover.f i) t).app G).addCommGroupIsoToAddEquiv.toEquiv

end AlgebraicGeometry.Scheme
