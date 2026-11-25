/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Topology.StratificationDense

/-!
# Generic constancy of constructible sheaves

Local constancy is étale local (`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_cover`:
the trivialising covers of the restrictions to the members of an étale cover compose to a
trivialising cover), and finiteness of the stalks is Zariski local
(`IsFiniteSheaf.of_openCover`: a geometric point lifts to a member of an open cover
containing its image, and the stalk of the restriction at the lift is the stalk), so finite
local constancy is Zariski local (`IsFiniteLocallyConstantSheaf.of_openCover`).

Consequently a constructible sheaf `F` on `X` is finite locally constant on a dense open
subscheme (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_dense_open`): the union `U` of
the interiors of the strata of a witnessing stratification is dense
(`Topology.Stratification.dense_iUnion_interior_stratum`), and on the open `interior Xᵢ` of
`U` the sheaf `F|_U` is the pullback of `F` along a morphism with image in `Xᵢ`, hence finite
locally constant by the independence of the scheme structure. No Noetherian hypothesis is
needed. (blueprint: `prop-constructible-generic-constancy`)

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

instance : etalePrecoverage.{u}.IsStableUnderComposition :=
  inferInstanceAs (precoverage @Etale).IsStableUnderComposition

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- **Local constancy is étale local**: if the pullbacks of `G` to the members of an étale
cover are locally constant, so is `G`. -/
theorem IsLocallyConstantSheaf.of_cover (𝒰 : Cover.{u} etalePrecoverage X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsLocallyConstantSheaf G := by
  have hV (i : 𝒰.I₀) : Nonempty (LocallyConstantDatum ((Etale.upperStar A (𝒰.f i)).obj G)) :=
    IsLocallyConstantSheaf.nonempty_locallyConstantDatum
  have 𝒱 := fun i ↦ (hV i).some
  refine ⟨⟨⟨𝒰.bind fun i ↦ (𝒱 i).cover, fun ⟨i, j⟩ ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  have h₁ := (isConstant_over_iff_upperStar A ((𝒱 i).cover.etalePrecoverageToEtale j) _).mp
    ((𝒱 i).isConstant j)
  have h₂ : ((Etale.upperStar A (𝒰.f i) ⋙ Etale.upperStar A ((𝒱 i).cover.f j)).obj G).IsConstant
      (Cover.etalePrecoverageToEtale (𝒰.bind fun i ↦ (𝒱 i).cover) ⟨i, j⟩).left.smallEtaleTopology :=
    h₁
  exact Sheaf.isConstant_congr _
    ((Etale.upperStarComp A ((𝒱 i).cover.f j) (𝒰.f i)).app G).symm

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

omit [HasSmallSiteSheafify A] in
/-- **Finiteness is Zariski local**: if the pullbacks of `G` to the members of an open cover
are finite, so is `G`. -/
theorem IsFiniteSheaf.of_openCover (𝒰 : OpenCover.{u} X) (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] : IsFiniteSheaf G where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s (IsLocalRing.closedPoint _))
    obtain ⟨s', rfl⟩ := exists_comp_eq_of_mem_range (𝒰.f i) s ⟨x, hx⟩
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (𝒰.f i)).obj G) Ω s').of_iso
      ((Etale.upperStarCompSheafFiberIso A (𝒰.f i) s').app G)

/-- **Finite local constancy is Zariski local**: if the pullbacks of `G` to the members of
an open cover are finite locally constant, so is `G`. -/
theorem IsFiniteLocallyConstantSheaf.of_openCover (𝒰 : OpenCover.{u} X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsFiniteLocallyConstantSheaf G where
  toIsLocallyConstantSheaf := by
    let 𝒱 : Cover.{u} etalePrecoverage X := 𝒰.changeProp (Q := @Etale) fun _ ↦ inferInstance
    have : ∀ i, IsLocallyConstantSheaf ((Etale.upperStar A (𝒱.f i)).obj G) := fun i ↦
      inferInstanceAs (IsLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G))
    exact IsLocallyConstantSheaf.of_cover 𝒱 G
  toIsFiniteSheaf := IsFiniteSheaf.of_openCover 𝒰 G

end Finite

section Generic

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The open subscheme of `X` given by the interior of a stratum. -/
def Stratification.interiorOpens (S : Stratification X) (i : Fin S.n) : X.Opens :=
  ⟨interior (S.stratum i), isOpen_interior⟩

/-- The union of the interiors of the strata, as an open subscheme of `X`. -/
def Stratification.interiorUnion (S : Stratification X) : X.Opens :=
  ⨆ i, S.interiorOpens i

/-- The union of the interiors of the strata is dense. -/
lemma Stratification.dense_interiorUnion (S : Stratification X) :
    Dense (S.interiorUnion : Set X) := by
  rw [Stratification.interiorUnion, TopologicalSpace.Opens.coe_iSup]
  exact S.dense_iUnion_interior_stratum

/-- The open cover of the union of the interiors of the strata by the interiors. -/
def Stratification.interiorUnionCover (S : Stratification X) :
    OpenCover.{u} S.interiorUnion.toScheme where
  I₀ := ULift.{u} (Fin S.n)
  X i := S.interiorOpens i.down
  f i := X.homOfLE (le_iSup S.interiorOpens i.down)
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup (s := S.interiorOpens)).mp x.2
    exact ⟨⟨i⟩, ⟨x.1, hi⟩, Subtype.ext (Scheme.homOfLE_apply (le_iSup S.interiorOpens i) _)⟩

/-- **Generic constancy**: a constructible sheaf is finite locally constant on a dense open
subscheme, the union of the interiors of the strata of a witnessing stratification.
(blueprint: `prop-constructible-generic-constancy`) -/
theorem IsConstructibleSheaf.exists_dense_open (F : Sheaf X.smallEtaleTopology A)
    [IsConstructibleSheaf F] :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsFiniteLocallyConstantSheaf ((Etale.upperStar A U.ι).obj F) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  refine ⟨S.interiorUnion, S.dense_interiorUnion, ?_⟩
  have h (i : ULift.{u} (Fin S.n)) : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar A (S.interiorUnionCover.f i)).obj
        ((Etale.upperStar A S.interiorUnion.ι).obj F)) := by
    have := hS i.down
    have h' : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar A (S.interiorOpens i.down).ι).obj F) := by
      refine IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ (S.immersion i.down) ?_ F
      rw [Scheme.Opens.range_ι, S.range_immersion]
      exact interior_subset
    refine IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar A (S.interiorOpens i.down).ι).obj F) ?_
    exact eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj F)
      (Scheme.homOfLE_ι X (le_iSup S.interiorOpens i.down)).symm) ≪≫
      (Etale.upperStarComp A (S.interiorUnionCover.f i) S.interiorUnion.ι).app F
  exact IsFiniteLocallyConstantSheaf.of_openCover S.interiorUnionCover _

end Generic

end AlgebraicGeometry.Scheme

end
