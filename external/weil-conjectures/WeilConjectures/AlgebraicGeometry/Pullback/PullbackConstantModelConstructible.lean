/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarMatrixInverseImage
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPresentationCokernel
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback

/-!
# Pullback of constructible modules with finite constant scalar models

Inverse image along a morphism of schemes preserves constructible modules together with their
specified finite constant scalar models.

## References

* Stacks Project, Tag 054I
* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.3.8

## Implementation details

The statement retains each given scalar module and the whole given covering family; the
pulled-back stratification and covers are the existing canonical constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pull back the given constructible locally closed subschemes, keeping their scheme
structures. The input uses the recorded finite locally closed stratification interface;
constructibility is supplied separately. The output includes constructibility, local
closedness, disjointness and the covering property, and has the same finite index set.
Its domains are `pullback (S.immersion a) g`, its immersions are `pullback.snd`, and its
stratum subsets are `g ⁻¹' S.stratum a`. -/
def constantModelPullbackStratification {Y Y' : Scheme.{u}}
    (S : Y.FiniteLocallyClosedStratification)
    (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) (g : Y' ⟶ Y) :
    Y'.Stratification :=
  Scheme.Stratification.pullback
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      isConstructible_stratum := hS
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion } g

/-- The given scalar module is a constant model of the twice restricted module.
This predicate names the repeated expression without changing its isomorphism data. -/
def HasScalarModelOnRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V X Y : Scheme.{u}}
    (v : V ⟶ X) (s : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ)) : Prop :=
  Nonempty ((CondensedRing.upperStar Λ v).obj ((CondensedRing.upperStar Λ s).obj M) ≅
    (finiteConstantScalarExtension Λ V).obj P)

/-- The two clauses of preservation: constructibility, and the same finite scalar models
on the base changes of any specified witnessing stratification and covers. The scalar
modules are quantified before pullback and occur unchanged on the right of each output
isomorphism. `pullback₂` retains the cover's index type and has members
`U_i ×_{Y_a} (Y_a ×_Y Y')`, with the second projection as covering map. -/
def ConstantModelPullbackStatement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : Prop :=
  ∀ {Y Y' : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] (g : Y' ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((CondensedRing.upperStar Λ g).obj M) ∧
      ∀ (S : Y.FiniteLocallyClosedStratification)
        (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
        (U : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
        (P : ∀ (a : Fin S.n) (_ : (U a).I₀), Mod Ab.{u + 1} (scalarRingObj Λ)),
        (∀ (a : Fin S.n) (i : (U a).I₀),
          Mod.IsFinitelyPresented (scalarRingObj Λ) (P a i)) →
        (∀ (a : Fin S.n) (i : (U a).I₀),
          HasScalarModelOnRestriction Λ ((U a).f i) (S.immersion a) M (P a i)) →
        ∀ (a : Fin S.n) (i : (U a).I₀),
          HasScalarModelOnRestriction Λ
            (((U a).pullback₂ (pullback.fst (S.immersion a) g)).f i)
            ((constantModelPullbackStratification S hS g).immersion a)
            ((CondensedRing.upperStar Λ g).obj M) (P a i)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension
  CondensedRing.upperStarComp upperStarFromPoint
  scalarSections scalarConstant scalarCoefficientHom

private theorem finiteScalarModel_cokernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P) :
    ∃ (m n : ℕ) (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)),
      ∀ X : Scheme.{u}, Nonempty ((finiteConstantScalarExtension Λ X).obj P ≅
        cokernel (scalarMatrix Λ X A)) := by
  obtain ⟨n, m, f, ⟨ef⟩⟩ := hP
  let A (j : Fin m) (k : Fin n) : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ :=
    (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
      (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom
  have hf : (biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)) = f := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    erw [biproduct.ι_matrix, biproduct.lift_π]
    apply Mod.regular_hom_ext
    simpa only [A, Category.assoc] using
      Mod.one_comp_regularLift (A := scalarRingObj Λ) _ _
  refine ⟨m, n, A, fun X ↦ ?_⟩
  let a := biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)
  obtain ⟨_, _, _, _, _, c, _⟩ := scalar_presentation_cokernel Λ X m n A
    (cokernel a) (cokernel.π a) (cokernel.condition a) (cokernelIsCokernel a)
  exact ⟨(finiteConstantScalarExtension Λ X).mapIso
    (ef ≪≫ cokernel.mapIso f a (Iso.refl _) (Iso.refl _) (by simp only [a, hf,
      Iso.refl_hom, Category.comp_id, Category.id_comp])) ≪≫ c⟩

private theorem finiteScalarModel_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V U : Scheme.{u}} (h : V ⟶ U)
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P) :
    Nonempty ((CondensedRing.upperStar Λ h).obj
      ((finiteConstantScalarExtension Λ U).obj P) ≅
        (finiteConstantScalarExtension Λ V).obj P) := by
  obtain ⟨m, n, A, he⟩ := finiteScalarModel_cokernel Λ P hP
  obtain ⟨eU⟩ := he U
  obtain ⟨eV⟩ := he V
  obtain ⟨ec, _⟩ := (scalarMatrix_inverseImage Λ h A).2
  exact ⟨(CondensedRing.upperStar Λ h).mapIso eU ≪≫ ec ≪≫ eV.symm⟩

private theorem restrictionSquareIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V X X' Y : Scheme.{u}}
    (a : V ⟶ X') (b : X' ⟶ Y) (c : V ⟶ X) (d : X ⟶ Y)
    (hc : a ≫ b = c ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Nonempty ((CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ b).obj M) ≅
      (CondensedRing.upperStar Λ c).obj ((CondensedRing.upperStar Λ d).obj M)) := by
  exact ⟨((CondensedRing.upperStarComp Λ a b).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) hc) ≪≫
    (CondensedRing.upperStarComp Λ c d).app M⟩

private theorem iteratedModel_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V U X X' Y Y' : Scheme.{u}}
    (v : V ⟶ X') (t : X' ⟶ X) (h : V ⟶ U) (u : U ⟶ X)
    (b : X' ⟶ Y') (s : X ⟶ Y) (g : Y' ⟶ Y)
    (ht : v ≫ t = h ≫ u) (hs : b ≫ g = t ≫ s)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P)
    (e : HasScalarModelOnRestriction Λ u s M P) :
    HasScalarModelOnRestriction Λ v b ((CondensedRing.upperStar Λ g).obj M) P := by
  obtain ⟨e⟩ := e
  obtain ⟨e₁⟩ := restrictionSquareIso Λ b g t s hs M
  obtain ⟨e₂⟩ := restrictionSquareIso Λ v t h u ht
    ((CondensedRing.upperStar Λ s).obj M)
  obtain ⟨eP⟩ := finiteScalarModel_pullback Λ h P hP
  exact ⟨(CondensedRing.upperStar Λ v).mapIso e₁ ≪≫ e₂ ≪≫
    (CondensedRing.upperStar Λ h).mapIso e ≪≫ eP⟩

private theorem coverModel_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}}
    (s : X ⟶ Y) (g : Y' ⟶ Y)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (i : U.I₀)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P)
    (e : HasScalarModelOnRestriction Λ (U.f i) s M P) :
    HasScalarModelOnRestriction Λ
      ((U.pullback₂ (pullback.fst s g)).f i) (pullback.snd s g)
      ((CondensedRing.upperStar Λ g).obj M) P := by
  exact iteratedModel_pullback Λ ((U.pullback₂ (pullback.fst s g)).f i)
    (pullback.fst s g) (pullback.fst (U.f i) (pullback.fst s g)) (U.f i)
    (pullback.snd s g) s g pullback.condition.symm pullback.condition.symm M P hP e

private theorem constantModelPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : ConstantModelPullbackStatement Λ := by
  classical
  intro Y Y' _ _ _ _ g M hM
  constructor
  · exact pullback_constructible Λ g M hM
  · intro S hS U P hP eP a i
    exact coverModel_pullback Λ (S.immersion a) g (U a) i M (P a i) (hP a i) (eP a i)

/-- Inverse image preserves constructible modules and their specified constant models, for
every commutative condensed coefficient ring (in particular finite discrete rings, the ℓ-adic
integers and numbers, their finite extensions, and the condensed algebraic closure). -/
theorem pullback_constantModelConstructible
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj L)] :
    ConstantModelPullbackStatement ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj L) := by
  intro Y Y' _ _ _ _ g M hM
  exact constantModelPullback _ g M hM

end AlgebraicGeometry.ProEtale
