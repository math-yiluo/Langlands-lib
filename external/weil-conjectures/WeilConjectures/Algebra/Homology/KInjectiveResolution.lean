/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# K-injective resolutions

A *K-injective resolution* of a cochain complex `K` is a quasi-isomorphism `ι : K ⟶ I` to a
K-injective complex `I`, i.e. a complex such that every map from an acyclic complex to `I` is
null-homotopic (`CochainComplex.IsKInjective`). Every bounded below complex in an abelian
category with enough injectives (for instance a Grothendieck abelian category) has a K-injective
resolution, given by a bounded below complex of injectives.

Two K-injective resolutions of the same complex are homotopy equivalent under `K`, by a homotopy
equivalence which is unique up to homotopy. Consequently, for an additive functor `v`, the
complex `Rv(K) = v(I)` is well defined up to canonical isomorphism in the homotopy category, and
it is functorial in `K`. An injective resolution `X ⟶ I•` of an object `X` gives a K-injective
resolution of `X[0]`, and `Hᵖ(Rv(X[0])) ≅ Rᵖv(X)`; shifting a K-injective resolution of `K`
gives a K-injective resolution of `K[n]`, so that `Rv(K[n]) ≅ Rv(K)[n]`.

## Main definitions

- `CochainComplex.KInjectiveResolution`: K-injective resolutions.
- `CochainComplex.KInjectiveResolution.lift`: maps to K-injective complexes extend along
  K-injective resolutions, uniquely up to homotopy.
- `CochainComplex.KInjectiveResolution.homotopyEquiv`: the homotopy equivalence between two
  K-injective resolutions of the same complex.
- `CochainComplex.KInjectiveResolution.rightDerived`: the complex `Rv(K) = v(I)` in the homotopy
  category, and `CochainComplex.KInjectiveResolution.rightDerivedIso`,
  `CochainComplex.KInjectiveResolution.rightDerivedMap`: its independence of the resolution and
  its functoriality.
- `InjectiveResolution.kInjectiveResolution`: the K-injective resolution of `X[0]` given by an
  injective resolution of `X`.
- `CochainComplex.KInjectiveResolution.shift`: the shift of a K-injective resolution.

## Main statements

- `CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE`,
  `CochainComplex.KInjectiveResolution.nonempty_of_isGE`: existence for bounded below complexes.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A **K-injective resolution** of a cochain complex `K`: a quasi-isomorphism `ι : K ⟶ I` to a
K-injective complex `I`.

(blueprint: `def-sp-kinjective-bridge`) -/
structure KInjectiveResolution (K : CochainComplex C ℤ) where
  /-- The K-injective complex `I`. -/
  I : CochainComplex C ℤ
  /-- The quasi-isomorphism `K ⟶ I`. -/
  ι : K ⟶ I
  quasiIso_ι : QuasiIso ι := by infer_instance
  isKInjective : I.IsKInjective := by infer_instance

attribute [instance] KInjectiveResolution.quasiIso_ι KInjectiveResolution.isKInjective

open HomotopyCategory in
/-- If `s : K ⟶ L` is a quasi-isomorphism and `J` is K-injective, precomposition with `s` is a
bijection between morphisms `L ⟶ J` and `K ⟶ J` in the homotopy category. -/
lemma IsKInjective.bijective_quotient_map_comp {K L J : CochainComplex C ℤ} (s : K ⟶ L)
    [QuasiIso s] [J.IsKInjective] :
    Function.Bijective (fun (φ : (quotient C (.up ℤ)).obj L ⟶ (quotient C (.up ℤ)).obj J) ↦
      (quotient C (.up ℤ)).map s ≫ φ) := by
  let := HasDerivedCategory.standard C
  have : IsIso (DerivedCategory.Qh.map ((quotient C (.up ℤ)).map s)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  refine ⟨fun φ₁ φ₂ hφ ↦ ?_, fun ψ ↦ ?_⟩
  · apply (IsKInjective.Qh_map_bijective _ J).1
    rw [← cancel_epi (DerivedCategory.Qh.map ((quotient C (.up ℤ)).map s)), ← Functor.map_comp,
      ← Functor.map_comp]
    exact congrArg _ hφ
  · obtain ⟨φ, hφ⟩ := (IsKInjective.Qh_map_bijective _ J).2
      (inv (DerivedCategory.Qh.map ((quotient C (.up ℤ)).map s)) ≫ DerivedCategory.Qh.map ψ)
    refine ⟨φ, (IsKInjective.Qh_map_bijective _ J).1 ?_⟩
    dsimp
    rw [Functor.map_comp, hφ, IsIso.hom_inv_id_assoc]

namespace KInjectiveResolution

variable {K : CochainComplex C ℤ} (R : K.KInjectiveResolution)

/-- A morphism to a K-injective complex extends along a K-injective resolution, up to homotopy. -/
lemma exists_lift {J : CochainComplex C ℤ} [J.IsKInjective] (ψ : K ⟶ J) :
    ∃ φ : R.I ⟶ J, (HomotopyCategory.quotient C (.up ℤ)).map (R.ι ≫ φ) =
      (HomotopyCategory.quotient C (.up ℤ)).map ψ := by
  obtain ⟨φ, hφ⟩ := (IsKInjective.bijective_quotient_map_comp (J := J) R.ι).2
    ((HomotopyCategory.quotient C (.up ℤ)).map ψ)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective φ
  exact ⟨φ, by rw [Functor.map_comp]; exact hφ⟩

/-- A morphism `ψ : K ⟶ J` to a K-injective complex extends along a K-injective resolution
`K ⟶ I` to a morphism `I ⟶ J`, unique up to homotopy (`KInjectiveResolution.liftHomotopy`,
`KInjectiveResolution.homotopyOfComp`). -/
noncomputable def lift {J : CochainComplex C ℤ} [J.IsKInjective] (ψ : K ⟶ J) : R.I ⟶ J :=
  (R.exists_lift ψ).choose

/-- The extension `R.lift ψ` of `ψ` along `R.ι` is compatible with `ψ` up to homotopy. -/
noncomputable def liftHomotopy {J : CochainComplex C ℤ} [J.IsKInjective] (ψ : K ⟶ J) :
    Homotopy (R.ι ≫ R.lift ψ) ψ :=
  HomotopyCategory.homotopyOfEq _ _ (R.exists_lift ψ).choose_spec

/-- Two morphisms `I ⟶ J` to a K-injective complex which agree in the homotopy category after
composition with `K ⟶ I` agree in the homotopy category. -/
lemma quotient_map_eq_of_comp {J : CochainComplex C ℤ} [J.IsKInjective] (φ₁ φ₂ : R.I ⟶ J)
    (h : (HomotopyCategory.quotient C (.up ℤ)).map (R.ι ≫ φ₁) =
      (HomotopyCategory.quotient C (.up ℤ)).map (R.ι ≫ φ₂)) :
    (HomotopyCategory.quotient C (.up ℤ)).map φ₁ =
      (HomotopyCategory.quotient C (.up ℤ)).map φ₂ := by
  apply (IsKInjective.bijective_quotient_map_comp (J := J) R.ι).1
  simpa only [Functor.map_comp] using h

/-- Two morphisms `I ⟶ J` to a K-injective complex which agree up to homotopy on `K` are
homotopic. -/
noncomputable def homotopyOfComp {J : CochainComplex C ℤ} [J.IsKInjective] (φ₁ φ₂ : R.I ⟶ J)
    (h : Homotopy (R.ι ≫ φ₁) (R.ι ≫ φ₂)) : Homotopy φ₁ φ₂ :=
  HomotopyCategory.homotopyOfEq _ _
    (R.quotient_map_eq_of_comp φ₁ φ₂ (HomotopyCategory.eq_of_homotopy _ _ h))

variable (R' : K.KInjectiveResolution)

/-- **Uniqueness of K-injective resolutions.** Two K-injective resolutions `K ⟶ I` and `K ⟶ I'`
of the same complex are homotopy equivalent, by a homotopy equivalence compatible with the maps
from `K` up to homotopy (`KInjectiveResolution.homotopyEquivHomotopy`); it is unique up to
homotopy (`KInjectiveResolution.homotopyEquivUnique`).

(blueprint: `lem-sp-kinjective-computes`) -/
noncomputable def homotopyEquiv : HomotopyEquiv R.I R'.I where
  hom := R.lift R'.ι
  inv := R'.lift R.ι
  homotopyHomInvId := R.homotopyOfComp _ _ ((Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    (((R.liftHomotopy R'.ι).compRight _).trans
      ((R'.liftHomotopy R.ι).trans (Homotopy.ofEq (Category.comp_id _).symm))))
  homotopyInvHomId := R'.homotopyOfComp _ _ ((Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    (((R'.liftHomotopy R.ι).compRight _).trans
      ((R.liftHomotopy R'.ι).trans (Homotopy.ofEq (Category.comp_id _).symm))))

/-- The homotopy equivalence between two K-injective resolutions is compatible with the maps
from `K` up to homotopy. -/
noncomputable def homotopyEquivHomotopy : Homotopy (R.ι ≫ (R.homotopyEquiv R').hom) R'.ι :=
  R.liftHomotopy R'.ι

/-- A morphism between two K-injective resolutions of `K` which is compatible with the maps
from `K` up to homotopy is homotopic to the homotopy equivalence
`KInjectiveResolution.homotopyEquiv`. -/
noncomputable def homotopyEquivUnique (φ : R.I ⟶ R'.I) (h : Homotopy (R.ι ≫ φ) R'.ι) :
    Homotopy φ (R.homotopyEquiv R').hom :=
  R.homotopyOfComp _ _ (h.trans (R.homotopyEquivHomotopy R').symm)

section Functoriality

variable {L : CochainComplex C ℤ} (S : L.KInjectiveResolution)

/-- The morphism `R.I ⟶ S.I` between K-injective resolutions induced by a morphism
`φ : K ⟶ L`. -/
noncomputable def map (φ : K ⟶ L) : R.I ⟶ S.I := R.lift (φ ≫ S.ι)

/-- The morphism `R.map S φ` is compatible with `φ` up to homotopy. -/
noncomputable def mapHomotopy (φ : K ⟶ L) : Homotopy (R.ι ≫ R.map S φ) (φ ≫ S.ι) :=
  R.liftHomotopy _

/-- The morphism `R.map R (𝟙 K)` is the identity in the homotopy category. -/
lemma quotient_map_map_id :
    (HomotopyCategory.quotient C (.up ℤ)).map (R.map R (𝟙 K)) = 𝟙 _ := by
  rw [← (HomotopyCategory.quotient C (.up ℤ)).map_id]
  exact HomotopyCategory.eq_of_homotopy _ _ (R.homotopyOfComp _ _
    ((R.mapHomotopy R (𝟙 K)).trans (Homotopy.ofEq (by simp))))

/-- The morphisms `R.map S φ` are compatible with composition in the homotopy category. -/
lemma quotient_map_map_comp {M : CochainComplex C ℤ} (T : M.KInjectiveResolution)
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    (HomotopyCategory.quotient C (.up ℤ)).map (R.map T (φ ≫ ψ)) =
      (HomotopyCategory.quotient C (.up ℤ)).map (R.map S φ ≫ S.map T ψ) := by
  refine HomotopyCategory.eq_of_homotopy _ _ (R.homotopyOfComp _ _ ?_)
  refine (R.mapHomotopy T (φ ≫ ψ)).trans ?_
  refine (Homotopy.ofEq (Category.assoc _ _ _)).trans ?_
  refine (((S.mapHomotopy T ψ).compLeft φ).symm.trans ?_)
  refine (Homotopy.ofEq (Category.assoc _ _ _).symm).trans ?_
  refine (((R.mapHomotopy S φ).symm.compRight _).trans ?_)
  exact Homotopy.ofEq (Category.assoc _ _ _)


end Functoriality

section RightDerived

variable {L : CochainComplex C ℤ} (S : L.KInjectiveResolution)
  {D : Type*} [Category* D] [Abelian D] (v : C ⥤ D) [v.Additive]

/-- The complex `Rv(K) = v(I)`, in the homotopy category, computed from a K-injective resolution
`K ⟶ I`.

(blueprint: `def-sp-kinjective-bridge`) -/
noncomputable def rightDerived : HomotopyCategory D (.up ℤ) :=
  (HomotopyCategory.quotient D (.up ℤ)).obj ((v.mapHomologicalComplex _).obj R.I)

/-- The cohomology `Rᵖv(K) = Hᵖ(Rv(K))` computed from a K-injective resolution.

(blueprint: `def-sp-kinjective-bridge`) -/
noncomputable def rightDerivedHomology (p : ℤ) : D :=
  ((v.mapHomologicalComplex _).obj R.I).homology p

/-- **`Rv(K)` does not depend on the K-injective resolution**: two K-injective resolutions give
canonically isomorphic complexes `v(I) ≅ v(I')` in the homotopy category.

(blueprint: `lem-sp-kinjective-computes`) -/
noncomputable def rightDerivedIso : R.rightDerived v ≅ R'.rightDerived v :=
  HomotopyCategory.isoOfHomotopyEquiv (v.mapHomotopyEquiv (R.homotopyEquiv R'))

/-- The cohomology `Rᵖv(K)` does not depend on the K-injective resolution. -/
noncomputable def rightDerivedHomologyIso (p : ℤ) :
    R.rightDerivedHomology v p ≅ R'.rightDerivedHomology v p :=
  (HomotopyCategory.homologyFunctorFactors D (.up ℤ) p).symm.app _ ≪≫
    (HomotopyCategory.homologyFunctor D (.up ℤ) p).mapIso (R.rightDerivedIso R' v) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (.up ℤ) p).app _


/-- **Functoriality of `Rv`**: the morphism `Rv(K) ⟶ Rv(L)` induced by a morphism `K ⟶ L`.

(blueprint: `lem-sp-kinjective-computes`) -/
noncomputable def rightDerivedMap (φ : K ⟶ L) : R.rightDerived v ⟶ S.rightDerived v :=
  (HomotopyCategory.quotient D (.up ℤ)).map ((v.mapHomologicalComplex _).map (R.map S φ))

/-- An additive functor preserves equalities in the homotopy category. -/
lemma quotient_map_mapHomologicalComplex_map {I J : CochainComplex C ℤ} (φ₁ φ₂ : I ⟶ J)
    (h : (HomotopyCategory.quotient C (.up ℤ)).map φ₁ =
      (HomotopyCategory.quotient C (.up ℤ)).map φ₂) :
    (HomotopyCategory.quotient D (.up ℤ)).map ((v.mapHomologicalComplex _).map φ₁) =
      (HomotopyCategory.quotient D (.up ℤ)).map ((v.mapHomologicalComplex _).map φ₂) :=
  HomotopyCategory.eq_of_homotopy _ _ (v.mapHomotopy (HomotopyCategory.homotopyOfEq _ _ h))

/-- Functoriality of `Rv`: identities. -/
@[simp]
lemma rightDerivedMap_id : R.rightDerivedMap R v (𝟙 K) = 𝟙 _ := by
  rw [rightDerivedMap, quotient_map_mapHomologicalComplex_map v _ (𝟙 _)
    (by rw [quotient_map_map_id, CategoryTheory.Functor.map_id])]
  simp [rightDerived]

/-- Functoriality of `Rv`: composition. -/
lemma rightDerivedMap_comp {M : CochainComplex C ℤ} (T : M.KInjectiveResolution)
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    R.rightDerivedMap T v (φ ≫ ψ) = R.rightDerivedMap S v φ ≫ S.rightDerivedMap T v ψ := by
  rw [rightDerivedMap, quotient_map_mapHomologicalComplex_map v _ _
    (R.quotient_map_map_comp S T φ ψ), Functor.map_comp, Functor.map_comp]
  rfl

/-- The isomorphism `Rv(K) ≅ Rv(K)` between the complexes computed from two K-injective
resolutions of `K` is the map induced by the identity of `K`. -/
lemma rightDerivedIso_hom : (R.rightDerivedIso R' v).hom = R.rightDerivedMap R' v (𝟙 K) := by
  refine quotient_map_mapHomologicalComplex_map v _ _ (HomotopyCategory.eq_of_homotopy _ _ ?_)
  exact (R.homotopyEquivUnique R' _ ((R.mapHomotopy R' (𝟙 K)).trans
    (Homotopy.ofEq (Category.id_comp _)))).symm


end RightDerived

section Existence

/-- **Existence of K-injective resolutions.** In an abelian category with enough injectives
(e.g. a Grothendieck abelian category), a complex `K` concentrated in degrees `≥ n` has a
K-injective resolution by a complex of injective objects concentrated in degrees `≥ n`.

(blueprint: `def-sp-kinjective-bridge`) -/
lemma exists_of_isStrictlyGE [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsStrictlyGE n] :
    ∃ R : K.KInjectiveResolution, R.I.IsStrictlyGE n ∧ ∀ i, Injective (R.I.X i) := by
  obtain ⟨L, i, _, hL, _⟩ := Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  have := isKInjective_of_injective L n
  exact ⟨⟨L, i, inferInstance, inferInstance⟩, inferInstance, hL⟩

/-- **Existence of K-injective resolutions.** In an abelian category with enough injectives
(e.g. a Grothendieck abelian category), every cohomologically bounded below complex has a
K-injective resolution.

(blueprint: `def-sp-kinjective-bridge`) -/
lemma nonempty_of_isGE [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    Nonempty K.KInjectiveResolution := by
  obtain ⟨R, -, -⟩ := exists_of_isStrictlyGE (K.truncGE n) n
  exact ⟨⟨R.I, K.πTruncGE n ≫ R.ι, inferInstance, inferInstance⟩⟩

/-- A chosen K-injective resolution of a cohomologically bounded below complex. -/
noncomputable def ofIsGE [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    K.KInjectiveResolution :=
  (nonempty_of_isGE K n).some

end Existence

section Shift

/-- **Shifts of K-injective resolutions.** If `K ⟶ I` is a K-injective resolution, then
`K[n] ⟶ I[n]` is a K-injective resolution.

(blueprint: `lem-sp-kinjective-computes`) -/
@[simps]
noncomputable def shift (n : ℤ) : (K⟦n⟧).KInjectiveResolution where
  I := R.I⟦n⟧
  ι := R.ι⟦n⟧'

variable {D : Type*} [Category* D] [Abelian D] (v : C ⥤ D) [v.Additive]

/-- **`Rv` commutes with shifts**: `Rv(K[n]) ≅ Rv(K)[n]`, computed from the shifted
resolution.

(blueprint: `lem-sp-kinjective-computes`) -/
noncomputable def rightDerivedShiftIso (n : ℤ) :
    (R.shift n).rightDerived v ≅ (R.rightDerived v)⟦n⟧ :=
  (HomotopyCategory.quotient D (.up ℤ)).mapIso
      (((v.mapHomologicalComplex (.up ℤ)).commShiftIso n).app R.I) ≪≫
    ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso n).app _

/-- **`Rv` commutes with shifts**: for any K-injective resolution `S` of `K[n]`,
`Rv(K[n]) ≅ Rv(K)[n]`.

(blueprint: `lem-sp-kinjective-computes`) -/
noncomputable def rightDerivedShiftIso' (n : ℤ) (S : (K⟦n⟧).KInjectiveResolution) :
    S.rightDerived v ≅ (R.rightDerived v)⟦n⟧ :=
  S.rightDerivedIso (R.shift n) v ≪≫ R.rightDerivedShiftIso v n

end Shift

end KInjectiveResolution

end CochainComplex

namespace CategoryTheory.InjectiveResolution

open CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {X : C} (R : InjectiveResolution X)

/-- A bounded below complex of injectives is K-injective: the `ℤ`-indexed complex of an
injective resolution is K-injective (`CochainComplex.isKInjective_of_injective`).

(blueprint: `lem-sp-kinjective-computes`) -/
instance : R.cochainComplex.IsKInjective := isKInjective_of_injective _ 0

/-- **An injective resolution `X ⟶ I•` is a K-injective resolution of `X[0]`.**

(blueprint: `lem-sp-kinjective-computes`) -/
@[simps]
noncomputable def kInjectiveResolution :
    ((CochainComplex.singleFunctor C 0).obj X).KInjectiveResolution where
  I := R.cochainComplex
  ι := R.ι'

end CategoryTheory.InjectiveResolution
