/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.SingleComplexInheritedTensorCondition
import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectPullbackComparison
import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided

/-! # Tor-independent base change for a perfect tensor factor

Source: Stacks Project, perfect.tex, single-complex base change (Tags 0DJ9, 0DJA)
and the Tor-independent comparison (Tag 08IB)
(blueprint: lem-pc-tor-independent-perfect-tensor-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe uPT wPT
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Convert the pullback comparison predicate into the identity stalk condition.
The coordinate equation makes t a quasi-isomorphism. Exact stalks preserve it;
the two tensor-to-stalk maps agree by uniqueness, so the localized comparisons
agree. Cancel the coordinate isomorphism and compose the remaining isomorphisms.
Source: Stacks, Tags 08IB, 01AG, and equation-bc before Tag 0DJ8. -/
private theorem stalkCondition_of_comparison
    [∀ Y : Scheme.{uPT},
      HasDerivedCategory.{wPT} (SheafOfModules.{uPT} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{uPT}} (f : X ⟶ S) (g : T ⟶ S)
    (P : schemeDerivedCategory X)
    (h : ∀ z, PullbackStalkTensor.IsComparisonIso f g P z) :
    SingleComplexBaseChange.StalkCondition f (pullback.snd f g) g (pullback.fst f g)
      (IsPullback.of_hasPullback f g) P ((derivedPullback (pullback.fst f g)).obj P)
      (𝟙 _) := by
  classical
  intro c z i
  let := c.counit_isIso
  have ht : IsIso ((DerivedCategory.Q (C := SheafOfModules.{uPT}
      (moduleRings (pullback f g).toRingedSpace))).map c.t) := by
    have hh := c.represents
    simp only [cast_eq, Category.comp_id] at hh
    have hiso : IsIso ((SingleComplexBaseChange.counit (pullback.fst f g)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P) ≫
      (DerivedCategory.Q (C := SheafOfModules.{uPT}
        (moduleRings (pullback f g).toRingedSpace))).map c.t ≫ c.e'.hom) := by
      rw [hh]
      infer_instance
    have hi := IsIso.of_isIso_comp_left
      ((SingleComplexBaseChange.counit (pullback.fst f g)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))
      ((DerivedCategory.Q (C := SheafOfModules.{uPT}
        (moduleRings (pullback f g).toRingedSpace))).map c.t ≫ c.e'.hom)
    exact IsIso.of_isIso_comp_right ((DerivedCategory.Q (C := SheafOfModules.{uPT}
      (moduleRings (pullback f g).toRingedSpace))).map c.t) c.e'.hom
  let := PullbackStalkTensor.leftAlgebra f g z
  let := PullbackStalkTensor.rightAlgebra f g z
  let := PullbackStalkTensor.tensorAlgebra f g z
  let := HasDerivedCategory.standard
    (ModuleCat.{uPT} (PullbackStalkTensor.R f g z))
  let := HasDerivedCategory.standard
    (ModuleCat.{uPT} (PullbackStalkTensor.B f g z))
  have hc := h z c.P c.isKFlat ⟨c.e⟩ i
  obtain ⟨e⟩ := hc.1
  have hi := hc.2 e
  have hloc := IsIso.of_isIso_comp_right
    ((PullbackStalkTensor.cohomologyModel f g z c.P).localizedComparison i) e.hom
  have : QuasiIso c.t :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (SheafOfModules.{uPT} (moduleRings (pullback f g).toRingedSpace)) c.t).mp ht
  have : (RingedSpace.moduleStalkFunctor (pullback f g).toRingedSpace z).PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro S hS
    exact ((RingedSpace.module_stalk_exact (pullback f g).toRingedSpace S.f).2.2.2.2
      S.X₃ S.f S.g S.zero).mp hS z
  have : QuasiIso
      (((RingedSpace.moduleStalkFunctor (pullback f g).toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) := inferInstance
  have hmap : SingleComplexBaseChange.tensorMap f (pullback.snd f g) g (pullback.fst f g)
      (IsPullback.of_hasPullback f g) z = PullbackStalkTensor.tensorToStalk f g z := by
    apply PullbackStalkTensor.tensorToStalk_unique
    · exact (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f
        (pullback.snd f g) g (pullback.fst f g) (IsPullback.of_hasPullback f g) z)).1
    · exact (Classical.choose_spec (SingleComplexBaseChange.exists_tensorMap f
        (pullback.snd f g) g (pullback.fst f g) (IsPullback.of_hasPullback f g) z)).2
  let := (SingleComplexBaseChange.tensorMap f (pullback.snd f g) g (pullback.fst f g)
    (IsPullback.of_hasPullback f g) z).toAlgebra
  have hl : IsIso ((SingleComplexBaseChange.cohomologyModel f (pullback.snd f g) g
      (pullback.fst f g) (IsPullback.of_hasPullback f g) z c.P).localizedComparison i) := by
    dsimp only [SingleComplexBaseChange.cohomologyModel]
    rw [hmap]
    exact hloc
  dsimp only [SingleComplexBaseChange.stalkComparison]
  infer_instance

/-- Naturality of the canonical mate in its derived input, from the naturality
of the pullback composition comparisons and the adjunction Hom equivalence.
Source: Stacks Project, Tag 08HY, the canonical derived base-change construction. -/
private theorem baseChange_naturality
    [∀ Z : Scheme.{uPT}, HasDerivedCategory.{wPT}
      (SheafOfModules.{uPT} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{uPT}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g)
    {E F : schemeDerivedCategory X} (s : E ⟶ F) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map s) ≫
        schemeDerivedBaseChangeMap f f' g g' h F =
      schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map s) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    set_option synthInstance.maxSize 2048 in
    open MonoidalCategory in by
  classical
  let ε : ∀ {A B : Scheme.{uPT}} (k : A ⟶ B),
      DerivedCategory.Qh (C := SheafOfModules.{uPT} (moduleRings B.toRingedSpace)) ⋙
        derivedPullback k ⟶
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{uPT} (moduleRings A.toRingedSpace)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k
  have hε : ∀ {A B : Scheme.{uPT}} (k : A ⟶ B),
      (derivedPullback k).IsLeftDerivedFunctor (ε k)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{uPT} (moduleRings B.toRingedSpace)) (.up ℤ)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k
  let c : ∀ {A B D : Scheme.{uPT}} (k : A ⟶ B) (l : B ⟶ D),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let adj := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f) (ε f) (hε f))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f') (ε f') (hε f'))
  let γ : (schemeDerivedDirectImage f ⋙ derivedPullback g) ⋙ derivedPullback f' ⟶
      derivedPullback g' :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (c f' g).hom ≫
      Functor.whiskerLeft _ (eqToHom (congrArg (fun k ↦ derivedPullback k) h.symm)) ≫
      Functor.whiskerLeft _ (c g' f).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight adj.counit (derivedPullback g') ≫
      (Functor.leftUnitor _).hom
  have hγ (K : schemeDerivedCategory X) :
      γ.app K = (c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
        (c g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback g').map (adj.counit.app K) := by
    simp only [γ, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_app, Category.id_comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have hbc (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h K = adj'.homEquiv _ _ (γ.app K) := by
    rw [hγ]
    rfl
  rw [hbc E, hbc F]
  exact adj'.homEquiv_naturality_left_square
    ((schemeDerivedDirectImage f ⋙ derivedPullback g).map s)
    (γ.app F) (γ.app E) ((derivedPullback g').map s) (γ.naturality s)

/-- Tor-independent qcqs base change over affine bases for a perfect tensor factor.
The target is written as Rf'_* Lg_X^*(P ⊗ K). Under the canonical tensor-pullback
isomorphism of lem-pc-derived-pullback-tensor-product (Stacks, 079U), this is exactly
Rf'_*(Lg_X^*P ⊗ Lg_X^*K). Postcomposing the fixed base-change map with that
isomorphism does not change IsIso.
Source: Stacks, perfect.tex, Tags 08IB, 0DJA and 0DJ9
(blueprint: lem-pc-tor-independent-perfect-tensor-base-change).
Proof (the node's four steps):
1. Apply lem-pc-tor-independent-perfect-pullback-comparison to P: Tor independence
   gives the stalkwise condition for the identity of Lg_X^*P.
2. Apply lem-pc-rf-single-complex-inherited-tensor-condition, with K=P,
   K'=Lg_X^*P, the identity comparison, and E=K, to inherit the condition for the
   tensor product. The two factors can be exchanged by tensor symmetry.
3. Perfect objects have quasi-coherent cohomology (08DB). By
   lem-pc-derived-pullback-tensor-qcoh all tensor products and pullbacks concerned
   have quasi-coherent cohomology. Apply lem-pc-rf-single-complex-qcqs-induction
   to this comparison; qcqs of f gives invertibility of the base-change composite.
4. Cancel the invertible tensor comparison in the direct image. Naturality of the
   canonical base-change map and the canonical derived braiding transport
   invertibility from K tensor P to P tensor K, giving the displayed map. -/
theorem torIndependent_perfect_tensor_baseChange
    [∀ Y : Scheme.{uPT},
      HasDerivedCategory.{wPT} (SheafOfModules.{uPT} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{uPT}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [∀ U : X.Opens,
      HasDerivedCategory.{wPT} (SheafOfModules.{uPT} ((moduleRings X.toRingedSpace).over U))]
    (hTor : PullbackStalkTensor.IsTorIndependent f g)
    (P K : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P)
    (hK : schemeDerivedQCohProperty X K) :
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition (P ⊗ K)) := by
  classical
  let g' := pullback.fst f g
  let f' := pullback.snd f g
  let sq := IsPullback.of_hasPullback f g
  have hPq := schemeDerivedQCohProperty_of_isPerfect X P hP
  have hP'q := (derivedPullback_tensor_preserve_QCoh g').1 P hPq
  have hK'q := (derivedPullback_tensor_preserve_QCoh g').1 K hK
  have hstalk := stalkCondition_of_comparison f g P
    (torIndependent_perfect_pullback_comparison f g hTor P hP)
  obtain ⟨m, _, hinherit⟩ := singleComplexInheritedTensorCondition f f' g g' sq
    ⟨P, hPq⟩ ⟨(derivedPullback g').obj P, hP'q⟩ (𝟙 _) hstalk
  let : (derivedPullback g').Monoidal := m.toMonoidal
  let φ := (Functor.Monoidal.μIso (derivedPullback g') K P).inv ≫
    ((derivedPullback g').obj K ◁ 𝟙 ((derivedPullback g').obj P))
  have hφ : IsIso φ := by
    dsimp [φ]
    infer_instance
  have hKPq := canonical_derivedTensor_preserve_QCoh X K P hK hPq
  have htarget := canonical_derivedTensor_preserve_QCoh (pullback f g)
    ((derivedPullback g').obj K) ((derivedPullback g').obj P) hK'q hP'q
  have hcomp := singleComplexBaseChangeQcqsInduction f f' g g' sq
    (K ⊗ P) hKPq _ htarget φ (hinherit ⟨K, hK⟩)
  have hbase : IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w (K ⊗ P)) := by
    let := hφ
    let := hcomp
    exact IsIso.of_isIso_comp_right _ ((schemeDerivedDirectImage f').map φ)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{uPT} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{uPT} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{uPT}
      (SheafOfModules.{uPT} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have := schemeModule_hasFunctorialFlatResolution X
  have : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{uPT} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, uPT, uPT} _
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{uPT} (moduleRings X.toRingedSpace))
  let e : P ⊗ K ≅ K ⊗ P :=
    DerivedMonoidal.braiding'
      (DerivedCategory.Qh (C := SheafOfModules.{uPT} (moduleRings X.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uPT} (moduleRings X.toRingedSpace)) (.up ℤ)) P K
  have : IsIso e.hom := e.isIso_hom
  have hn := baseChange_naturality f f' g g' sq.w e.hom
  have hiso : IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map e.hom) ≫
      schemeDerivedBaseChangeMap f f' g g' sq.w (K ⊗ P)) := by
    let := hbase
    infer_instance
  have hiso' : IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w (P ⊗ K) ≫
      (schemeDerivedDirectImage f').map ((derivedPullback g').map e.hom)) := by
    rw [← hn]
    exact hiso
  let := hiso'
  exact IsIso.of_isIso_comp_right _
    ((schemeDerivedDirectImage f').map ((derivedPullback g').map e.hom))

end AlgebraicGeometry
