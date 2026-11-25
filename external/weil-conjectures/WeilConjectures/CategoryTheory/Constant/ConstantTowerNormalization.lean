/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.ProperBaseChange.DiagramKFlatReplacements
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Category.ULift

/-!
# The representative normalization of the derived constant-tower comparison

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`
(dual), and the completed-pullback constant-tower subargument, Step 4
(blueprint: lem-cbc-derived-constant-tower-normalization).

The auxiliary maps below merely spell out the canonical localization identifications.
Strict towers are indexed by `ℕᵒᵖ`, with level `n` representing the paper's level `n + 1`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB u

open CategoryTheory CategoryTheory.Limits

-- Avoid expanding covering multicospans when forgetting commutative ring structures.
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]

-- Computation on a resolving class is invariant under the chosen universal pair.
private theorem comparison_from_resolutions
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uB} [Category.{vB} D]
    (p : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (s : P ⟶ K), p P ∧ QuasiIso s)
    (U V : DerivedCategory A ⥤ D) (H : CochainComplex A ℤ ⥤ D)
    (η : DerivedCategory.Q ⋙ U ⟶ H) (θ : DerivedCategory.Q ⋙ V ⟶ H)
    (hη : ∀ P, p P → IsIso (η.app P)) (hθ : ∀ P, p P → IsIso (θ.app P)) :
    ∃! b : U ≅ V, ∀ P, p P → b.hom.app (DerivedCategory.Q.obj P) ≫ θ.app P =
      η.app P := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let i := DerivedCategory.quotientCompQhIso A
  let η' : q ⋙ (Q ⋙ U) ⟶ H := Functor.whiskerRight i.hom U ≫ η
  let θ' : q ⋙ (Q ⋙ V) ⟶ H := Functor.whiskerRight i.hom V ≫ θ
  have hη' (K : CochainComplex A ℤ) (hK : p K) : IsIso (η'.app K) := by
    have := hη K hK
    dsimp [η']
    infer_instance
  have hθ' (K : CochainComplex A ℤ) (hK : p K) : IsIso (θ'.app K) := by
    have := hθ K hK
    dsimp [θ']
    infer_instance
  let P : HomotopyCategory A (.up ℤ) → Prop := fun X ↦ p X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X), P Y ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨N, s, hN, hs⟩ := res K
    exact ⟨q.obj N, q.map s, hN,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let α (X : HomotopyCategory A (.up ℤ)) (hX : P X) :
      (Q ⋙ U).obj X ⟶ (Q ⋙ V).obj X :=
    letI := hθ' X.as hX
    η'.app X.as ≫ inv (θ'.app X.as)
  have hα : ∀ (X Y : HomotopyCategory A (.up ℤ)) (hX : P X) (hY : P Y) (s : X ⟶ Y),
      (Q ⋙ U).map s ≫ α Y hY = α X hX ≫ (Q ⋙ V).map s := by
    intro X Y hX hY s
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have := hθ' K hX
    have := hθ' N hY
    change (q ⋙ Q ⋙ U).map f ≫ (η'.app N ≫ inv (θ'.app N)) =
      (η'.app K ≫ inv (θ'.app K)) ≫ (q ⋙ Q ⋙ V).map f
    apply (cancel_mono (θ'.app N)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [θ'.naturality f]
    simp only [IsIso.inv_hom_id_assoc]
    exact η'.naturality f
  have hU : W.IsInvertedBy (Q ⋙ U) := by
    intro X Y s hs
    have := Localization.inverts Q W s hs
    exact U.map_isIso (Q.map s)
  obtain ⟨γ, hγ⟩ := exists_natTrans_from_resolvingClass W P hres (Q ⋙ U) (Q ⋙ V) hU α hα
  have hγiso (X : HomotopyCategory A (.up ℤ)) : IsIso (γ.app X) := by
    obtain ⟨Y, s, hY, hs⟩ := hres X
    have := Localization.inverts Q W s hs
    have : IsIso ((Q ⋙ U).map s) := hU s hs
    have : IsIso ((Q ⋙ V).map s) := V.map_isIso (Q.map s)
    have := hη' Y.as hY
    have := hθ' Y.as hY
    have : IsIso (γ.app Y) := by rw [hγ Y hY]; dsimp [α]; infer_instance
    have he : γ.app X = inv ((Q ⋙ U).map s) ≫ γ.app Y ≫ (Q ⋙ V).map s := by
      rw [← γ.naturality s]
      simp
    rw [he]
    infer_instance
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  let b : U ≅ V := Localization.liftNatIso Q W (Q ⋙ U) (Q ⋙ V) U V (asIso γ)
  have hb (X : HomotopyCategory A (.up ℤ)) : b.hom.app (Q.obj X) = γ.app X := by
    simp [b]
  have hnorm (K : CochainComplex A ℤ) (hK : p K) :
      b.hom.app (DerivedCategory.Q.obj K) ≫ θ.app K = η.app K := by
    have := hθ' K hK
    apply (cancel_epi (U.map (i.hom.app K))).1
    rw [← Category.assoc, b.hom.naturality (i.hom.app K), Category.assoc]
    change b.hom.app (Q.obj (q.obj K)) ≫ θ'.app K = η'.app K
    rw [hb, hγ (q.obj K) hK]
    change (η'.app K ≫ inv (θ'.app K)) ≫ θ'.app K = η'.app K
    simp
  refine ⟨b, hnorm, ?_⟩
  intro c hc
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  obtain ⟨N, s, hN, hs⟩ := res K
  have : QuasiIso s := hs
  have : IsIso (DerivedCategory.Q.map s) := inferInstance
  have he : c.hom.app (DerivedCategory.Q.obj N) = b.hom.app (DerivedCategory.Q.obj N) := by
    have := hθ N hN
    apply (cancel_mono (θ.app N)).1
    rw [hc N hN, hnorm N hN]
  apply (cancel_epi (U.map (DerivedCategory.Q.map s))).1
  rw [c.hom.naturality, b.hom.naturality, he]

-- The inverse of Mathlib's transpose on complexes of functors.
private def diagramComplex
    {A I : Type*} [Category A] [HasZeroMorphisms A] [Category I]
    (M : I ⥤ CochainComplex A ℤ) : CochainComplex (I ⥤ A) ℤ where
  X n := M ⋙ HomologicalComplex.eval A (.up ℤ) n
  d n m :=
    { app := fun j ↦ (M.obj j).d n m
      naturality := fun j k a ↦ (M.map a).comm n m }
  shape n m h := by ext j; exact (M.obj j).shape n m h
  d_comp_d' n m k _ _ := by ext j; exact (M.obj j).d_comp_d n m k

private def ringedResolvingClass
    {C : Type u} [SmallCategory C] {T : GrothendieckTopology C}
    (R : Sheaf T CommRingCat.{u})
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) : Prop :=
  CochainComplex.IsAcyclicTensorKFlat (R := R) P ∧
    ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)

private theorem ringed_resolution
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    (R : Sheaf T CommRingCat.{u})
    (K : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ P, ∃ s : P ⟶ K, ringedResolvingClass R P ∧ QuasiIso s := by
  obtain ⟨P, s, hk, hf, hs, _⟩ := CochainComplex.exists_diagram_isKFlatResolution T R
    ((Functor.const (Discrete PUnit.{u + 1})).obj K)
  exact ⟨P.obj ⟨PUnit.unit⟩, s.app ⟨PUnit.unit⟩,
    ⟨hk ⟨PUnit.unit⟩, hf ⟨PUnit.unit⟩⟩, hs ⟨PUnit.unit⟩⟩

namespace CategoryTheory.Functor

section Identifications

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (E : A ⥤ B) [E.Additive]

end Identifications

end CategoryTheory.Functor

namespace CategoryTheory.RingedToposMorphism

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {T : GrothendieckTopology C} {T' : GrothendieckTopology D}
  (R : Sheaf T CommRingCat.{u}) (S : Sheaf T' CommRingCat.{u})
  [HasDerivedCategory.{wA}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wB}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]

end CategoryTheory.RingedToposMorphism
